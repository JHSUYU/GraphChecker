package org.apache.hadoop.hdfs.server.balancer;

import static org.junit.Assert.assertTrue;

import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.hdfs.DFSConfigKeys;
import org.apache.hadoop.hdfs.HdfsConfiguration;
import org.apache.hadoop.hdfs.MiniDFSCluster;
import org.apache.hadoop.hdfs.NameNodeProxies;
import org.apache.hadoop.hdfs.protocol.Block;
import org.apache.hadoop.hdfs.protocol.ClientProtocol;
import org.apache.hadoop.hdfs.protocol.ExtendedBlock;
import org.apache.hadoop.hdfs.security.token.block.BlockTokenSecretManager;
import org.apache.hadoop.hdfs.server.blockmanagement.BlockManager;
import org.apache.hadoop.hdfs.server.blockmanagement.DatanodeDescriptor;
import org.apache.hadoop.hdfs.server.datanode.DataNode;
import org.apache.hadoop.hdfs.server.datanode.DataNodeTestUtils;
import org.junit.Test;

/**
 * Bounded variant of encrypted {@link TestBalancer#testBalancer1Internal}.
 *
 * <p>The original workload normally gives each DataNode only its registration
 * {@code addKeys()} call.  This diagnostic variant preserves the same uneven
 * two-DataNode cluster and Balancer phase, but inserts one deterministic key
 * delivery after the final cluster is active.  It marks the already
 * registered DataNodes for an update and triggers their heartbeats before
 * starting Balancer.  Consequently the second {@code addKeys()} for each
 * manager observes a non-empty {@code allKeys} prestate and executes the real
 * {@code removeExpiredKeys()} guards.</p>
 *
 * <p>This is bounded capture evidence, not an unmodified execution of
 * {@code TestBalancerWithEncryptedTransfer}.</p>
 */
public final class
    CausynthControlledSecondKeyUpdateTestBalancerWithEncryptedTransfer {

  @Test(timeout = 120_000)
  public void testEncryptedBalancer1() throws Exception {
    Configuration conf = new HdfsConfiguration();
    conf.setBoolean(DFSConfigKeys.DFS_ENCRYPT_DATA_TRANSFER_KEY, true);
    conf.setBoolean(DFSConfigKeys.DFS_BLOCK_ACCESS_TOKEN_ENABLE_KEY, true);
    TestBalancer.initConf(conf);

    TestBalancer delegate = new TestBalancer();
    long[] distribution = new long[] {
        50 * TestBalancer.CAPACITY / 100,
        10 * TestBalancer.CAPACITY / 100
    };
    long[] capacities = new long[] {
        TestBalancer.CAPACITY,
        TestBalancer.CAPACITY
    };
    String[] racks = new String[] {
        TestBalancer.RACK0,
        TestBalancer.RACK1
    };
    long totalUsedSpace = TestBalancer.sum(distribution);

    ExtendedBlock[] blocks = invokeGenerateBlocks(
        delegate, conf, totalUsedSpace, (short) distribution.length);
    Block[][] blocksByDn = TestBalancer.distributeBlocks(
        blocks, (short) (distribution.length - 1), distribution);

    conf.set(DFSConfigKeys.DFS_NAMENODE_SAFEMODE_THRESHOLD_PCT_KEY, "0.0f");
    MiniDFSCluster cluster = new MiniDFSCluster.Builder(conf)
        .numDataNodes(distribution.length)
        .format(false)
        .racks(racks)
        .simulatedCapacities(capacities)
        .build();
    try {
      cluster.waitActive();
      ClientProtocol client = NameNodeProxies.createProxy(
          conf, cluster.getFileSystem(0).getUri(), ClientProtocol.class)
          .getProxy();
      setDelegateCluster(delegate, cluster);
      delegate.client = client;

      for (int i = 0; i < blocksByDn.length; i++) {
        cluster.injectBlocks(i, Arrays.asList(blocksByDn[i]), null);
      }

      deliverControlledSecondAddKeys(cluster);
      invokeRunBalancer(delegate, conf, totalUsedSpace,
          TestBalancer.sum(capacities));
    } finally {
      cluster.shutdown();
      setDelegateCluster(delegate, null);
    }
  }

  private static void deliverControlledSecondAddKeys(MiniDFSCluster cluster)
      throws Exception {
    BlockManager blockManager = cluster.getNamesystem().getBlockManager();
    BlockTokenSecretManager master =
        blockManager.getBlockTokenSecretManager();
    int currentKeyId = master.exportKeys().getCurrentKey().getKeyId();

    for (DataNode dataNode : cluster.getDataNodes()) {
      DatanodeDescriptor descriptor = blockManager.getDatanodeManager()
          .getDatanode(dataNode.getDatanodeId());
      descriptor.setNeedKeyUpdate(true);
    }

    String blockPoolId = cluster.getNamesystem().getBlockPoolId();
    for (DataNode dataNode : cluster.getDataNodes()) {
      // The first call delivers DNA_ACCESSKEYUPDATE.  The second call is an
      // actor-thread fence proving that the first command was processed.
      DataNodeTestUtils.triggerHeartbeat(dataNode);
      DataNodeTestUtils.triggerHeartbeat(dataNode);
      DatanodeDescriptor descriptor = blockManager.getDatanodeManager()
          .getDatanode(dataNode.getDatanodeId());
      assertTrue("NameNode did not consume the forced key-update flag",
          !descriptor.needKeyUpdate());
      assertTrue("DataNode current key differs after controlled addKeys()",
          dataNode.getBlockPoolTokenSecretManager().get(blockPoolId)
              .generateDataEncryptionKey().keyId == currentKeyId);
    }
  }

  private static ExtendedBlock[] invokeGenerateBlocks(TestBalancer delegate,
      Configuration conf, long size, short nodes) throws Exception {
    Method method = TestBalancer.class.getDeclaredMethod("generateBlocks",
        Configuration.class, long.class, short.class);
    method.setAccessible(true);
    return (ExtendedBlock[]) invoke(method, delegate, conf, size, nodes);
  }

  private static void invokeRunBalancer(TestBalancer delegate,
      Configuration conf, long used, long capacity) throws Exception {
    Method method = TestBalancer.class.getDeclaredMethod("runBalancer",
        Configuration.class, long.class, long.class);
    method.setAccessible(true);
    invoke(method, delegate, conf, used, capacity);
  }

  private static Object invoke(Method method, Object receiver,
      Object... arguments) throws Exception {
    try {
      return method.invoke(receiver, arguments);
    } catch (InvocationTargetException e) {
      Throwable cause = e.getCause();
      if (cause instanceof Exception) {
        throw (Exception) cause;
      }
      if (cause instanceof Error) {
        throw (Error) cause;
      }
      throw e;
    }
  }

  private static void setDelegateCluster(TestBalancer delegate,
      MiniDFSCluster cluster) throws Exception {
    Field field = TestBalancer.class.getDeclaredField("cluster");
    field.setAccessible(true);
    field.set(delegate, cluster);
  }
}
