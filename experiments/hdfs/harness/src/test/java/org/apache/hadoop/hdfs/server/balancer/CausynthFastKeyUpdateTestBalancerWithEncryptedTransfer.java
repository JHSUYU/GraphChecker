package org.apache.hadoop.hdfs.server.balancer;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.hdfs.DFSConfigKeys;
import org.apache.hadoop.hdfs.HdfsConfiguration;
import org.junit.Test;

/**
 * Bounded workload variant for capturing a second NN-to-DN block-key update.
 *
 * <p>The original test uses the production default 600-minute block-key
 * update interval and normally ends before a second update reaches either
 * DataNode.  This harness invokes the same {@code testBalancer1Internal}
 * workload with only that interval set to zero minutes.  The NameNode monitor
 * still runs on its normal five-second cycle.  Token lifetime and every other
 * encrypted-transfer setting retain the original test values.</p>
 *
 * <p>This class is diagnostic workload evidence and must not be reported as
 * an unmodified execution of {@code TestBalancerWithEncryptedTransfer}.</p>
 */
public final class CausynthFastKeyUpdateTestBalancerWithEncryptedTransfer {

  @Test
  public void testEncryptedBalancer1() throws Exception {
    Configuration conf = new HdfsConfiguration();
    conf.setBoolean(DFSConfigKeys.DFS_ENCRYPT_DATA_TRANSFER_KEY, true);
    conf.setBoolean(DFSConfigKeys.DFS_BLOCK_ACCESS_TOKEN_ENABLE_KEY, true);
    conf.setLong(DFSConfigKeys.DFS_BLOCK_ACCESS_KEY_UPDATE_INTERVAL_KEY, 0L);
    new TestBalancer().testBalancer1Internal(conf);
  }
}
