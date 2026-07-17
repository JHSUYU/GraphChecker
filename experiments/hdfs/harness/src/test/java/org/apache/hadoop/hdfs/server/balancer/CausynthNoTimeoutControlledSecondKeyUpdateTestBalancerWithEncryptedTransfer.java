package org.apache.hadoop.hdfs.server.balancer;

import org.junit.Test;

/**
 * No-timeout Surefire entry point for the controlled second-key-update
 * concolic workload.
 *
 * <p>The delegate method is called directly, so its {@code @Test} timeout is
 * not installed by JUnit.  The workload itself remains defined solely by the
 * delegate class.</p>
 */
public final class
    CausynthNoTimeoutControlledSecondKeyUpdateTestBalancerWithEncryptedTransfer {

  @Test
  public void testEncryptedBalancer1() throws Exception {
    new CausynthControlledSecondKeyUpdateTestBalancerWithEncryptedTransfer()
        .testEncryptedBalancer1();
  }
}
