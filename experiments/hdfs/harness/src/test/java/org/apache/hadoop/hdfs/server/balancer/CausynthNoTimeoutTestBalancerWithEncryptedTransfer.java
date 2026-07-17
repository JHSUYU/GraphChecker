package org.apache.hadoop.hdfs.server.balancer;

import org.junit.Test;
import org.junit.internal.runners.statements.FailOnTimeout;
import org.junit.runners.model.Statement;

/**
 * Harness-only entry point for the interpreted concolic JVM.
 *
 * <p>The original test carries {@code @Test(timeout = 60000)}.  Running the
 * instrumented Hadoop classes in the Zero interpreter can consume nearly all
 * of that allowance.  A zero-valued JUnit 4.11 {@link FailOnTimeout} retains
 * the original timeout worker-thread execution model while waiting without a
 * second, outer 60-second deadline.  Hadoop's own semantic timeouts and the
 * Surefire fork timeout remain active.</p>
 */
public final class CausynthNoTimeoutTestBalancerWithEncryptedTransfer {

  @Test
  public void testEncryptedBalancer1() throws Throwable {
    final TestBalancerWithEncryptedTransfer delegate =
        new TestBalancerWithEncryptedTransfer();

    // Match JUnit's original ordering: @Before executes outside the timeout
    // worker, and the test body executes on the StatementThread.
    delegate.setUpConf();
    new FailOnTimeout(new Statement() {
      @Override
      public void evaluate() throws Throwable {
        delegate.testEncryptedBalancer1();
      }
    }, 0L).evaluate();
  }
}
