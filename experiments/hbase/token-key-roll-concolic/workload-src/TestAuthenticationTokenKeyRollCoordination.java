/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.hadoop.hbase.security.token;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.hbase.Abortable;
import org.apache.hadoop.hbase.HBaseTestingUtil;
import org.apache.hadoop.hbase.Waiter;
import org.apache.hadoop.hbase.testclassification.SecurityTests;
import org.apache.hadoop.hbase.testclassification.SmallTests;
import org.apache.hadoop.hbase.util.EnvironmentEdgeManager;
import org.apache.hadoop.hbase.util.ManualEnvironmentEdge;
import org.apache.hadoop.hbase.util.Writables;
import org.apache.hadoop.hbase.zookeeper.ZKWatcher;
import org.apache.hadoop.security.token.SecretManager.InvalidToken;
import org.apache.hadoop.security.token.Token;
import edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder;
import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

/** Exercises a delayed token-key notification across two secret managers. */
@Tag(SecurityTests.TAG)
@Tag(SmallTests.TAG)
public class TestAuthenticationTokenKeyRollCoordination {

  private static final long TOKEN_LIFETIME = 1000;

  private static final class RecordingAbortable implements Abortable {
    private volatile boolean aborted;

    @Override
    public void abort(String why, Throwable error) {
      aborted = true;
    }

    @Override
    public boolean isAborted() {
      return aborted;
    }
  }

  @Test
  public void testDelayedRollNotificationMakesUnexpiredTokenUnverifiable() throws Exception {
    HBaseTestingUtil testUtil = new HBaseTestingUtil();
    testUtil.startMiniZKCluster();
    CausynthTraceRecorder.startRecording();
    AuthenticationTokenSecretManager master = null;
    ZKWatcher masterZk = null;
    ZKWatcher issuerZk = null;
    try {
      Configuration conf = testUtil.getConfiguration();
      masterZk = new ZKWatcher(conf, "key-master", new RecordingAbortable());
      master = new AuthenticationTokenSecretManager(conf, masterZk, "key-master", 3600000,
        TOKEN_LIFETIME);
      master.start();
      AuthenticationTokenSecretManager leader = master;
      Waiter.waitFor(conf, 30000,
        () -> leader.isMaster() && leader.getCurrentKey() != null);

      ManualEnvironmentEdge clock = new ManualEnvironmentEdge();
      clock.setValue(EnvironmentEdgeManager.currentTime());
      EnvironmentEdgeManager.injectEdge(clock);

      // First make a key that both servers know.  The issuer's watcher event for the
      // next roll is delayed; addKey models the old cached key at that instant.
      master.rollCurrentKey();
      AuthenticationKey oldKey = master.getCurrentKey();
      assertNotNull(oldKey);
      issuerZk = new ZKWatcher(conf, "token-issuer", new RecordingAbortable());
      AuthenticationTokenSecretManager issuer = new AuthenticationTokenSecretManager(conf,
        issuerZk, "token-issuer", 3600000, TOKEN_LIFETIME);
      issuer.addKey(oldKey);

      clock.incValue(100);
      long rollTime = clock.currentTime();
      master.rollCurrentKey();
      AuthenticationKey newKey = master.getCurrentKey();
      assertEquals(rollTime + TOKEN_LIFETIME, oldKey.getExpiration());

      // A finite 100 ms notification delay is enough.  The issuer does catch up
      // immediately after issuing the token; no persistent partition is needed.
      clock.incValue(100);
      Token<AuthenticationTokenIdentifier> token = issuer.generateToken("user");
      AuthenticationTokenIdentifier identifier = new AuthenticationTokenIdentifier();
      Writables.getWritable(token.getIdentifier(), identifier);
      assertEquals(oldKey.getKeyId(), identifier.getKeyId());
      assertArrayEquals(token.getPassword(), master.retrievePassword(identifier));
      issuer.addKey(newKey);

      // The leader expires the old key based on the roll, not on the last
      // token issued with it.  The token still has 99 ms left at this point.
      clock.setValue(rollTime + TOKEN_LIFETIME + 1);
      assertTrue(identifier.getExpirationDate() > clock.currentTime());
      master.removeExpiredKeys();
      assertNull(master.getKey(oldKey.getKeyId()));
      InvalidToken error = assertThrows(InvalidToken.class,
        () -> leader.retrievePassword(identifier));
      assertTrue(error.getMessage().contains("Unknown master key"), error.getMessage());
    } finally {
      EnvironmentEdgeManager.reset();
      if (master != null) {
        master.stop();
      }
      if (issuerZk != null) {
        issuerZk.close();
      }
      if (masterZk != null) {
        masterZk.close();
      }
      testUtil.shutdownMiniZKCluster();
    }
  }
}
