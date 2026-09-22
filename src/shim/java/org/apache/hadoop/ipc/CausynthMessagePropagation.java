/**
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
package org.apache.hadoop.ipc;

import java.util.UUID;

import edu.uva.liftlab.graphchecker.runtime.CausynthTraceRecorder;
import edu.uva.liftlab.graphchecker.runtime.SymbolicMessageEnvelope;

/**
 * THE Hadoop shim: message-carried GraphChecker context for Hadoop IPC and
 * SASL, and the workload's registration and recording boundary.
 *
 * <p>Published by GraphChecker (the {@code hadoop-shim} classifier jar, and
 * inside the main jar every Hadoop tree already compiles against), so every
 * tree calls ONE version.  It used to be a file in each tree: six versions in
 * three lineages over nine trees, and a tree cut from another carried a
 * different subset.  What a tree keeps is the calls -- the IPC and SASL wire
 * propagation the design's transport mapping needs, its fault markers and
 * symbolize hooks, its daemon ticks -- and nothing that compensates for
 * attribution: {@code runtime.Attribution} names the node of every thread,
 * and a start carries its scope to its claim, in both passes.</p>
 */
public final class CausynthMessagePropagation {
  public static final String IPC = "HADOOP_IPC";
  public static final String SASL = "HDFS_SASL";

  private static final ThreadLocal<Inbound> CURRENT = new ThreadLocal<>();
  private static final ThreadLocal<String> PENDING_SASL = new ThreadLocal<>();

  private CausynthMessagePropagation() {
  }

  /**
   * The request scope of the calling thread, as a value the work it is
   * creating can carry to whatever thread later sends it.
   */
  public static Object captureScope() {
    return CausynthTraceRecorder.captureScope();
  }

  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner) {
    return outbound(transport, correlationId, attemptId, half, localOwner,
        null);
  }

  /** The same leg, for work carrying the scope it was created in. */
  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner, Object scope) {
    String trace = CausynthTraceRecorder.outboundExchange(transport,
        correlationId, attemptId, half, localOwner, scope);
    String symbolic = SymbolicMessageEnvelope.takeOutbound();
    return trace.isEmpty() && symbolic.isEmpty() ? Outbound.EMPTY
        : new Outbound(correlationId, attemptId, trace, symbolic);
  }

  public static String rpcCorrelation(byte[] clientId, int callId) {
    return "hadoop-ipc-" + hex(clientId) + "-" + callId;
  }

  private static String hex(byte[] bytes) {
    if (bytes == null) {
      return "";
    }
    StringBuilder text = new StringBuilder(bytes.length * 2);
    for (byte value : bytes) {
      text.append(String.format("%02x", value));
    }
    return text.toString();
  }

  public static Inbound inbound(String trace, String symbolic,
      String transport, String correlationId, String attemptId, String half,
      Object localOwner) {
    return inbound(trace, symbolic, transport, correlationId, attemptId,
        half, localOwner, false);
  }

  private static Inbound inbound(String trace, String symbolic,
      String transport, String correlationId, String attemptId, String half,
      Object localOwner, boolean preserveSymbolic) {
    endInbound(!preserveSymbolic);
    if (!preserveSymbolic) {
      SymbolicMessageEnvelope.clearInbound();
    }
    boolean hasTrace = trace != null && !trace.isEmpty();
    boolean hasSymbolic = symbolic != null && !symbolic.isEmpty();
    if (!hasTrace && !hasSymbolic) {
      return Inbound.EMPTY;
    }
    long token = hasTrace
        ? CausynthTraceRecorder.inboundExchange(trace, transport,
            correlationId, attemptId, half, localOwner)
        : 0L;
    if (hasSymbolic) {
      SymbolicMessageEnvelope.installInbound(symbolic);
    }
    Inbound scope = new Inbound(token, correlationId, attemptId, half);
    CURRENT.set(scope);
    return scope;
  }

  public static void endInbound(Inbound scope) {
    if (scope == null || scope == Inbound.EMPTY) {
      return;
    }
    if (CURRENT.get() != scope) {
      // Already ended by the next message's install, which is not a
      // workload error.
      return;
    }
    endInbound();
  }

  public static void endInbound() {
    endInbound(true);
  }

  private static void endInbound(boolean clearSymbolic) {
    Inbound scope = CURRENT.get();
    if (scope == null) {
      return;
    }
    CURRENT.remove();
    if (clearSymbolic) {
      SymbolicMessageEnvelope.clearInbound();
    }
    if (scope.token > 0L) {
      CausynthTraceRecorder.endInboundExchange(scope.token);
    }
  }

  /**
   * Starts one multi-message SASL exchange on the client thread.
   *
   * <p>One exchange at a time on a thread: a begin nested inside another --
   * the same handshake reached through a second entry point, {@code
   * newSocketSend} into {@code send} -- is that same exchange, and only the
   * outermost end closes it.</p>
   */
  public static void beginSasl() {
    int depth = SASL_DEPTH.get();
    SASL_DEPTH.set(depth + 1);
    if (depth == 0) {
      PENDING_SASL.set("hdfs-sasl-" + UUID.randomUUID());
    }
  }

  public static void endSasl() {
    int depth = SASL_DEPTH.get();
    if (depth > 1) {
      SASL_DEPTH.set(depth - 1);
      return;
    }
    SASL_DEPTH.remove();
    PENDING_SASL.remove();
    endInbound();
  }

  private static final ThreadLocal<Integer> SASL_DEPTH =
      ThreadLocal.withInitial(() -> 0);

  /** Emits the next message of the current SASL exchange. */
  public static Outbound outboundSasl() {
    Inbound current = CURRENT.get();
    if (current != null && "REQUEST".equals(current.half)) {
      return outbound(SASL, current.correlationId, current.attemptId,
          "RESPONSE", null);
    }
    endInbound();
    String correlationId = PENDING_SASL.get();
    if (correlationId == null) {
      return Outbound.EMPTY;
    }
    return outbound(SASL, correlationId, "1", "REQUEST", null);
  }

  /** Installs one message without discarding values carried earlier in the
   * same multi-message SASL exchange. */
  public static Inbound inboundSasl(String trace, String symbolic,
      String correlationId, String attemptId) {
    boolean response = correlationId != null
        && correlationId.equals(PENDING_SASL.get());
    return inbound(trace, symbolic, SASL, correlationId, attemptId,
        response ? "RESPONSE" : "REQUEST", null, true);
  }

  /**
   * Enters the scope a queued unit of work carried from where it was made:
   * the dequeue half of the IPC {@code Server.Call} transport mapping.
   */
  public static long enterCarriedScope(Object scope, String role,
      String api) {
    return CausynthTraceRecorder.enterCarriedScope(scope, role, api);
  }

  /** Leaves the scope {@link #enterCarriedScope} entered. */
  public static void exitCarriedScope(long token) {
    CausynthTraceRecorder.exitCarriedScope(token);
  }

  /** Opens one daemon tick as a root of its own: a service-loop turn. */
  public static long beginTick(Object owner, String role) {
    return CausynthTraceRecorder.beginDaemonTick(owner, role);
  }

  /** Closes the tick {@link #beginTick} opened. */
  public static void endTick(long token) {
    CausynthTraceRecorder.endDaemonTick(token);
  }

  /** Opens the recorded window: the workload's recording boundary. */
  public static void startRecording() {
    CausynthTraceRecorder.startRecording();
  }

  public static void registerSource(Object anchor, String kind, String role,
      String sourceId, long epoch) {
    CausynthTraceRecorder.registerSource(anchor, kind, role, sourceId, epoch);
  }

  public static void registerSourceAlias(Object alias, Object anchor) {
    CausynthTraceRecorder.registerSourceAlias(alias, anchor);
  }

  /**
   * Registers one node: its anchor as the source, and every object the node
   * runs its work through as the same node.
   *
   * <p>The objects are what the attribution rule finds on a thread's frames
   * -- the RPC server a handler serves, the SASL server a connection
   * handshakes with, the DataNode a daemon was started from -- so naming
   * them here is what attributes work nothing else scopes.  A null or
   * repeated alias is skipped.</p>
   */
  public static void registerNode(Object anchor, String kind, String role,
      String sourceId, Object... aliases) {
    registerSource(anchor, kind, role, sourceId, 0L);
    if (aliases == null) {
      return;
    }
    for (Object alias : aliases) {
      if (alias == null || alias == anchor) {
        continue;
      }
      registerSourceAlias(alias, anchor);
    }
  }

  public static void restartSource(Object anchor, String kind, String role,
      String sourceId, long epoch) {
    CausynthTraceRecorder.restartSource(anchor, kind, role, sourceId, epoch);
  }

  public static long beginRequest(Object source, String api) {
    endInbound();
    return CausynthTraceRecorder.beginSourceRequest(source, api);
  }

  public static void endRequest(long request, String api) {
    endInbound();
    CausynthTraceRecorder.endSourceRequest(request, api);
  }

  public static final class Outbound {
    private static final Outbound EMPTY = new Outbound("", "", "", "");
    public final String correlationId;
    public final String attemptId;
    public final String trace;
    public final String symbolic;

    private Outbound(String correlationId, String attemptId, String trace,
        String symbolic) {
      this.correlationId = correlationId;
      this.attemptId = attemptId;
      this.trace = trace;
      this.symbolic = symbolic == null ? "" : symbolic;
    }

    public boolean active() {
      return !trace.isEmpty() || !symbolic.isEmpty();
    }
  }

  public static final class Inbound {
    private static final Inbound EMPTY = new Inbound(0L, "", "", "");
    private final long token;
    private final String correlationId;
    private final String attemptId;
    private final String half;

    private Inbound(long token, String correlationId, String attemptId,
        String half) {
      this.token = token;
      this.correlationId = correlationId;
      this.attemptId = attemptId;
      this.half = half;
    }
  }
}
