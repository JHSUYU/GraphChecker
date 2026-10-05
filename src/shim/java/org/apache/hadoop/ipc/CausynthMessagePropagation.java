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

import edu.uva.liftlab.graphchecker.runtime.MessageDoors;

/**
 * THE Hadoop shim: Hadoop IPC, the SASL data-transfer exchange and the
 * DataTransfer ops on {@link MessageDoors}, the transport-neutral doors every
 * system calls.
 *
 * <p>Published by GraphChecker (the {@code hadoop-shim} classifier jar, and
 * inside the main jar every Hadoop tree already compiles against), so every
 * tree calls ONE version.  What is Hadoop's own here: the transport names,
 * the IPC correlation id, the SASL exchange -- one handshake of several
 * messages on one thread, opened by a thread that may itself be serving a
 * request -- and the DataTransfer op, a request on a correlation of its own
 * that no response answers through a door.  Everything else delegates.</p>
 */
public final class CausynthMessagePropagation {
  public static final String IPC = "HADOOP_IPC";
  public static final String SASL = "HDFS_SASL";
  /** The transport of the library catalog's DataTransfer doors. */
  public static final String DATA_TRANSFER = "HDFS_DATA_TRANSFER";

  private static final ThreadLocal<String> PENDING_SASL = new ThreadLocal<>();
  /**
   * The exchange this thread was SERVING when it opened a SASL exchange of
   * its own as a client, set aside unended until that exchange closes.
   */
  private static final ThreadLocal<MessageDoors.Inbound> SERVING =
      new ThreadLocal<>();
  private static final ThreadLocal<Integer> SASL_DEPTH =
      ThreadLocal.withInitial(() -> 0);

  private CausynthMessagePropagation() {
  }

  public static Object captureScope() {
    return MessageDoors.captureScope();
  }

  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner) {
    return outbound(transport, correlationId, attemptId, half, localOwner,
        null);
  }

  /** The same leg, for work carrying the scope it was created in. */
  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner, Object scope) {
    return new Outbound(MessageDoors.outbound(transport, correlationId,
        attemptId, half, localOwner, scope));
  }

  /**
   * One request of the IPC client leaving, named by the operation its
   * request asks for ({@link #verb}): a DataNode turn's block report is that
   * turn's first report whether or not a heartbeat went before it, as the
   * recorded turn's was (IDENTITY §4).
   */
  public static Outbound outboundRequest(String transport,
      String correlationId, String attemptId, Object localOwner,
      Object scope, Object request) {
    return new Outbound(MessageDoors.outboundRequest(transport,
        correlationId, attemptId, localOwner, scope, verb(request)));
  }

  /**
   * One IPC request starting on the caller's thread, at its RPC engine's
   * invoke point before the client's call ({@link
   * MessageDoors#requestStarting}): named by the operation it asks for
   * ({@link #verb}), {@code attempt} the retry count its call carries.
   *
   * @return what {@link #requestEnded} takes, in the invoke's finally
   */
  public static long requestStarting(Object request, int attempt) {
    return MessageDoors.requestStarting(IPC, verb(request), attempt);
  }

  /** The request {@link #requestStarting} began is over. */
  public static void requestEnded(long request) {
    MessageDoors.requestEnded(request);
  }

  /**
   * The operation a protobuf RPC request asks for, as {@code
   * <protocol>.<method>} with the protocol's simple name: the name Hadoop
   * gives the request itself ({@code RpcProtobufRequest#toString}, from its
   * header, package-private in Hadoop), a constant of the call.  Any other
   * request names none ({@code ""}).
   */
  static String verb(Object request) {
    if (request == null
        || !"RpcProtobufRequest".equals(request.getClass().getSimpleName())) {
      return "";
    }
    String named = String.valueOf(request);
    int method = named.lastIndexOf('.');
    int protocol = method < 0 ? -1 : named.lastIndexOf('.', method - 1);
    return named.substring(protocol + 1);
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
    return new Inbound(MessageDoors.inbound(trace, symbolic, transport,
        correlationId, attemptId, half, localOwner, false));
  }

  public static void endInbound(Inbound scope) {
    if (scope != null) {
      MessageDoors.endInbound(scope.door);
    }
  }

  public static void endInbound() {
    MessageDoors.endInbound();
  }

  /**
   * Starts one multi-message SASL exchange on the client thread.
   *
   * <p>One exchange at a time on a thread: a begin nested inside another --
   * the same handshake reached through a second entry point, {@code
   * newSocketSend} into {@code send} -- is that same exchange, and only the
   * outermost end closes it.</p>
   *
   * <p>The thread may be SERVING an exchange while it opens this one: a
   * DataNode that received a write, a replace or a checksum request opens
   * its own handshake with the next node while it still serves the one it
   * received.  That served exchange is set aside, unended, for as long as
   * this one runs ({@link #outboundSasl} says why) and is the thread's again
   * when this one closes.</p>
   */
  public static void beginSasl() {
    int depth = SASL_DEPTH.get();
    SASL_DEPTH.set(depth + 1);
    if (depth == 0) {
      PENDING_SASL.set("hdfs-sasl-" + UUID.randomUUID());
      MessageDoors.Inbound serving = MessageDoors.setAside();
      if (serving != null) {
        SERVING.set(serving);
      }
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
    MessageDoors.endInbound();
    MessageDoors.Inbound serving = SERVING.get();
    if (serving != null) {
      SERVING.remove();
      MessageDoors.restore(serving);
    }
  }

  /**
   * Emits the next message of the current SASL exchange.
   *
   * <p>A message's half is the sender's ROLE in its exchange: the client of
   * an exchange this thread opened ({@link #beginSasl}) sends requests of
   * that exchange, whatever else the thread is serving, and only a thread
   * serving someone else's exchange answers it.  Asking "is this thread
   * serving a request?" first labelled a forwarding DataNode's own
   * handshake with the next node as the RESPONSE to the request it was
   * serving: hdfs-17967's head opened the mirror connection inside the
   * source's transfer, its key id went out under the source's correlation,
   * the recording stated no export of it on the head, and the plan never
   * instrumented the occurrence that sent it -- the key id every replay
   * delivered was then a free value.  The per-hop request scopes the trees
   * used to open around such connections hid exactly this.</p>
   */
  public static Outbound outboundSasl() {
    String correlationId = PENDING_SASL.get();
    if (correlationId != null) {
      // The previous message of THIS exchange -- the server's answer -- is
      // over; a served exchange was set aside by beginSasl.
      MessageDoors.endInbound();
      return outbound(SASL, correlationId, "1", MessageDoors.REQUEST, null);
    }
    MessageDoors.Inbound current = MessageDoors.current();
    if (current != null && MessageDoors.REQUEST.equals(current.half)) {
      return outbound(SASL, current.correlationId, current.attemptId,
          MessageDoors.RESPONSE, null);
    }
    MessageDoors.endInbound();
    return Outbound.EMPTY;
  }

  /** Installs one message without discarding values carried earlier in the
   * same multi-message SASL exchange. */
  public static Inbound inboundSasl(String trace, String symbolic,
      String correlationId, String attemptId) {
    boolean response = correlationId != null
        && correlationId.equals(PENDING_SASL.get());
    return new Inbound(MessageDoors.inbound(trace, symbolic, SASL,
        correlationId, attemptId,
        response ? MessageDoors.RESPONSE : MessageDoors.REQUEST, null, true));
  }

  /**
   * One DataTransfer op leaves ({@code Sender#send}): a request on a
   * correlation of its own (its SEND names the op's producer endpoint),
   * carrying the values its thread exported for the op, which the op's
   * trace info takes to the receiver with the correlation.  The sender keeps
   * serving whatever it serves: a DataNode forwards an op to its mirror
   * inside the op it received.
   */
  public static Outbound outboundOp() {
    return outbound(DATA_TRANSFER, "hdfs-dt-" + UUID.randomUUID(), "1",
        MessageDoors.REQUEST, null);
  }

  /**
   * A DataNode's turn received one op ({@code Receiver}, after its parse and
   * before any of its fields is read), into the turn's own context
   * ({@link MessageDoors#received}): the turn keeps its address, and the op
   * is served until the turn ends ({@link #endInbound}).
   */
  public static void inboundOp(String symbolic, String correlationId) {
    MessageDoors.received(symbolic, DATA_TRANSFER, correlationId, "1", null);
  }

  /**
   * Enters the scope a queued unit of work carried from where it was made:
   * the dequeue half of the IPC {@code Server.Call} transport mapping.
   */
  public static long enterCarriedScope(Object scope, String role,
      String api) {
    return MessageDoors.enterCarriedScope(scope, role, api);
  }

  /** Leaves the scope {@link #enterCarriedScope} entered. */
  public static void exitCarriedScope(long token) {
    MessageDoors.exitCarriedScope(token);
  }

  /** Opens one daemon tick as a root of its own: a service-loop turn. */
  public static long beginTick(Object owner, String role) {
    return MessageDoors.beginTick(owner, role);
  }

  /**
   * {@code who} is about to take startup {@code step} (the NameNode adding
   * a DataNode, by its UUID): a replay holds it to the order its recording
   * completed the step in.
   */
  public static Object startupStep(String step, String who) {
    return MessageDoors.startupStep(step, who);
  }

  /** The step {@link #startupStep} began completed. */
  public static void startupDone(Object pass) {
    MessageDoors.startupDone(pass);
  }

  /** Closes the tick {@link #beginTick} opened. */
  public static void endTick(long token) {
    MessageDoors.endTick(token);
  }

  /** Opens the recorded window: the workload's recording boundary. */
  public static void startRecording() {
    MessageDoors.startRecording();
  }

  /**
   * Whether the case declares its window open before its cluster starts
   * ({@code recording_window=startup}): the cluster adapter then opens it
   * there, else once the cluster is up.
   */
  public static boolean startupWindow() {
    return MessageDoors.startupWindow();
  }

  /**
   * Opens the construction of one node under the name it is then registered
   * by: what the construction starts or creates belongs to that node, though
   * the test's request stands where it runs (MessageDoors#beginNodeStartup).
   */
  public static long beginNodeStartup(String kind, String role,
      String sourceId) {
    return MessageDoors.beginNodeStartup(kind, role, sourceId);
  }

  /** Opens one startup of a registered node: a restart, or its start. */
  public static long beginNodeStartup(Object node) {
    return MessageDoors.beginNodeStartup(node);
  }

  /** Ends the startup {@code token} opened. */
  public static void endNodeStartup(long token) {
    MessageDoors.endNodeStartup(token);
  }

  /**
   * Whether this run is a concolic replay: a world the engine chose, where a
   * workload's check of the RECORDING's world (the key a node must still
   * retain, the gap that must still be open) is not the workload's to make.
   */
  public static boolean replaying() {
    return MessageDoors.replaying();
  }

  public static void registerSource(Object anchor, String kind, String role,
      String sourceId, long epoch) {
    MessageDoors.registerSource(anchor, kind, role, sourceId, epoch);
  }

  public static void registerSourceAlias(Object alias, Object anchor) {
    MessageDoors.registerSourceAlias(alias, anchor);
  }

  /**
   * Registers one node: its anchor as the source, and every object the node
   * runs its work through as the same node -- the RPC server a handler
   * serves, the SASL server a connection handshakes with, the DataNode a
   * daemon was started from.
   */
  public static void registerNode(Object anchor, String kind, String role,
      String sourceId, Object... aliases) {
    MessageDoors.registerNode(anchor, kind, role, sourceId, aliases);
  }

  public static void restartSource(Object anchor, String kind, String role,
      String sourceId, long epoch) {
    MessageDoors.restartSource(anchor, kind, role, sourceId, epoch);
  }

  public static long beginRequest(Object source, String api) {
    return MessageDoors.beginRequest(source, api);
  }

  public static void endRequest(long request, String api) {
    MessageDoors.endRequest(request, api);
  }

  /** What one outbound message carries. */
  public static final class Outbound {
    private static final Outbound EMPTY =
        new Outbound(MessageDoors.outboundNone());
    public final String correlationId;
    public final String attemptId;
    public final String trace;
    public final String symbolic;

    private Outbound(MessageDoors.Outbound door) {
      this.correlationId = door.correlationId;
      this.attemptId = door.attemptId;
      this.trace = door.trace;
      this.symbolic = door.symbolic;
    }

    public boolean active() {
      return !trace.isEmpty() || !symbolic.isEmpty();
    }
  }

  /** One installed inbound IPC or SASL message. */
  public static final class Inbound {
    private final MessageDoors.Inbound door;

    private Inbound(MessageDoors.Inbound door) {
      this.door = door;
    }
  }
}
