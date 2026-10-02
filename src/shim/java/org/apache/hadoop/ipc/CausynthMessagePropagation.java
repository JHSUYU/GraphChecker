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

import java.lang.reflect.Field;
import java.lang.reflect.Method;
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
  /** The exchange bracket the open SASL exchange owns: the user name its
   * client encodes travels with its next message. */
  private static final ThreadLocal<Long> SASL_BRACKET = new ThreadLocal<>();

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
   * The same leg with the payload the door holds before it is serialized:
   * the IPC client's {@code call.rpcRequest}, the server's response.  Its
   * protobuf message is what the transport's codec walks.
   */
  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner, Object scope,
      Object payload) {
    return new Outbound(MessageDoors.outbound(transport, correlationId,
        attemptId, half, localOwner, scope, message(transport, payload)));
  }

  /**
   * The protobuf message an IPC payload wraps: an {@code RpcProtobufRequest}
   * holds it in its {@code payload} field, a {@code ProtobufWrapper} answers
   * it from {@code getMessage()} (both package-private in Hadoop, read here
   * reflectively); anything else is its own message.  One it cannot read
   * is named, and the message carries none of its values.
   */
  static Object message(String transport, Object payload) {
    if (payload == null) {
      return null;
    }
    try {
      switch (payload.getClass().getSimpleName()) {
        case "RpcProtobufRequest":
          Field field = payload.getClass().getDeclaredField("payload");
          field.setAccessible(true);
          return field.get(payload);
        case "ProtobufWrapper":
          Method getter = payload.getClass().getDeclaredMethod("getMessage");
          getter.setAccessible(true);
          return getter.invoke(payload);
        default:
          return payload;
      }
    } catch (ReflectiveOperationException | RuntimeException unreadable) {
      MessageDoors.payloadUnread(transport, payload.getClass().getName()
          + ": " + unreadable);
      return null;
    }
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
      SASL_BRACKET.set(MessageDoors.beginExchange(SASL));
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
    Long bracket = SASL_BRACKET.get();
    if (bracket != null) {
      SASL_BRACKET.remove();
      MessageDoors.endExchange(bracket);
    }
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

  /** Closes the tick {@link #beginTick} opened. */
  public static void endTick(long token) {
    MessageDoors.endTick(token);
  }

  /** Opens the recorded window: the workload's recording boundary. */
  public static void startRecording() {
    MessageDoors.startRecording();
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
