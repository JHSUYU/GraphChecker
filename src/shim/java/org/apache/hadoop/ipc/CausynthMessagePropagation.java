package org.apache.hadoop.ipc;

import java.util.UUID;

import edu.uva.liftlab.graphchecker.runtime.MessageDoors;

public final class CausynthMessagePropagation {
  public static final String IPC = "HADOOP_IPC";
  public static final String SASL = "HDFS_SASL";
  public static final String DATA_TRANSFER = "HDFS_DATA_TRANSFER";

  private static final ThreadLocal<String> PENDING_SASL = new ThreadLocal<>();
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

  public static Outbound outbound(String transport, String correlationId,
      String attemptId, String half, Object localOwner, Object scope) {
    return new Outbound(MessageDoors.outbound(transport, correlationId,
        attemptId, half, localOwner, scope));
  }

  public static Outbound outboundRequest(String transport,
      String correlationId, String attemptId, Object localOwner,
      Object scope, Object request) {
    return new Outbound(MessageDoors.outboundRequest(transport,
        correlationId, attemptId, localOwner, scope, verb(request),
        carried(request, "payload")));
  }

  public static Outbound outboundResponse(String transport,
      String correlationId, String attemptId, Object localOwner,
      Object response) {
    return new Outbound(MessageDoors.outbound(transport, correlationId,
        attemptId, MessageDoors.RESPONSE, localOwner, null,
        carried(response, "message")));
  }

  public static void received(Object message) {
    MessageDoors.parsed(message);
  }

  static Object carried(Object wrapper, String field) {
    if (wrapper == null) {
      return null;
    }
    for (Class<?> type = wrapper.getClass(); type != null;
        type = type.getSuperclass()) {
      try {
        java.lang.reflect.Field held = type.getDeclaredField(field);
        held.setAccessible(true);
        return held.get(wrapper);
      } catch (NoSuchFieldException absent) {
      } catch (ReflectiveOperationException | RuntimeException sealed) {
        return null;
      }
    }
    return null;
  }

  public static long requestStarting(Object request, int attempt) {
    return MessageDoors.requestStarting(IPC, verb(request), attempt);
  }

  public static void requestEnded(long request) {
    MessageDoors.requestEnded(request);
  }

  public static Object handingOff(byte[] clientId, int callId) {
    return MessageDoors.handingOff(IPC, rpcCorrelation(clientId, callId),
        MessageDoors.REQUEST);
  }

  public static void handedOff(Object handoff) {
    MessageDoors.handedOff(handoff);
  }

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
      MessageDoors.putBack(serving);
    }
  }

  public static Outbound outboundSasl() {
    String correlationId = PENDING_SASL.get();
    if (correlationId != null) {

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

  public static Inbound inboundSasl(String trace, String symbolic,
      String correlationId, String attemptId) {
    boolean response = correlationId != null
        && correlationId.equals(PENDING_SASL.get());
    return new Inbound(MessageDoors.inbound(trace, symbolic, SASL,
        correlationId, attemptId,
        response ? MessageDoors.RESPONSE : MessageDoors.REQUEST, null, true));
  }

  public static Outbound outboundOp(Object op) {
    return new Outbound(MessageDoors.outbound(DATA_TRANSFER,
        "hdfs-dt-" + UUID.randomUUID(), "1", MessageDoors.REQUEST, null,
        null, op));
  }

  public static void inboundOp(String symbolic, String correlationId) {
    MessageDoors.received(symbolic, DATA_TRANSFER, correlationId, "1", null);
  }

  public static long enterCarriedScope(Object scope, String role,
      String api) {
    return MessageDoors.enterCarriedScope(scope, role, api);
  }

  public static void exitCarriedScope(long token) {
    MessageDoors.exitCarriedScope(token);
  }

  public static long beginTick(Object owner, String role) {
    return MessageDoors.beginTick(owner, role);
  }

  public static Object startupStep(String step, String who) {
    return MessageDoors.startupStep(step, who);
  }

  public static void startupDone(Object pass) {
    MessageDoors.startupDone(pass);
  }

  public static void endTick(long token) {
    MessageDoors.endTick(token);
  }

  public static void startRecording() {
    MessageDoors.startRecording();
  }

  public static boolean startupWindow() {
    return MessageDoors.startupWindow();
  }

  public static long beginNodeStartup(String kind, String role,
      String sourceId) {
    return MessageDoors.beginNodeStartup(kind, role, sourceId);
  }

  public static long beginNodeStartup(Object node) {
    return MessageDoors.beginNodeStartup(node);
  }

  public static void endNodeStartup(long token) {
    MessageDoors.endNodeStartup(token);
  }

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

  public static final class Inbound {
    private final MessageDoors.Inbound door;

    private Inbound(MessageDoors.Inbound door) {
      this.door = door;
    }
  }
}
