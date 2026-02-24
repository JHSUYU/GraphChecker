package edu.uva.liftlab.graphchecker.staticanalysis;

public enum RecoveryPatternType {
    RETRY,
    FAILOVER,
    STATE_RESTORE,
    ASYNC_RECOVERY,
    ZOOKEEPER_BASED,

    MULTI_THREAD,
    UNKNOWN
}
