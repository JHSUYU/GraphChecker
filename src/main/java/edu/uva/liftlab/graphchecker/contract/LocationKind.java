package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1: what kind of location a state edge is about.  {@link
 * #STORE} is a store the nodes share (ZooKeeper in a one-JVM cluster): its
 * owner is the transport, its slot the path as every run spells it, its
 * version the store's own; its rows come from the store doors, never from
 * the VM (IDENTITY §7.2).
 */
public enum LocationKind {
    STATIC,
    INSTANCE,
    ARRAY,
    MAP,
    STORE
}
