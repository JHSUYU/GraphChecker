package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1: what kind of location a state edge is about.  {@link
 * #STORE} is a store the nodes share (ZooKeeper in a one-JVM cluster): its
 * owner is the transport, its slot the path as every run spells it, its
 * version the store's own; its rows come from the store doors, never from
 * the VM (IDENTITY §7.2).  {@link #VIEW} is one node's view of a store
 * location: its owner the transport at the node, its slot the store's; a
 * version is the store version the node last decoded, written by each
 * decode and read where a guard reads an object a decode made (SYMBOL-SCOPE
 * §6.4): a node decides on its view, which a later decode re-points.
 */
public enum LocationKind {
    STATIC,
    INSTANCE,
    ARRAY,
    MAP,
    STORE,
    VIEW
}
