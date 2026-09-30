package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §1: the only two edge kinds (IDENTITY §4): {@link #WIRE}
 * export-to-attach, {@link #STATE} write version to observing read.
 */
public enum InteractionKind {
    WIRE,
    STATE
}
