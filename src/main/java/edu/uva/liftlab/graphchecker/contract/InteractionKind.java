package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 1: the two edge kinds of the causal graph.
 *
 * <p>{@link #WIRE} is an export paired with an attach (by the exchange
 * correlation id and the expression handle); {@link #STATE} is a write's
 * version paired with the read that observed it.  There is no third kind:
 * IDENTITY-V2 sec 3 -- lineage edges and version edges, nothing else.</p>
 */
public enum InteractionKind {
    WIRE,
    STATE
}
