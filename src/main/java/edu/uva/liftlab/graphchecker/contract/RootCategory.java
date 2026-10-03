package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.2: where a root's value enters the world (SYMBOL-SCOPE
 * §4), as the mint that made it knows.  The kind says how a witness may move
 * a root; the category says what moving it means: a decision reaching a
 * FAULT marker is a fault flip site, one reaching a boolean CONFIG is not.
 */
public enum RootCategory {
    /** A clock reading ({@code causynth.RootCatalog}). */
    CLOCK,
    /** A fault marker: a library door's or the workload's own. */
    FAULT,
    /** A configuration value ({@code causynth.ConfigRoots}). */
    CONFIG,
    /** A read of a location an unwoven accessor answers. */
    READ,
    /** A tree's own {@code CausynthSymbolicSource.symbolize} hook. */
    HOOK
}
