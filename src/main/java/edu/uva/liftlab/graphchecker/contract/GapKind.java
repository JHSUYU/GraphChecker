package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC 2: the closed set of things a stage may refuse on.
 *
 * <p>Closed on purpose: a kind without a consumer is a report nobody reads, and
 * the deletion pass removed several.  Every kind here is either BLOCKING for
 * some stage or a DIAGNOSTIC that a report prints, and the producer that raises
 * it states which on the row.</p>
 */
public enum GapKind {
    /** A selected path's replay was not admitted on its focused region. */
    ADMISSION_GAP,
    /** A replay paired an endpoint the epoch catalog does not have. */
    TOPOLOGY_DIVERGENCE,
    /** An arm from a run whose producer never stated a path condition. */
    UNATTESTED_ARM,
    /**
     * A focused replay left the schedule prefix it was held to.
     *
     * <p>Stated by the replay's turnstile at the position where the run's
     * next event was not the prefix's, with both events spelled out.  From
     * there the replay runs free, exactly as a replay with no prefix did:
     * DIAGNOSTIC, because what the prefix could not hold is an ordering fact,
     * and every row the replay publishes after it still states what ran.</p>
     */
    SCHEDULE_DIVERGED,
    /** A projection joined to no write version and pinned to no value. */
    UNSTATED_VALUE,
    /** An attach answered with a value no producer arm can produce. */
    UNPRODUCIBLE_ANSWER,
    /** The composed formula is satisfied at the recorded valuation. */
    FORMULA_SAT_AT_RECORDED_VALUATION,
    /** A root or a port the case never declared. */
    DECLARATION_MISSING,
    /** An address degraded because a lineage hop was unattributable. */
    LINEAGE_LOST,
    /** A planned task no activation of this replay answered. */
    TASK_UNANSWERED,
    /**
     * One planned task answered at two addresses across the corpus.
     *
     * <p>DIAGNOSTIC, and read by EXPLORE: an arm is owed once per planned
     * OCCURRENCE, so an address that moves between replays of the same plan
     * row splits one owed fact into two and the arms answered at the first
     * address settle nothing at the second.  The cause is upstream of any
     * wave -- what the execution index counted -- so the wave names it and
     * goes on.</p>
     */
    ADDRESS_UNSTABLE,
    /** The solver gave no answer in the time it was given. */
    SOLVER_TIMEOUT,
    /**
     * An activation closed at a different execution-index depth than it
     * opened at.
     *
     * <p>BLOCKING, and it has to be: the frames an occurrence stands on ARE
     * its identity (IDENTITY-V3 §1), so a frame pushed at an entry and not
     * popped at its exit moves the address of everything that runs after
     * it -- on hdfs-17960 it moved four frames onto the replay's index and
     * 34 of 81 planned tasks were refused on an address nobody could see
     * was wrong.  A leak cannot be reported as a diagnostic, because every
     * row published after it is addressed by the wrong occurrence.</p>
     */
    FRAME_UNBALANCED,
    /** A retained condition loop ran under an inherited K_L, not a declared
     *  one, so the model it produces is a prefix nobody stated. */
    BOUNDED_LOOP_BODY_BOUND_UNDECLARED,
    /** A retained array-indexed loop declared no K_L: its trip count is the
     *  array length the replay observes, which the replay states exactly. */
    BOUNDED_LOOP_FIXED_COUNT_BOUND_UNDECLARED,
    /** One loop nest's control sites do not all classify alike, so the nest
     *  is published as the weaker CONDITION_BOUNDED and named here. */
    BOUNDED_LOOP_CLASSIFICATION_INCONSISTENT,
    /** A declared wire flow no region of the slice holds the capture of. */
    COMMUNICATION_REQUEST_PORT_UNRESOLVED,
    /** A port truncated its recorded accesses, so the accesses above the
     *  retained ones are invisible to every later stage. */
    BOUND_INSUFFICIENT,
    /** Two activations of one region share an address: nothing IDENTITY-V3
     *  names tells them apart.  Every one of them is published with its own
     *  events, so a chain is not broken; a declared selector's k picks among
     *  them in seed order. */
    OCCURRENCE_ADDRESS_SHARED,
    /**
     * A mint this run could attribute to no node, so nothing was written.
     *
     * <p>BLOCKING for the session that met it: the wave's value for this
     * root was NOT written, so the replay ran the recording's value under an
     * obligation that asked for another one.</p>
     *
     * <p>IMPORT raises it too, under invariant 11: a session whose
     * expressions name a root's symbol and that states no {@code
     * RootMintRow} for that root carries a quantity no row of it
     * attributes.</p>
     */
    MINT_UNATTRIBUTED,
    /**
     * A message-carried context this side refused to install, so the
     * values that message carried are unattributed.
     *
     * <p>DIAGNOSTIC: the consequence is already on the rows the message
     * would have fed -- an attach with no element states {@code
     * elementAbsent} and mints v_H on the arrived value, and a send with no
     * request scope carries no header -- so this row is the reason those
     * say what they say, once per distinct refusal.  It is a row and not an
     * exception because the doors that raise it are called from inside the
     * workload's own transport: thrown, a refused registration-response
     * envelope stopped two DataNodes from ever registering and the
     * MiniDFSCluster wait never ended (lane11741d).</p>
     */
    MESSAGE_CONTEXT_REFUSED,
    /**
     * A mint of the right site at the wrong node epoch.
     *
     * <p>Same consequence, and the same class: a configured source is
     * reached once per node lifecycle, so an assignment applied at another
     * epoch rewrites a value the wave said nothing about.</p>
     */
    EPOCH_UNMATCHED,
    /**
     * A session no reader could read whole.
     *
     * <p>BLOCKING, raised at IMPORT: a truncated row or an absent {@code
     * manifest.json} makes a kind come back empty, which every later stage
     * reads as "this run had none".  Seven of the 11741 campaign #2 sessions
     * were cut by the campaign's kill, and one of them left a half-written
     * gap row that made the whole corpus unreadable with a JSON exception
     * instead of a named refusal.</p>
     */
    SESSION_INCOMPLETE,
    /**
     * A root the obligation assigns whose mint RAN in the replay and did not
     * plant the wave's value.  A root whose mint never ran is not one -- the
     * occurrence the obligation was for did not happen, which its
     * NOT_ADMITTED verdict states.
     *
     * <p>BLOCKING for the session that met it, and stated by the REPLAY: the
     * run read the recording's value where the wave asked for another one,
     * so it did not run what was asked.  11741 session
     * 869a1f0e285913ad-6f59cb84 is the case -- {@code
     * HDFS.BLOCK_KEY.SERIAL_NO} was minted through the field path, which
     * never asked for the wave's value -- and the composer meeting it as
     * "the mint states 182907 and the obligation assigns 182910" was the
     * second statement of the same fact, not the first.</p>
     */
    ASSIGNMENT_UNPLANTED,
    /**
     * A root the obligation assigns that the recording mints nowhere.
     *
     * <p>DIAGNOSTIC, and raised where the obligation is PROPOSED: a replay
     * plants an assignment at the MINT of the root, so an assignment the
     * recording published no mint for names no occurrence any replay could
     * be focused on, and running it would spend a replay on the recording's
     * own value.  The subject is the obligation -- that is what is not run
     * -- and the detail is the root, which is why.</p>
     *
     * <p>Told apart from {@link #ASSIGNMENT_UNPLANTED}, which is a REPLAY
     * that reached a mint and could not place the write: this one never
     * gets that far, and the wave spends nothing on it.</p>
     */
    ASSIGNMENT_UNMINTABLE,
    /**
     * One composed path whose own conjunction is unsatisfiable before any
     * root is considered.
     *
     * <p>BLOCKING, and raised at DECIDE.  A path is a question -- "is there
     * a world of this corpus in which this path reaches the fatal arm?" --
     * and a question that is unsat with every root free is not a question
     * about the roots at all: it is a contradiction the composition built.
     * The one that shipped for two rounds was pi_p carrying the anchor
     * decision's RECORDED polarity while phi_p asserted its complement, so
     * every path whose session did not observe the fatal arm was refuted by
     * construction -- all 7 paths of hdfs-11741 campaign #4 and 17960's own
     * third path, with z3's core naming only {@code path_fatal__*} and
     * {@code fatal_target} and no valuation assertion at all.  A claim
     * whose polarity rests on such a refutation states "the recording
     * decides the arm" about a formula no root could have satisfied, which
     * is why this is BLOCKING and why {@code polarityDecides} is withheld
     * beside it.</p>
     */
    PATH_SELF_CONTRADICTORY
}
