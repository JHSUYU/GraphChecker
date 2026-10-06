package edu.uva.liftlab.graphchecker.contract;

/**
 * CONTRACT-SPEC §2.5: the closed set of things a stage may refuse on.  Closed on
 * purpose: every kind has a consumer, and the producer states on the row
 * whether it is BLOCKING or DIAGNOSTIC.
 */
public enum GapKind {
    /** A selected path's replay was not admitted on its focused region. */
    ADMISSION_GAP,
    /** A replay paired an endpoint the epoch catalog does not have. */
    TOPOLOGY_DIVERGENCE,
    /** An arm from a run whose producer never stated a path condition. */
    UNATTESTED_ARM,
    /**
     * A focused replay left its schedule prefix; stated by the turnstile with
     * both events.  DIAGNOSTIC: the replay runs free after it and its rows
     * still state what ran.
     */
    SCHEDULE_DIVERGED,
    /** A projection joined to no write version and pinned to no value. */
    UNSTATED_VALUE,
    /** An attach answered with a value no producer arm can produce. */
    UNPRODUCIBLE_ANSWER,
    /** The composed formula is satisfied at the recorded valuation. */
    FORMULA_SAT_AT_RECORDED_VALUATION,
    /**
     * The declared occurrence took the fatal arm in the recording: the case
     * declares an occurrence that throws as recorded, so no counterfactual
     * is asked of it (PLAN, BLOCKING).
     */
    TARGET_FATAL_IN_RECORDING,
    /**
     * A guard of the declared target reaches it on both arms, so the scope
     * map states no fatal arm at the declared occurrence (PLAN, BLOCKING):
     * the declaration names no question.
     */
    AMBIGUOUS_FATAL_ARM,
    /**
     * The seed replay observed the fatal at the declared occurrence: the run
     * as recorded is no counterfactual, so no claim stands on the corpus
     * (COMPOSE, BLOCKING).  Beside {@link #TARGET_FATAL_IN_RECORDING} it is
     * the declaration's; without it the replay diverged from its recording.
     */
    SEED_OBSERVED_FATAL,
    /** A root or a port the case never declared. */
    DECLARATION_MISSING,
    /**
     * A tree hook ran in a case whose plan declares its source nowhere: no
     * root of this case, nothing minted, its value concrete.  DIAGNOSTIC;
     * a closed negative (UNSAT_CLOSED) counts them in {@code result.json}
     * ({@code undeclaredHookCount}).
     */
    HOOK_UNDECLARED,
    /** An address degraded because a lineage hop was unattributable. */
    LINEAGE_LOST,
    /**
     * A planned task no activation of this replay answered (DIAGNOSTIC: the
     * replay states what ran instead).  BLOCKING when PLAN states it: a row
     * whose anchor names a node its occurrence address does not, which no
     * activation can answer.
     */
    TASK_UNANSWERED,
    /**
     * An address a run did not reproduce, DIAGNOSTIC, in one of three
     * places.  EXPLORE ({@code explore.ExploreMain}): one planned task
     * answered at two addresses across the corpus, its subject the task id
     * -- arms answered at one address settle nothing at the other; the
     * cause is the execution index, upstream.  A replay ({@code
     * runtime.RowRuntime#answered}): a planned occurrence ran at another
     * address and answers it by its shape (IDENTITY §9), its rows stated at
     * the planned address, its subject that address -- read by {@code
     * explore.SlotTable} and CONFIRM.  A CONFIRM run ({@code
     * runtime.Confirmation#attached}): a delivery into the anchor came from
     * a producer at another address than the model's that answers the
     * model's producer's question, its subject the consumer endpoint.
     */
    ADDRESS_UNSTABLE,
    /** The solver gave no answer in the time it was given. */
    SOLVER_TIMEOUT,
    /**
     * An activation closed at a different execution-index depth than it
     * opened at.  BLOCKING: frames are identity (IDENTITY §3), so a leaked
     * frame misaddresses every later row.
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
    /** Two activations of one region share an address (IDENTITY §5: the
     *  address cannot tell them apart); each keeps its events, and a
     *  selector's k picks in seed order. */
    OCCURRENCE_ADDRESS_SHARED,
    /**
     * A mint this run could attribute to no node, so the wave's value was not
     * written (BLOCKING for that session).  IMPORT also raises it (invariant
     * 11) for a named root symbol with no {@code RootMintRow}.
     */
    MINT_UNATTRIBUTED,
    /**
     * A message-carried context this side refused to install, so its values
     * are unattributed.  DIAGNOSTIC: the affected rows already say so
     * ({@code elementAbsent}); this names why, once per refusal.  A row, never
     * an exception: the doors run inside the workload's transport, where a
     * throw can hang the cluster.
     */
    MESSAGE_CONTEXT_REFUSED,
    /**
     * A mint of the right site at the wrong node epoch; applying the
     * assignment there would rewrite a value the wave said nothing about.
     */
    EPOCH_UNMATCHED,
    /**
     * A session no reader could read whole.  BLOCKING at IMPORT: a truncated
     * row or absent {@code manifest.json} reads back as "this run had none".
     */
    SESSION_INCOMPLETE,
    /**
     * An assigned root whose mint RAN in the replay without planting the
     * wave's value (a mint that never ran is NOT_ADMITTED instead).
     * BLOCKING for that session, stated by the replay.
     */
    ASSIGNMENT_UNPLANTED,
    /**
     * An assigned root the recording mints nowhere, so no replay could plant
     * it.  DIAGNOSTIC, raised when the obligation is proposed; the obligation
     * is not run.  Unlike {@link #ASSIGNMENT_UNPLANTED}, no replay is spent.
     */
    ASSIGNMENT_UNMINTABLE,
    /**
     * Every composed path unsatisfiable with every root free, and this one
     * so even without its fatal arm, or after observing it: a contradiction
     * the composition built, not a fact about roots (DIAGNOSTIC per path,
     * BLOCKING for the composition at DECIDE).  A path its fatal arm alone
     * refutes is one no root turns, the claim's own answer and no gap.
     */
    PATH_SELF_CONTRADICTORY,
    /**
     * The confirmation replay took an edge the model did not choose (a
     * family arm or a state join), named with the edge taken instead.
     * DIAGNOSTIC, read by CONFIRM: any one downgrades the claim to
     * SAT_UNCONFIRMED.  The expectation never steers the run.
     */
    CONFIRM_MISMATCH,
    /**
     * A model CONFIRM refuted, which the composition excludes so the next
     * claim is another model or none ({@code compose.Refutations}).
     * DIAGNOSTIC: the exclusion is the composition's own knowledge.
     */
    CLAIM_REFUTED,
    /**
     * A model CONFIRM gave no verdict on, excluded as a refuted one is so the
     * next claim follows; an UNSAT resting on it is no verdict ({@code
     * compose.ComposeMain#campaignClaim}).  DIAGNOSTIC.
     */
    CLAIM_REFUSED
}
