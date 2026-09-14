package edu.uva.liftlab.graphchecker.contract;

/**
 * The vocabulary of the composition manifest.
 *
 * <p>One artifact is written by a composer and read by the solve, decide and
 * emit stages, so the member names belong to the artifact rather than to
 * whichever composer produced it.  They live here so that replacing the
 * composer does not move the contract its readers were written against.</p>
 */
public final class ComposedManifest {
    public static final int SCHEMA_VERSION = 2;
    public static final String KIND = "CONCOLIC_COMPOSED_SMT";

    /** Whether the composition may be read as a candidate at all. */
    public static final String STATE = "state";
    public static final String CANDIDATE_READY = "CANDIDATE_READY";
    public static final String CANDIDATE_WITH_GAPS = "CANDIDATE_WITH_GAPS";

    public static final String FINAL_STATUS = "finalStatus";
    public static final String FINAL_READY = "FINAL_READY";
    public static final String FINAL_REFUSED = "FINAL_REFUSED";

    /** The anchored target, and the occurrences of it that were composed. */
    public static final String TARGET_REACH_OCCURRENCES =
            "targetReachOccurrences";
    public static final String TARGET_REACH_LEDGER = "targetReachLedger";

    /** Case selectors, and the subset a fault control makes conditional. */
    public static final String CASE_PARTITIONS = "caseSelectorPartitions";
    public static final String CONDITIONAL_CASE_PARTITIONS =
            "conditionalCaseSelectorPartitions";

    /** The roots, what each one recorded, and where they disagree. */
    public static final String CONFIGURED_SOURCE_MATERIALIZATION_FIELD =
            "configuredSourceMaterializations";
    public static final String CONFIGURED_SOURCE_MATERIALIZATION_KIND =
            "CONFIGURED_SYMBOLIC_SOURCE_MATERIALIZATION";
    public static final String CONFIGURED_SOURCE_MATERIALIZATION_AUTHORITY =
            "COMPOSER_CONFIGURED_SOURCE_PHASE_TERM_V3";
    public static final int CONFIGURED_SOURCE_MATERIALIZATION_SCHEMA = 3;
    public static final String MANUAL_SOURCE_MATERIALIZATION_FIELD =
            "manualSymbolicRootMaterializations";
    public static final String MANUAL_SOURCE_MATERIALIZATION_KIND =
            "MANUAL_SYMBOLIC_ROOT_MATERIALIZATION";
    public static final String MANUAL_SOURCE_MATERIALIZATION_AUTHORITY =
            "COMPOSER_MANUAL_SYMBOLIC_ROOT_TERM_V1";
    public static final String RECORDED_ROOT_VALUES = "recordedRootValues";
    /**
     * Where SOLVE publishes its valuations and mechanisms.
     *
     * <p>Beside the formula they are about, rather than in a file of their
     * own: one anchored occurrence, one artifact.</p>
     */
    public static final String SOLVER = "solver";
    public static final String RECORDED_SOURCE_VALUE = "recordedValue";
    public static final String RECORDED_VALUE_CONFLICT =
            "recordedValueConflict";

    /** Whether an UNSAT answer is closed over everything that was explored. */
    public static final String UNSAT_CLOSURE_COMPLETE =
            "unsatClosureComplete";
    public static final String UNSAT_CLOSURE_EVIDENCE =
            "unsatClosureEvidence";
    public static final String UNSAT_CLOSURE_AUTHORITY =
            "SELECTED_CAUSAL_PATH_UNSAT_CLOSURE_V1";

    /** Ledgers the witness legitimacy gates read. */
    public static final String BOUNDARY_DISPATCH_TOTALITY =
            "boundaryDispatchTotality";
    public static final String ABSENT_KEY_DEFAULTS = "absentKeyDefaults";
    public static final String WIRE_FLOW_BINDINGS = "wireFlowBindings";
    public static final String FAULT_CONTROL_GAPS_FIELD = "faultControlGaps";

    private ComposedManifest() {
    }
}
