; ===========================================================================
; Environment axioms for T5 realizability refinement.
;
; Read by smt_realizability_refine.py --assume.  Directives live in comments
; so the file stays valid SMT-LIB text; everything that is not a directive is
; prose and is ignored.
;
;   ; @axiom <id>              start a block
;   ; @kind environment|control
;   ; @basis <text>            why this is an environment fact (repeatable,
;                              required)
;   ; @declare <name> <sort>   introduce an environment symbol
;   ; @select <selector> [arg] choose the terms the next @emit ranges over
;   ; @emit <template>         one assertion per selected term
;
; Selectors are engine vocabulary, never application vocabulary:
;   existential-root [<javaTypeDescriptor>]
;       every unconstrained producer listed in the reachability report.
;   clock-read
;       every constant the composer emitted for a System.currentTimeMillis()
;       read (environment__<scope>__currentTimeMills_<n>__<hash>).
;   existential-root-on-clock-timeline
;       MEASURED, not assumed: the roots that the composed query itself uses
;       as an operand of an ordering comparison (< > <= >=) whose other
;       operand is a clock read.  The script parses the query to derive this.
;   existential-root-clock-pair
;       the same relation, exposing ${root} and ${clock}.
;
; THE RULE.  An axiom here may constrain the environment: the domain of the
; clock, the sign of a duration, the epoch the timeline sits on.  It may
; never constrain program causality -- what the program computes from those
; values.  Asserting a computed relation in order to move the answer is
; forging a summary, and no result obtained that way means anything.  An
; axiom that assumes the answer is marked `@kind control` and is never
; selected by default; it exists so a control experiment can be run and
; reported as a control.
; ===========================================================================


; ---------------------------------------------------------------------------
; @axiom clock-read-nonnegative
; @kind environment
; @basis System.currentTimeMillis() is specified as the count of
; @basis milliseconds since the Unix epoch, 1970-01-01T00:00:00Z.  The
; @basis composed query constrains these reads only to the signed 64-bit
; @basis range (see the java integral domain assertion the composer emits
; @basis alongside each declaration), so the solver is currently free to
; @basis place a clock read before the epoch.  The recording this query was
; @basis composed from was produced by a JVM that ran, so its clock read a
; @basis time after the epoch.  A negative reading is not a value the
; @basis environment can deliver.
; @basis This bounds the environment oracle only.  It says nothing about
; @basis what the program computes from the reading, and it does not decide
; @basis any comparison the reading takes part in.
; @select clock-read
; @emit (>= ${term} 0)
; ---------------------------------------------------------------------------


; ---------------------------------------------------------------------------
; @axiom timeline-root-nonnegative
; @kind environment
; @basis These roots are unconstrained producers: no region inside the
; @basis closure defines them, so the solver may place them anywhere in the
; @basis signed 64-bit range, including before the epoch.
; @basis The selector is measured off the composed query, not assumed: a
; @basis root is included only if the query itself uses it as an operand of
; @basis an ordering comparison whose other operand is an environment clock
; @basis read.  A quantity that is ordered against a wall-clock reading
; @basis denotes a point on the same wall-clock timeline as that reading.
; @basis A point on the Unix-epoch timeline that the environment can
; @basis actually realise is non-negative.
; @basis What this constrains is the freedom granted to a MISSING producer,
; @basis not a relation the program computes.  It leaves every comparison
; @basis between such a root and a clock read free in both directions, so it
; @basis neither forces nor forbids the fatal branch.
; @select existential-root-on-clock-timeline
; @emit (>= ${term} 0)
; ---------------------------------------------------------------------------


; ---------------------------------------------------------------------------
; @axiom timeline-epoch-anchor
; @kind environment
; @basis Strictly stronger than the two axioms above and still neutral about
; @basis the answer: the whole wall-clock timeline -- every clock read and
; @basis every root ordered against one -- sits at or after a single
; @basis strictly positive anchor.  This rules out the family of models in
; @basis which the timeline is pinned at zero, without ordering any root
; @basis against any clock read, so the fatal branch stays free.
; @basis HONEST LIMIT: the anchor is left symbolic and only required to be
; @basis positive, so the solver may satisfy it with 1.  A dated anchor
; @basis (say "the run happened after 2020") would be materially stronger,
; @basis but nothing in the recorded artifacts carries a concrete clock
; @basis value to source it from: the trace records currentTimeMillis only
; @basis as a symbolic placeholder, never as a captured number.  Inventing a
; @basis date here would be fabricating evidence, so the anchor stays
; @basis symbolic until a recorder change supplies one.
; @declare env_epoch_anchor Int
; @emit (> env_epoch_anchor 0)
; @select clock-read
; @emit (>= ${term} env_epoch_anchor)
; @select existential-root-on-clock-timeline
; @emit (>= ${term} env_epoch_anchor)
; ---------------------------------------------------------------------------


; ---------------------------------------------------------------------------
; @axiom control-expiry-strictly-after-now
; @kind control
; @basis NOT AN ENVIRONMENT AXIOM.  Never selected by default; it must be
; @basis named explicitly with --axioms, and its result must be reported as
; @basis a control, never as a realizability result.
; @basis It asserts that every root ordered against a clock read is strictly
; @basis greater than that read.  That is the negation of the condition the
; @basis fatal branch consumes, so it assumes the answer.  Asserting it to
; @basis obtain UNSAT would be forging.
; @basis It is worth running exactly once, as an encoding check: if the
; @basis composed query really does make the fatal branch depend on this
; @basis comparison, forcing the comparison the other way must turn the
; @basis query UNSAT.  A "sat" here would mean the fatal branch is reachable
; @basis without the comparison going the failing way, i.e. the encoding is
; @basis not what it appears to be.  The result therefore says something
; @basis about the model's faithfulness and nothing about realizability.
; @select existential-root-clock-pair
; @emit (> ${root} ${clock})
; ---------------------------------------------------------------------------


; --- Measured non-axiom: clock monotonicity is not instantiable here -------
; Clock monotonicity is a legitimate environment axiom. It is not stated above
; because this candidate offers no pair of
; clock reads whose order is known.  The composer names a clock read
; environment__<scope>__currentTimeMills_<ordinal>__<hash> and notes that the
; VM restarts placeholder ordinals per replay task, so an ordinal orders
; reads only inside one scope.  All three clock reads in this candidate carry
; the same ordinal in three different case scopes: they are alternatives
; inside a case split, not a temporal sequence.  Asserting an order between
; them would be inventing one.  When a candidate does contain two reads in
; one scope with different ordinals, the axiom to add is
;   @select ... ; @emit (<= ${earlier} ${later})
; over that pair, and the selector to add is one that reads the ordinal off
; the composer's name within a fixed scope.
; ---------------------------------------------------------------------------
