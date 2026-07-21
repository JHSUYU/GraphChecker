# Causynth concolic semantics capability matrix

Status: implementation audit, 2026-07-21.

This document records the semantic boundary between the customized OpenJDK
expression IR and GraphChecker's two SMT encoders:

- `ConcolicConstraintSolver` builds a branch-flip candidate. A model from this
  stage is admitted only after an unforced concrete replay.
- `ConcolicSmtComposer` builds the cross-region bootstrap/final query. An item
  added to its `unsupported` set makes the composition manifest structurally
  incomplete.

The classifications below have deliberately narrow meanings:

- **Exact** means exact for the stated domain in the emitted SMT, including
  Java exception preconditions where stated.
- **Encoder-exact, E2E pending** means both GraphChecker encoders implement the
  stated Java/JVM relation, but the customized VM has not yet been shown to
  preserve the required expression and category-1/category-2 slot provenance
  through a real replay.  This is not an end-to-end exactness claim.
- **Bounded abstraction** means useful only under an explicit domain bound or
  a subsequent concrete replay; it must not be presented as full Java
  semantics.
- **Fail-closed** means the IR is retained as a diagnostic gap and cannot make
  a final composition complete.
- **Silent abstraction** means a free term or uninterpreted function is
  admitted without an `unsupported` marker. These are the highest-priority
  soundness risks.

## Scalar and control-flow matrix

| VM IR / Java feature | Branch-flip solver | Final composer | Classification and limits |
| --- | --- | --- | --- |
| `SymbolExpression`, integral primitives | SMT `Int`; exact byte/char/short/int/long root bounds and width metadata | SMT `Int`; typed port binding and the same bounds | Exact scalar values for admitted, explicitly typed roots. `int` and `long` share the transport sort but retain `JAVA_INT`/`JAVA_LONG` width metadata. Ambiguous widths fail closed. |
| Java `boolean` | SMT `Bool` in branch-flip solver | SMT `Int`, tested as zero/nonzero; Boolean report later restricts roots to 0/1 | Bounded abstraction at raw-composer level. The Boolean projection is exact only after its explicit 0/1 domain assertions are included. |
| `float`, `double` literals and roots | SMT `(_ FloatingPoint 8 24)` / `(_ FloatingPoint 11 53)`; literals are built from Java-parsed raw IEEE bits | Same FP sorts; typed `VFloat`/`VDouble` port carriers | Encoder-exact for binary32/binary64 literals and roots, including subnormals, signed zero, infinities, and NaN. Solver replay reads IEEE bits plus a separate `fp.isNaN` discriminator because `fp.to_ieee_bv` is unspecified for NaN. Full E2E status remains pending the VM cast/compare/slot audit below. |
| String literal/root | SMT `String` | SMT `String` | Exact for the serialized SMT Unicode-scalar domain. Java uses UTF-16 code units, so operations involving unpaired surrogates or code-unit inspection require an explicit restriction. |
| integral `+`, `-`, `*` | SMT `Int` operation followed by `java_int_wrap` or `java_long_wrap` | Same shared lowering | Exact Java two's-complement wrap for `int`/`long`, including overflow. Java binary numeric promotion is applied only when both operand widths are known. |
| floating `+`, `-`, `*`, `/` / VM `@` | `fp.add/sub/mul/div RNE` | Same shared lowering | Encoder-exact IEEE binary32/binary64 arithmetic, including NaN, infinities, signed zero, and rounding. E2E pending the VM audit; Java floating `%` is deliberately not mapped to SMT `fp.rem`. |
| integral `/` / VM `@`, integral or floating `%` | Diagnostic term plus `unsupported` | Same | Fail-closed. Integral division still needs Java truncation toward zero, divide-by-zero, and `MIN_VALUE / -1`; Java floating remainder is not IEEE `fp.rem`. Neither encoder silently uses SMT `div`, `mod`, or `fp.rem`. |
| unary numeric negation | Width-aware wrap for `int`/`long`; `fp.neg` for binary32/binary64 | Same | Exact at the encoder, including `MIN_VALUE` wrap and floating signed zero/NaN behavior. VM expression/slot fidelity is still part of the E2E audit. |
| `<`, `<=`, `>`, `>=`, `==`, `!=` on same-sort scalar values | Integer relations or `fp.lt/leq/gt/geq/eq`; nonnumeric/mismatched sorts are rejected | Same | Exact for admitted integral and IEEE FP operands. IEEE `!=` is `not fp.eq`, so NaN behavior is preserved. String equality is exact within the stated SMT-string domain; unsupported ordering fails closed. |
| `lcmp` IR operator `--` | Nested `ite` yielding Java int `-1/0/1` | Same | Encoder-exact for two admitted Java `long` operands. E2E pending: the current VM compare-witness path may freeze the concrete relation instead of propagating the symbolic trichotomy result to the following `if*`. |
| `fcmpl/g`, `dcmpl/g` IR operators `--l` / `--g` | Nested `ite` with `fp.isNaN`, `fp.lt`, and `fp.gt`, yielding Java int `-1/0/1` | Same | Encoder-exact, including the required NaN result (`-1` for `*cmpl`, `1` for `*cmpg`). E2E pending for the same VM compare-witness and category-2 slot reasons. |
| `&`, `|`, `^`, `<<`, `>>`, `>>>` | Unsupported binary operator | Fresh term plus `unsupported` | Fail-closed. Supporting these exactly is best done with fixed-width bit-vectors, not unbounded `Int`. |
| `iinc` | `java_int_wrap(old + signed-byte-constant)` | Same | Exact Java int increment after the signed-immediate fix, including overflow. |
| primitive casts in serialized IR | Explicit source/target table | Same | Encoder-exact for identity/integral widening, `int`/`long` to binary32/binary64 with RNE, and binary32/binary64 conversion. Narrowing, FP-to-integral, reference conversion, and unproved pairs fail closed. This is **not yet E2E-supported**: the VM `CONCOLIC_CONVERT_TYPE` path can currently erase in-place conversions or add a false equality assumption for non-identity conversions. |
| `if_icmp*`, `ifeq` etc. | VM branch event points to the exact captured condition occurrence | Same | Exact when the operand expression is supported. Missing/unmodeled condition indices are rejected by branch-mapping admission. |
| `if_acmp*` / null comparisons | VM can build reference equality/inequality when the required reference shadows (or an explicit null) are present | Same scalar reference relation | Encoder support exists, but missing reference-shadow provenance fails closed. Treat non-null alias replay as E2E pending until the new VM field/stack propagation has dedicated coverage. |
| `lookupswitch` / `tableswitch`, selected arm | Exact VM event owns `selector == selectedKey` and an ordered PC-index suffix | Same observed guard can be composed | Exact **observation** only when opcode/site/successor/key order/condition indices all attest. It does not imply that the worklist can force every alternative successor. |
| `lookupswitch` / `tableswitch`, default arm | Exact VM event owns the ordered conjunction `selector != caseKey` for every key | Same observed conjunction can be composed | Exact observation of the default arm. Malformed/missing/reordered predicates fail closed. Multiway successor forcing remains fail-closed with `MULTIWAY_SWITCH_SUCCESSOR_WORKLIST_REQUIRED`; a binary true/false flip must not be used as a substitute. |
| switch with concrete selector | Exact conditionless event may still attest the observed successor | No symbolic selector relation is invented | Concrete observation only, explicitly not symbolic closure. |
| simple bounded `for`/`while` | Per-occurrence branch mappings plus `iinc`/arithmetic; worklist flips observed occurrences | Guarded path cases are merged | Exact only for the finite explored paths and configured worklist bounds. This is not loop summarization and must report closure/bound gaps. |

## Java String matrix

`SymString` can emit many `OpStrExpression` names. The existence of a VM
handler means only that provenance was captured; it does not imply that an SMT
semantics exists.

| Operation | Solver | Composer | Classification |
| --- | --- | --- | --- |
| `contains` | `str.contains` including `_is_not` | Same | Exact for the SMT string domain; bounded by the Java UTF-16 qualification above. |
| `equals` (String argument) | SMT equality including `_is_not` | Same | Exact for non-null String operands in the SMT string domain. Non-String/null `Object` overload behavior is not claimed. |
| `startsWith(String)` | `str.prefixof` including `_is_not` | Same | Exact for the no-offset overload and SMT string domain. Offset overload fails arity checks. |
| `endsWith` | `str.suffixof` including `_is_not` | Same | Exact for the SMT string domain. |
| `isEmpty` | `str.len(s) = 0` | Same | Exact. Static helper variants are exact only for their captured non-null domain; library-specific null semantics are not modeled. |
| `length` | `str.len` | Same | Bounded abstraction because SMT length counts Unicode scalar values while Java length counts UTF-16 code units. Exact for strings whose Java code units correspond one-to-one with SMT characters. |
| `concat` / supported `StringBuilder` concatenation | `str.++` | Same | Exact for admitted all-String operands and the SMT string domain. Java null/exception behavior is represented only by successful captured executions. |
| primitive `toString` | Unsupported in the branch-flip solver | Composer supports a proved Java `int` decimal conversion only | Cross-stage gap. Keep non-int conversions fail-closed; add the same exact int conversion to the solver. |
| `charAt`, `compareTo`, `compareToIgnoreCase`, `copyValueOf`, `equalsIgnoreCase`, `getChars`, `hashCode`, `indexOf`, `intern`, `lastIndexOf`, `matches`, `regionMatches`, `replace*`, `split` in general, `substring`/`subSequence`, `toCharArray`, case conversion, `trim`, `getBytes`, and overloads not listed above | `OP_STRING_OPERATOR:*` unsupported | `MODEL_SEMANTICS_MISSING:*` unsupported | Fail-closed. Regex, locale, UTF-16 indexing, exception behavior, and overload signatures must be modeled before promotion. |
| structurally proved `parseInt(split(...))` decimal round-trip | Generic UF in branch-flip solver | Exact specialized proof in composer | Cross-stage gap. The composer proof is intentionally narrow; arbitrary `parseInt` remains unsupported semantically even if represented as a method call. |
| `parseLong` and other String-derived method calls | Diagnostic UF plus unsupported marker | Same | Fail-closed, not exact parsing semantics. A diagnostic SMT artifact may still be rendered, but cannot be reported as structurally complete. |

## Arrays, methods, and unknown expressions

| Feature | Behavior | Admission consequence |
| --- | --- | --- |
| Symbolic array load in branch-flip solver | Unconstrained SMT array plus selected-index equality | Candidate-only bounded abstraction; concrete replay must validate it. |
| Symbolic finite array load in composer | Requires an activation-local array/input bridge, finite length, bounds, and typed element equality | Exact for the captured finite array snapshot. Missing bridge is fail-closed. |
| Array store expression | Explicit unsupported marker | Fail-closed. |
| Recognized Map operations / finite map observations | Typed `MapState` operations plus required observation evidence | Exact only for the selected finite snapshot/effect sequence. Missing selectors/evidence are fail-closed. |
| Arbitrary `MethodExpression` | Both encoders may declare a sort-qualified diagnostic uninterpreted function and always add `MODEL_SEMANTICS_MISSING` | Fail-closed. The diagnostic UF keeps the SMT inspectable, but can no longer make branch-flip or final composition claim exact completeness. |
| Unknown expression `_type` | Composer creates a fresh term and adds `unsupported`; solver adds `unsupported` and returns no model | Fail-closed. |
| Unknown binary/String operator, invalid numeric literal, unbound placeholder | Composer may create a fresh well-sorted term, but also adds `unsupported`; solver does likewise or stops before Z3 | Fail-closed. The fresh term is diagnostic scaffolding, not admitted semantics. |
| Missing upstream region summary | Uninterpreted region relation plus `incompleteSummaries` | Fail-closed for final completeness. |
| Unknown/malformed Java scalar type | Usually falls back to reference sort | Correct for actual references, but a malformed primitive descriptor can be silently misclassified. Static port schema checks reduce this risk; the encoders should nevertheless reject unknown non-reference descriptors explicitly. |

### Answer to the free-variable audit

Most unknown-expression fallbacks are safe in the admission sense: although
the composer declares a fresh SMT term so that it can still render a diagnostic
query, it also appends an `unsupported` reason. `structurallyComplete` requires
that set to be empty.

The first three audited exceptions have been closed: arbitrary methods carry
an unsupported marker, casts use an explicit exact-widening table, and both
encoders apply numeric admission before ordering/arithmetic. The remaining
schema risk is an unknown Java type falling back to `Ref`; static port-schema
validation normally catches it, but malformed external IR remains fail-closed
work for a future hardening pass.

The earlier switch-default bug was fixed by attaching the complete, ordered
conjunction `selector != caseKey` to one exact switch event.  That proves the
observed default arm; it does **not** prove that the present binary-flip
worklist can enumerate every switch successor.

## Prioritized minimum repairs and regression workloads

### Closed at the GraphChecker encoder boundary (2026-07-21)

1. Integral roots are range-constrained and `int`/`long` `+`, `-`, `*`, unary
   negation, and `iinc` use exact two's-complement wrap.
2. Binary32/binary64 roots, literals, promotion, comparisons, `+`, `-`, `*`,
   `/`, and JVM `*cmp*` result terms use SMT FP rather than mathematical Real.
   NaN replay does not rely on the unspecified `fp.to_ieee_bv NaN` result.
3. `String.contains` and its false branch lower exactly to `str.contains` and
   `not str.contains`; unsupported String operations remain explicit gaps.
4. Unknown methods, casts, sorts, and operators cannot silently make a final
   composition complete.
5. Selected/default switch events can be checked as exact observations;
   malformed event ownership fails closed.

### P0: remaining E2E blockers

1. **VM conversion capture:** replace the current `CONCOLIC_CONVERT_TYPE`
   behavior with a real `TypeCastExpression` for every conversion opcode.
   In-place layout must not erase `f2d`, `d2f`, `i2l`, or narrowing, and a cast
   must not create a path assumption `old == cast(old)`.
2. **VM compare-result propagation:** preserve symbolic `lcmp`, `fcmpl/g`, and
   `dcmpl/g` `-1/0/1` expressions through the following `if*`.  A witness based
   only on the concrete result freezes the seed path and is not an exact
   symbolic guard, especially for NaN.
3. **VM slot audit:** verify every relevant load/store, dup/pop, call/return,
   field access, conversion, and comparison transition for category-2
   `long`/`double` values.  Until this is complete, the IEEE and `lcmp`
   lowerings are encoder-exact but not claimed E2E-exact.
4. **Multiway switch exploration:** add a successor-aware worklist.  Until
   then, exact selected/default observation is retained but forcing another
   switch arm must report `MULTIWAY_SWITCH_SUCCESSOR_WORKLIST_REQUIRED`.
5. **Division/remainder:** integral division and both integral/floating `%`
   remain fail-closed until Java exception, truncation, overflow, and remainder
   rules are encoded exactly.

### P1: stage alignment and bounded domains

1. Port the exact `int` `toString` and proved decimal round-trip semantics to
   the branch-flip solver; keep all other conversions fail-closed.
2. State the allowed String character domain in artifacts. If arbitrary Java
   strings are required, model UTF-16 code units rather than claiming SMT
   Unicode `str.len` is Java `String.length()`.
3. Add fixed-width bit-vector semantics for bitwise/shift operations only when
   workloads require them; the present fail-closed behavior is safer than an
   unbounded-Int approximation.

### P2: extend String only with exact overload-aware adapters

Candidate next operations are `indexOf` without UTF-16 ambiguity,
`substring`/`charAt` with explicit bounds, and non-regex replacements. Each
adapter must identify the Java overload/signature, encode exception
preconditions, and test both the true and false/exception paths. Regex,
locale-sensitive case conversion, and charset conversion should remain
fail-closed until their full domain is intentionally bounded.

## Required end-to-end coverage

A robust scalar campaign should include, at minimum:

1. boolean + overflowing int arithmetic + simple loop (`iinc`, repeated
   branch occurrences), including `Integer.MIN_VALUE` negation;
2. long overflow and `lcmp`, plus binary32/binary64 rounding, signed zero,
   subnormal, infinity, NaN, `fcmpl/g`, and `dcmpl/g` paths;
3. both true and false `String.contains` paths and an astral-character length
   case documenting the UTF-16 bound;
4. category-2 values crossing calls, locals, stack shuffles, fields, casts,
   comparisons, and returns before an E2E FP/long claim is promoted;
5. negative signed division/remainder and cast boundaries, currently expected
   to fail closed where semantics are not implemented;
6. lookup/table switch selected and default observations, plus an assertion
   that alternative forcing reports the explicit multiway-worklist gap;
7. one deliberately unsupported String operation and one arbitrary method
   call, verifying that neither can yield a `complete=true` exact report.

Every workload should inspect both the branch-flip record and final composition
manifest. A Z3 `sat` result alone is not semantic admission.

## Source audit anchors

Line numbers are from the 2026-07-21 worktree and may move; the named method or
macro is the stable anchor.

| Concern | Customized VM source | GraphChecker source | Minimum repair location |
| --- | --- | --- | --- |
| Shared Java numeric semantics | Opcode expression construction in `bytecodeInterpreter.cpp` | `JavaPrimitiveSmtSemantics`; both encoders' `binary`/`typeCast` methods | Retain width metadata, wrap functions, SMT FP formats, RNE operations, and fail-closed unsupported operators in one shared semantic authority. |
| Cast capture and category-2 slots | `bytecodeInterpreter.cpp`, `CONCOLIC_CONVERT_TYPE` and conversion opcode stack offsets | Both encoders already have explicit `TypeCastExpression` tables | Repair VM provenance first, then exercise `int/long/float/double` conversions through real replay. Encoder unit tests alone are insufficient. |
| Generic method UF | VM `MethodExpression::serialize_internal`; call sites include `symbolicPrimitive.cpp` (`parseInt`/`parseLong`) | Solver `Encoder.methodTerm` near line 582; composer `Emitter.methodTerm` near line 4308 and `methodConstraint` near line 3639 | Exact whitelist/adapters first; otherwise mark `MODEL_SEMANTICS_MISSING`. Track UF count/identities in the manifest and exclude them from exact completeness. |
| Final completeness gate | N/A | `ConcolicSmtComposer.compose`, `structurallyComplete` near line 505 | Include any semantic-abstraction registry in the completeness predicate, not merely syntax/type gaps. |
| Divide/remainder spelling and semantics | `SymbolicOpStr` maps divide to `@`; `bytecodeInterpreter.cpp` binary arithmetic macros | Both encoders' `binary` methods | Floating `/` is SMT FP; keep integral `/` and all `%` fail-closed until exact Java lowering exists. |
| Exact switch observation vs exploration | `bytecodeInterpreter.cpp`, `_tableswitch`/`_lookupswitch`; `threadContext.cpp`, `record_branch_conditions` | `ConcolicRegionRuntime` exact switch-event validation; `RegionPathWorklist` | Preserve complete ordered arm predicates. Implement successor-aware forcing separately; never coerce a multiway event into one Boolean flip. |
| Compare witness | `bytecodeInterpreter.cpp`, `CONCOLIC_CMP_TRIPLE_RES`; `threadContext.cpp`, `record_compare_witness` | `JavaPrimitiveSmtSemantics.integralCompareResult` / `floatingCompareResult` and both `binary` methods | Make the VM emit/propagate the trichotomy expression (`--`, `--l`, `--g`) instead of a concrete `<`, `=`, or `>` witness; audit long/double slot offsets. |
| FP model materialization | N/A | `ConcolicConstraintSolver` FP bit/NaN queries; `SmtModelValueCodec`; `ConcolicPrimitiveBootstrapProjector` | Retain the separate NaN discriminator and exact bit decoding. Promote to E2E exact only after VM/replay coverage of special values and category-2 paths. |
| String capture surface | `symbolicString.cpp`, `init_handle_method_names` near line 18 and `finish_method_helper` near line 178 | Solver `stringOperation` near line 458; composer `stringOperation` near line 3231 | Keep the explicit exact-operation whitelist. Add overload/signature and character-domain metadata before extending it. |
| Diagnostic fresh terms | N/A | Composer `unknownConstraint` near line 9088 and the unknown branches of `term`, `binary`, `codecGap` | Preserve fresh terms only for rendering, always paired with `unsupported`; add a regression asserting manifest `structurallyComplete=false`. |
| Signed `iinc` | `bytecodeInterpreter.cpp`, `_iinc` near line 1572 | Ordinary `+` lowering | Retain the explicit `(jint)(jbyte)pc[2]` constructor selection; smoke-test both positive and negative increments. |

The recommended implementation order is therefore:

1. VM cast/compare/category-2 slot fidelity, followed by real replay tests;
2. successor-aware multiway switch forcing;
3. exact Java integral division/remainder and floating remainder;
4. stage-alignment gaps already explicit as unsupported (`int` `toString`,
   additional String operations, bitwise/shift support).
