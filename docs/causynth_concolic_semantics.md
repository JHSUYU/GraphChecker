# Causynth concolic semantics capability matrix

Status: implementation audit, 2026-07-21.

This document records the semantic boundary between the customized OpenJDK
expression IR and GraphChecker's two SMT encoders:

- `ConcolicConstraintSolver` builds a branch-flip candidate. A model from this
  stage is admitted only after an unforced concrete replay.
- `ConcolicSmtComposer` builds the cross-region bootstrap/final query. An item
  added to its `unsupported` set makes the composition manifest structurally
  incomplete.

## Supported execution envelope

Dynamic capture is intentionally and permanently scoped to the customized
HotSpot **Zero interpreter**. Workloads must run with that JDK and `-Xint`.
There is no C1/C2 compiler-IR or generated-code instrumentation, and running a
target without `-Xint` is outside the supported contract. The VM work described
below therefore means bytecode-interpreter instrumentation plus its HotSpot
concolic runtime (expression IR, shadow state, calls, native adapters, and
thread context), not JIT support.

The classifications below have deliberately narrow meanings:

- **Exact** means exact for the stated domain in the emitted SMT, including
  Java exception preconditions where stated.
- **Encoder-exact, boundary replay pending** means both GraphChecker encoders
  implement the stated Java/JVM relation and ordinary interpreter capture has
  been exercised, but exhaustive concrete replay of special boundary values
  has not yet been demonstrated. This is not a claim about untested values.
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
| `float`, `double` literals and roots | SMT `(_ FloatingPoint 8 24)` / `(_ FloatingPoint 11 53)`; literals are built from Java-parsed raw IEEE bits | Same FP sorts; typed `VFloat`/`VDouble` port carriers | Exact encoder semantics for binary32/binary64, including subnormals, signed zero, infinities, and NaN. Solver replay reads IEEE bits plus a separate `fp.isNaN` discriminator because `fp.to_ieee_bv` is unspecified for NaN. Ordinary `-Xint` capture is covered; exhaustive special-value materialization/replay remains pending. |
| String literal/root | SMT `String` content plus an explicit reference-nullness `Bool` | SMT `String` content plus an explicit reference-nullness `Bool` | Exact null/content separation for the serialized SMT Unicode-scalar domain. A null model is materialized as Java `null`; content operations require the non-null side condition. Java uses UTF-16 code units, so operations involving unpaired surrogates or code-unit inspection require an explicit restriction. |
| integral `+`, `-`, `*` | SMT `Int` operation followed by `java_int_wrap` or `java_long_wrap` | Same shared lowering | Exact Java two's-complement wrap for `int`/`long`, including overflow. Java binary numeric promotion is applied only when both operand widths are known. |
| floating `+`, `-`, `*`, `/` / VM `@` | `fp.add/sub/mul/div RNE` | Same shared lowering | Exact IEEE binary32/binary64 lowering, including NaN, infinities, signed zero, and rounding. Ordinary interpreter propagation is covered; a complete special-value replay matrix is still pending. Java floating `%` is deliberately not mapped to SMT `fp.rem`. |
| integral `/` / VM `@`, integral or floating `%` | Diagnostic term plus `unsupported` | Same | Fail-closed. Integral division still needs Java truncation toward zero, divide-by-zero, and `MIN_VALUE / -1`; Java floating remainder is not IEEE `fp.rem`. Neither encoder silently uses SMT `div`, `mod`, or `fp.rem`. |
| unary numeric negation | Width-aware wrap for `int`/`long`; `fp.neg` for binary32/binary64 | Same | Exact lowering, including `MIN_VALUE` wrap and floating signed zero/NaN behavior. Interpreter shadow propagation is covered; exhaustive special-FP replay remains pending. |
| `<`, `<=`, `>`, `>=`, `==`, `!=` on same-sort scalar values | Integer relations or `fp.lt/leq/gt/geq/eq`; nonnumeric/mismatched sorts are rejected | Same | Exact for admitted integral and IEEE FP operands. IEEE `!=` is `not fp.eq`, so NaN behavior is preserved. String equality is exact within the stated SMT-string domain; unsupported ordering fails closed. |
| `lcmp` IR operator `--` | Nested `ite` yielding Java int `-1/0/1` | Same | Exact. The Zero interpreter keeps the symbolic trichotomy on the shadow stack until the consuming `if*`; it no longer records a concrete compare witness that freezes the seed relation. |
| `fcmpl/g`, `dcmpl/g` IR operators `--l` / `--g` | Nested `ite` with `fp.isNaN`, `fp.lt`, and `fp.gt`, yielding Java int `-1/0/1` | Same | Exact lowering, including the required NaN result (`-1` for `*cmpl`, `1` for `*cmpg`). Trichotomy propagation through the consuming branch is covered; exhaustive special-FP replay remains pending. |
| `&`, `|`, `^`, `<<`, `>>`, `>>>` | Unsupported binary operator | Fresh term plus `unsupported` | Fail-closed. Supporting these exactly is best done with fixed-width bit-vectors, not unbounded `Int`. |
| `iinc` | `java_int_wrap(old + signed-byte-constant)` | Same | Exact Java int increment after the signed-immediate fix, including overflow. |
| 15 JVM primitive conversion opcodes | Explicit source/target table | Same | Exact Java lowering and typed VM capture for `i2l/f/d`, `l2i/f/d`, `f2i/l/d`, `d2i/l/f`, and `i2b/c/s`. This includes wrapping/narrowing, RNE FP conversion, and Java FP-to-integral NaN/overflow saturation rules. Casts produce values, not path assumptions. Reference casts are outside this scalar table; exhaustive special-FP replay remains pending. |
| `if_icmp*`, `ifeq` etc. | VM branch event points to the exact captured condition occurrence | Same | Exact when the operand expression is supported. Missing/unmodeled condition indices are rejected by branch-mapping admission. |
| `if_acmp*` / null comparisons | A controlled reference gets an exact `ref = nullRef` predicate; a null model becomes an explicit `NULL` replay assignment | Same scalar reference relation | Exact for null tests only when planned/applied assignment identity, path constraint, VM branch site/occurrence/outcome, and importer proof-catalog joins all agree. A non-null prefix preserves the concrete source object and is accepted only after exact ordered-prefix replay. Fabricating a non-null target object or an unproved alias remains fail-closed. |
| `lookupswitch` / `tableswitch`, selected arm | Exact VM event owns `selector == selectedKey` and an ordered PC-index suffix | Same observed guard can be composed | Exact **observation** only when opcode/site/successor/key order/condition indices all attest. It does not imply that the worklist can force every alternative successor. |
| `lookupswitch` / `tableswitch`, default arm | Exact VM event owns the ordered conjunction `selector != caseKey` for every key | Same observed conjunction can be composed | Exact observation of the default arm. Malformed/missing/reordered predicates fail closed. Multiway successor forcing remains fail-closed with `MULTIWAY_SWITCH_SUCCESSOR_WORKLIST_REQUIRED`; a binary true/false flip must not be used as a substitute. |
| switch with concrete selector | Exact conditionless event may still attest the observed successor | No symbolic selector relation is invented | Concrete observation only, explicitly not symbolic closure. |
| simple bounded `for` | Per-occurrence branch mappings plus `iinc`/arithmetic; worklist flips observed occurrences | Guarded path cases are merged | Exact only for finite explored paths within configured worklist bounds. This is not loop summarization. `while` loops are not currently part of the claimed workload envelope, even when their bytecode shape happens to be similar. |

## Java String matrix

`SymString` can emit many `OpStrExpression` names. The existence of a VM
handler means only that provenance was captured; it does not imply that an SMT
semantics exists.

| Operation | Solver | Composer | Classification |
| --- | --- | --- | --- |
| `contains` | `str.contains` including branch negation | Same | Exact for the SMT string domain, subject to the Java UTF-16 qualification above. The VM carries an unpolarized predicate (`_is_not=false`) through locals/calls; only the consuming `ifeq`/`ifne` applies path polarity. Thus a false seed observation does not turn the value itself into `not contains`. |
| `equals` (String argument) | SMT equality including `_is_not` | Same | Exact for non-null String operands in the SMT string domain. Non-String/null `Object` overload behavior is not claimed. |
| `startsWith(String)` | `str.prefixof` including `_is_not` | Same | Exact for the no-offset overload and SMT string domain. Offset overload fails arity checks. |
| `endsWith` | `str.suffixof` including `_is_not` | Same | Exact for the SMT string domain. |
| `isEmpty` | `str.len(s) = 0` | Same | Exact. Static helper variants are exact only for their captured non-null domain; library-specific null semantics are not modeled. |
| `length` | `str.len` | Same | Bounded abstraction because SMT length counts Unicode scalar values while Java length counts UTF-16 code units. Exact for strings whose Java code units correspond one-to-one with SMT characters. |
| `concat` / supported `StringBuilder` concatenation | `str.++` | Same | Exact for admitted all-String operands and the SMT string domain. Java null/exception behavior is represented only by successful captured executions. |
| `toString()` / `intern()` returning a String | Identity content edge; no new String operator | Same | The VM preserves the concrete oop selected by Java and propagates symbolic content only on the returned operand edge. `intern()` neither rewrites JVM canonical identity nor installs a symbolic shadow globally on the interned oop. Symbolic intern-table identity itself is not modeled, so identity-dependent synthesis remains outside the exact SMT claim. |
| primitive `toString` | Unsupported in the branch-flip solver | Composer supports a proved Java `int` decimal conversion only | Cross-stage gap. Keep non-int conversions fail-closed; add the same exact int conversion to the solver. |
| `charAt`, `compareTo`, `compareToIgnoreCase`, `copyValueOf`, `equalsIgnoreCase`, `getChars`, `hashCode`, `indexOf`, `lastIndexOf`, `matches`, `regionMatches`, `replace*`, `split` in general, `substring`/`subSequence`, `toCharArray`, case conversion, `trim`, `getBytes`, and overloads not listed above | `OP_STRING_OPERATOR:*` unsupported | `MODEL_SEMANTICS_MISSING:*` unsupported | Fail-closed. Regex, locale, UTF-16 indexing, exception behavior, and overload signatures must be modeled before promotion. |
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
an unsupported marker, casts use an explicit exact Java conversion table, and
both encoders apply numeric admission before ordering/arithmetic. The remaining
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
6. Java reference-null guards use exact `nullRef` predicates. Null prefix and
   target assignments are admitted only through a plural replay-proof catalog
   that binds each assignment and path constraint to one Zero-interpreter
   branch event; missing, duplicate, reordered, or tampered evidence is
   rejected. Non-null object synthesis is deliberately not claimed.

### Closed in the customized Zero interpreter (2026-07-21)

1. All 15 numeric conversion opcodes emit a typed `TypeCastExpression` and
   correctly replace their one- or two-word operand footprints. A conversion
   never adds `old == cast(old)` to the path condition.
2. `lcmp`, `fcmpl/g`, and `dcmpl/g` emit a symbolic `-1/0/1` expression and
   retain it until the actual consuming branch. The concrete-witness shortcut
   and its stale cross-branch state have been removed.
3. Category-1/category-2 ownership is explicit across constants, loads/stores,
   arithmetic, casts, comparisons, arrays, fields, Java/native calls and
   returns, `pop`/`pop2`, exception unwinds, and abandoned branch markers.
   Dedicated `-Xint` lifecycle smoke coverage checks that dead companion words
   cannot become later branch conditions.
4. Boolean-returning String calls retain an unpolarized symbolic value until
   the bytecode branch applies polarity. Interned Strings use detached/edge
   shadows so symbolization does not mutate JVM-global alias identity.

### P0: remaining semantic/exploration gaps

1. **Special floating-point replay:** extend concrete model/replay coverage to
   a full boundary matrix for signed zero, subnormals, infinities, NaNs, and
   FP-to-integral saturation. The SMT lowering is exact; the remaining gap is
   exhaustive end-to-end validation of those values.
2. **Multiway switch exploration:** add a successor-aware worklist. Until
   then, exact selected/default observation is retained but forcing another
   switch arm must report `MULTIWAY_SWITCH_SUCCESSOR_WORKLIST_REQUIRED`.
3. **Division/remainder:** integral division and both integral/floating `%`
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

A robust scalar campaign should retain, at minimum:

1. boolean + overflowing int arithmetic + simple bounded `for` (`iinc`, repeated
   branch occurrences), including `Integer.MIN_VALUE` negation;
2. long overflow and `lcmp`, plus binary32/binary64 rounding, signed zero,
   subnormal, infinity, NaN, `fcmpl/g`, and `dcmpl/g` paths;
3. both true and false `String.contains` paths and an astral-character length
   case documenting the UTF-16 bound;
4. category-2 values crossing calls, locals, stack shuffles, fields, casts,
   comparisons, returns, and exception unwinds, including checks that stale
   companion words never attach to later branches;
5. negative signed division/remainder, currently expected to fail closed, plus
   all 15 implemented primitive casts and their boundary values;
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
| Cast capture and category-2 slots | `bytecodeInterpreter.cpp`, `CONCOLIC_CONVERT_TYPE`, value-width shadow helpers, and conversion opcode stack offsets | `JavaPrimitiveSmtSemantics` and both encoders' `TypeCastExpression` lowering | Preserve typed source/target metadata for all 15 opcodes and whole-value one/two-word replacement. Keep VM lifecycle smoke coverage alongside encoder tests. |
| Generic method UF | VM `MethodExpression::serialize_internal`; call sites include `symbolicPrimitive.cpp` (`parseInt`/`parseLong`) | Solver `Encoder.methodTerm` near line 582; composer `Emitter.methodTerm` near line 4308 and `methodConstraint` near line 3639 | Exact whitelist/adapters first; otherwise mark `MODEL_SEMANTICS_MISSING`. Track UF count/identities in the manifest and exclude them from exact completeness. |
| Final completeness gate | N/A | `ConcolicSmtComposer.compose`, `structurallyComplete` near line 505 | Include any semantic-abstraction registry in the completeness predicate, not merely syntax/type gaps. |
| Divide/remainder spelling and semantics | `SymbolicOpStr` maps divide to `@`; `bytecodeInterpreter.cpp` binary arithmetic macros | Both encoders' `binary` methods | Floating `/` is SMT FP; keep integral `/` and all `%` fail-closed until exact Java lowering exists. |
| Exact switch observation vs exploration | `bytecodeInterpreter.cpp`, `_tableswitch`/`_lookupswitch`; `threadContext.cpp`, `record_branch_conditions` | `ConcolicRegionRuntime` exact switch-event validation; `RegionPathWorklist` | Preserve complete ordered arm predicates. Implement successor-aware forcing separately; never coerce a multiway event into one Boolean flip. |
| Compare trichotomy | `bytecodeInterpreter.cpp`, `CONCOLIC_OPC_TRICHOTOMY`; branch recording in `threadContext.cpp` | `JavaPrimitiveSmtSemantics.integralCompareResult` / `floatingCompareResult` and both `binary` methods | Preserve the symbolic result (`--`, `--l`, `--g`) on the shadow stack until its consuming `if*`; never reintroduce a concrete compare witness. |
| FP model materialization | N/A | `ConcolicConstraintSolver` FP bit/NaN queries; `SmtModelValueCodec`; `ConcolicPrimitiveBootstrapProjector` | Retain the separate NaN discriminator and exact bit decoding. Extend the replay matrix for special values without weakening the already-tested category-2 lifecycle. |
| String capture surface | `symbolicString.cpp`, `init_handle_method_names` near line 18 and `finish_method_helper` near line 178 | Solver `stringOperation` near line 458; composer `stringOperation` near line 3231 | Keep the explicit exact-operation whitelist. Add overload/signature and character-domain metadata before extending it. |
| Diagnostic fresh terms | N/A | Composer `unknownConstraint` near line 9088 and the unknown branches of `term`, `binary`, `codecGap` | Preserve fresh terms only for rendering, always paired with `unsupported`; add a regression asserting manifest `structurallyComplete=false`. |
| Signed `iinc` | `bytecodeInterpreter.cpp`, `_iinc` near line 1572 | Ordinary `+` lowering | Retain the explicit `(jint)(jbyte)pc[2]` constructor selection; smoke-test both positive and negative increments. |

The remaining implementation order is therefore:

1. special floating-point boundary replay;
2. successor-aware multiway switch forcing;
3. exact Java integral division/remainder and floating remainder;
4. stage-alignment gaps already explicit as unsupported (`int` `toString`,
   additional String operations, bitwise/shift support).
