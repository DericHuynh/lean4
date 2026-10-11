# Research-driven native compiler memory optimizations

This experimental branch modifies the normal Lean4 elaboration → LCNF → native compilation pipeline. It is NOT a separate ELF emitter.

## Primary sources and reference implementations

**Morphic lifetime inference:** Brandon et al., *Fully-Automatic Type Inference for Borrows with Lifetimes*, OOPSLA 2026, https://doi.org/10.1145/3798221. Reference: https://github.com/morphic-lang/morphic/tree/main/crates/morphic_backend/src, especially annot_modes.rs, annot_obligations.rs, annot_rcs.rs and type_check_borrows.rs. Uses lifetime and mode constraints, function specialization, and reference-count insertion when inference cannot establish safe borrowing.

**FP² size-indexed reuse credits:** Lorenzen, Leijen, Swierstra, *FP²: Fully In-Place Functional Programming*, ICFP 2023, https://doi.org/10.1145/3607840. Paper: https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf. Reference implementation: https://github.com/koka-lang/koka. A no-allocation or constant-stack theorem requires linear resource credits and unique storage assumptions, not merely an equality proof.

**Destination Calculus:** Bagrel and Spiwack, OOPSLA 2025, https://arxiv.org/abs/2503.07489. Coq mechanization: https://github.com/tweag/destination-calculus. A general sound implementation requires linear/scoped destinations and proof that values cannot escape or be read before complete initialization.

**Lean stock compilation:** https://github.com/leanprover/lean4/blob/master/src/Lean/Compiler/LCNF/Passes.lean. The optimized baseline already inserts reset/reuse, performs borrowing inference and explicit RC, expands reuse and coalesces RC. Reference: *Counting Immutable Beans*, https://arxiv.org/abs/1908.05647.

## Implemented automatically in this draft: three-way ByteArray append fusion

The built-in pure-LCNF pass is inserted immediately after pullInstances and before simp/inlining. It recognizes either two direct ByteArray.fastAppend calls, or a chain of overloaded append operations with exactly the ByteArray.instAppend dictionary, instHAppendOfAppend and HAppend method projection. It requires an immediate return of the second result and no escaping intermediate. Unknown calls, arbitrary dictionaries, extra uses or mutable side effects do not match.

The pass selects ByteArray.fastAppend3, a destination-reserving implementation that fills a fresh buffer with three sequential copies. Subsequent stock passes re-infer borrowing, RC and reuse after this rewrite. The corresponding Lean equation proves byte-value equality with the original two appends, not physical allocation behavior.

A pinned v4.33.0-rc2 probe showed that impure LCNF contains only ByteArray.size and ByteArray.copySlice because fastAppend was inlined already, so an impure-phase matcher would be dormant. At base LCNF after pullInstances, both ordinary source forms are visible and were automatically fused; compilation and executable smoke tests passed. Probe: https://github.com/DericHuynh/lean4lean/actions/runs/38110432105 . Pin-specific kernel proof: see latest Append Fusion Probe actions on that fork.

## Explicit verification boundaries

- Source equation: byte values equal on all inputs, assuming Lean ByteArray source semantics.
- Compiler trigger: witnessed for both ordinary overload syntax and explicit fastAppend under the pinned companion probe.
- Full build of the real DericHuynh/lean4 fork: pending; the fork currently reports no Actions runs. Do not merge without a real compiler bootstrap and regression tests.
- Physical allocation/RC/memory bound: unproved. Destination capacity and copySlice implementation are runtime trust boundaries.
- Morphic lifetime solver: NOT YET IMPLEMENTED (stock Lean borrowing remains active).
- FP² FIP resource-credit checker: NOT YET IMPLEMENTED (stock Perceus-style reset/reuse remains active).
- General modal typed destinations/linear initialization: NOT YET IMPLEMENTED.
- End-to-end machine-code semantic correctness and faster Lean4 compiler builds: NOT ESTABLISHED.

Next: implement path-sensitive lifetime/mode constraints with conservative RC fallback and a checker for summaries; implement linear size-indexed credits on actual reset/reuse paths, including shared descendants and branch joins; establish a destination-capacity/initialization representation relation. Bind every certificate to actual generated IR. Test ablations against optimized stock Lean with physical allocator/RC instrumentation, without silently certifying a fallback.


## Automatic array-element borrow lifetime constraints

The stock Lean compiler already runs SCC-wide borrowing inference via a monotone ownedness fixed point; the Morphic reference compiler additionally tracks mode and lifetime constraints for each resource slot and then specializes calls. A first conservative part of that relationship is now integrated directly into Lean.Compiler.LCNF.InferBorrow: for Array.getInternal, Array.get!Internal, and Array.uget, if the extracted result is required to be owned, the source array is also required to be owned. Existing forward propagation from owner to element remains in place. The new OwnReason.arrayElementEscape is explicitly **not** correctness-forced: incrementing the extracted element independently remains a valid RC fallback, and existing borrowed ABI annotations must be respected. It participates in the normal SCC fixed-point analysis as an optional ownership preference before explicit RC.

This does not remove reference-count instructions on its own, nor does it constitute Morphic's full path-sensitive inference. It is a conservative, optional ownership preference for array-derived values; generic unknown calls retain stock ownership/RC behavior. Its runtime impact and proof obligations require evaluation separately from destination-passing speedups.

Code: src/Lean/Compiler/LCNF/InferBorrow.lean. Regression: tests/compile/array_borrow_lifetime.lean, with returned reference-typed elements, shared owner, branch selection, and read-only array size. The actual lean4 compiler bootstrap and tests must pass before any merged claim.

Research comparison: the Morphic borrow backend's annot_modes.rs builds lifetime/mode constraints, annot_obligations.rs discharges path obligations, annot_rcs.rs emits retains/releases, and type_check_borrows.rs checks moves and loan liveness. The current Lean change covers only one known borrowed projection class, not general nested shapes, path-sensitive lifetime joins, SCC mode specialization, or a proved runtime heap relation.

### Remaining formal verification requirements

* Prove an explicit operational model of scoped borrows, heap aliases, and RC transfer against Lean's actual LCNF and runtime operations; a Boolean mode propagation theorem alone is insufficient.
* Extend call summaries to record return-borrows-from-arguments and escaping projections with versioned ABI constraints, then validate constraints across SCC boundaries before changing a parameter's calling convention.
* Preserve tail calls, and reject unknown effects with RC fallback instead of claiming resource certificates.
* Track owned descendants separately from root uniqueness; map all field slots into resource equations before applying FP² storage reuse credits.
