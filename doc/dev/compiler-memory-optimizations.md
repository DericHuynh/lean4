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
