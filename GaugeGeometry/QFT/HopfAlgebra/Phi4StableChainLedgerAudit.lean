import GaugeGeometry.QFT.HopfAlgebra.Phi4NestedBoundaryIdCoherenceAudit
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBoundaryIdempotence
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableGenuineForestBlockEquiv
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableFiniteSumReindex
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoproductCoassociativity
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovFactorization
import GaugeGeometry.QFT.HopfAlgebra.Phi4CarrierGapBogoliubovDroppedSector
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRenormalizationSettlement

/-!
# φ⁴₄ stable chain — reproducible theorem ledger / axiom audit

**A single, self-contained audit module** turning the sprint log into a **reproducible
theorem ledger**. Building this file (`lake build
GaugeGeometry.QFT.HopfAlgebra.Phi4StableChainLedgerAudit`) re-checks every headline of the
QFT-R1 (coproduct + coassociativity) and QFT-R2 (renormalization Birkhoff factorization +
Figure-1 discrepancy) claim in one place: it first `#check @`s each declaration by its
ACTUAL name (so a rename cannot silently pass — the build fails if a name is wrong), then
`#print axioms` each. A reviewer runs this one build and reads the emitted axiom lines.

## What this ledger machine-checks (by building green + the emitted `#print axioms`)

1. **No `sorry` / `admit` / project-level axiom.** Every `#print axioms` below emits exactly
   `[propext, Classical.choice, Quot.sound]` (a `sorry`/`admit` would surface `sorryAx`; a
   project axiom would surface its name). No `native_decide` / `Lean.ofReduceBool` (would
   surface `Lean.ofReduceBool`).
2. **Build green.** This module compiles against the pinned toolchain (Lean `v4.29.0`,
   Mathlib `v4.29.0`); a broken upstream proof fails this build.
3. **Names resolve.** Each `#check @` pins the declaration by its exact name; a rename or a
   deleted theorem fails this build (the body-626 "false-clean" guard: never trust
   `#print axioms` on an unbound/prefixed name).

## What this ledger records (verified once, by the method stated; re-checkable)

4. **No forbidden divergence class in any headline type.** None of
   `IsPermInvariantDivergence`, `IsIsoInvariantDivergence`, `IsAmbientInvariantDivergence`,
   `IsDivergencePreservedByContract`, `IsDivergencePreservedByAdmissibleForestContract`,
   `IsDivergenceReflectedByAdmissibleForestContract` appears in any `#check @` printed type
   below. *(Method: grep the eight `#check @` outputs for these class names — none occur;
   the φ⁴ power-counting enters only as the concrete providable `phi4DivergenceMeasureFamily`
   value, never as a typeclass hypothesis.)*
5. **No `HEq` / `cast` / graph-data `▸` in any headline type.** Every `#check @` type below is
   homogeneous; the few dependent transports of the forest-block inverse live in `private`
   helper bodies, never in a public statement. *(Method: `#check @` type inspection; the
   public declaration types carry no `HEq`/`cast`.)*
6. **No consumption of the old unstable coproduct.** The stable chain never imports or
   references the old (naive, non-idempotent) resolved coproduct: coassociativity holds
   because the naive boundary completion is provably *not* relabeling-stable
   (`nested_direct_singletonProfile_ne`), so the whole chain is rebuilt on the stable
   idempotent completion (`stableBoundaryIterate_idempotent`). *(Method: the stable chain's
   import DAG does not include a pre-stable coproduct term; the no-go itself is banked as a
   theorem here.)*
7. **No forest-occurrence dedup.** All forest sums are `Finset.sum` over `.attach` of the
   carrier index with **exact component multiplicity** — no `Multiset.dedup` / `.toFinset`
   collapse of ID-distinct occurrences (that would change coefficients). The forest-block
   map is a genuine **bijection** (`stablePhi4ForestBlockEquiv`, both inverses proved), so
   the finite-sum reindex (`stableForestBlock_finiteSum_reindex`) preserves every weight.

## Theorem → source file → introducing commit

| # | Declaration | Source file | Commit |
|---|---|---|---|
| 1 | `nested_direct_singletonProfile_ne` (naive completion **not** relabeling-stable — the no-go) | `Phi4NestedBoundaryIdCoherenceAudit.lean` | `c357c03` |
| 2 | `stableBoundaryIterate_idempotent` (stable iterate `=` normal form — idempotent completion) | `Phi4StableBoundaryIdempotence.lean` | `6af86a5` |
| 3 | `stablePhi4ForestBlockEquiv` (weight-preserving forest-block **bijection**) | `Phi4StableGenuineForestBlockEquiv.lean` | `fcfea57` |
| 4 | `stableForestBlock_finiteSum_reindex` (the two residual sums coincide) | `Phi4StableFiniteSumReindex.lean` | `eb2cd58` |
| 5 | `coproduct_resolved_stable_phi4_coassociative` (**QFT-R1 crown** — Δᵣˢ coassociative) | `Phi4StableCoproductCoassociativity.lean` | `de44ee9` |
| 6 | `phi4Bogoliubov_birkhoff_factorization` (**QFT-R2 crown** — `φ₋ ⋆ φ = φ₊`) | `Phi4StableBogoliubovFactorization.lean` | `dd57810` |
| 7 | `phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector` (Figure-1 dropped-sector) | `Phi4CarrierGapBogoliubovDroppedSector.lean` | `f3a302d` |
| 8 | `phi4StableCK_renormalization_settlement` (public settlement — 5 ∧ 7 bundled) | `Phi4StableRenormalizationSettlement.lean` | `e7351fa` |

(Commits are the *introducing* commit of each file, on `main`; `v2.0.0` = `10.5281/zenodo.21765915`.)

This module contains **no new mathematics** — only `#check @` / `#print axioms` diagnostics.
It defines nothing, so it introduces no axioms of its own; the emitted lines are exactly the
dependency footprints of the eight audited declarations.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step A — pin every declaration by its ACTUAL name (rename ⇒ build fails) -/

-- QFT-R1: the stability no-go, the idempotent repair, the bijection, the reindex, the crown
#check @nested_direct_singletonProfile_ne
#check @stableBoundaryIterate_idempotent
#check @stablePhi4ForestBlockEquiv
#check @stableForestBlock_finiteSum_reindex
#check @coproduct_resolved_stable_phi4_coassociative

-- QFT-R2: the Birkhoff factorization crown, the Figure-1 discrepancy, the public settlement
#check @phi4Bogoliubov_birkhoff_factorization
#check @phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector
#check @phi4StableCK_renormalization_settlement

/-! ## Step B — axiom footprint of every declaration
    (each must emit exactly `[propext, Classical.choice, Quot.sound]`) -/

#print axioms nested_direct_singletonProfile_ne
#print axioms stableBoundaryIterate_idempotent
#print axioms stablePhi4ForestBlockEquiv
#print axioms stableForestBlock_finiteSum_reindex
#print axioms coproduct_resolved_stable_phi4_coassociative

#print axioms phi4Bogoliubov_birkhoff_factorization
#print axioms phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector
#print axioms phi4StableCK_renormalization_settlement

end GaugeGeometry.QFT.Combinatorial
