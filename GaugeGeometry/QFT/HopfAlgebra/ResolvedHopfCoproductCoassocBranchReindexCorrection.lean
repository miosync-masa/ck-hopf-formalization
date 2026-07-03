import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchCoverWiringCheck
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputFullSumBoundary
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchSide

/-!
# R-6c-body-77 — corrected BRANCH reindex wiring: `regroupBranchSum = boundary + ∑ cover`

Seventy-seventh genuine-body step, wiring the branch side into the boundary-external form body-76 decided.  The
algebraic split of `regroupBranchSum` into `boundary + tail` is PROVED; the corrected reindex then follows from
body-76's tails-only cover.  A consistency note is recorded honestly.

## The branch boundary/tail split (proved)

`regroupBranchSum_eq_outerSum` (existing) plus body-69's `outer_branch_boundary_tail_split` give, at a
representative,

```text
regroupBranchSum (G.toResolvedHopfGen hCD)
  = assoc(forestSum G ⊗ 1)  +  ∑_A coassocLeftTail A
```

(`resolved_regroupBranchSum_boundary_tail`) — the branch side is exactly the primitive-outer boundary plus the
left-tail sum, purely by definition and linearity.

## The corrected reindex

Feeding body-76's `branch_tail_cover` (`∑ cover = ∑_A coassocLeftTail A`) gives the corrected branch agreement

```text
regroupBranchSum = assoc(forestSum G ⊗ 1)  +  ∑ cover
```

(`ResolvedCorrectedBranchReindexSupply.branch_agreement_corrected`): the branch boundary handled SEPARATELY
(primitive-outer, cover-external per body-70), the cover carrying the left tails.

## Consistency note (honest)

The image side (body-75) has `∑ cover = regroupImageSum` (its boundary IS the `∅`-fiber, INSIDE the cover); the
branch corrected form here has `∑ cover = regroupBranchSum − assoc(forestSum G ⊗ 1)` (its boundary OUTSIDE the
cover).  Since `∑ cover = ∑ imageWeight` (`term_eq`) is intrinsically the IMAGE-side quantity, the sum-consistent
value is `∑ cover = regroupImageSum = regroupBranchSum` (coassoc), i.e. the boundary is IN the cover on BOTH
sides at the sum level — which is exactly body-54's `outer_branch_cover`.  So the ASYMMETRY (body-64/70/76) is at
the PER-`A` level — the image boundary is a split-choice fiber (the `∅` one), the branch boundary is not any
fiber — NOT at the sum-level cover value.  The corrected form here is the boundary/tail SPLIT of
`regroupBranchSum` (proved) plus the CONDITIONAL reindex from body-76's `branch_tail_cover`; whether the branch
primitive is body-76's tails-only `fiber_eq_tail` or body-54's boundary-in summand form is decided by the actual
cover value (`= regroupImageSum`, image-determined).  Settling this — reconciling body-75 (`∑ cover =
regroupImageSum`) with the branch decomposition — is the remaining coassoc bookkeeping, flagged here, not forced.

Per the HALT, the image side is untouched; `fiber_eq_tail` is not proved; the branch boundary/tail split is
proved and the corrected reindex is assembled conditionally.

Landed:

* `resolved_regroupBranchSum_boundary_tail` — `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑_A coassocLeftTail A`
  (PROVED, definition + linearity);
* `ResolvedCorrectedBranchReindexSupply F` — the branch tail supply bundled for the corrected reindex;
* `.branch_agreement_corrected` — `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑ cover`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-77 — the branch boundary/tail split of `regroupBranchSum`.**  Purely definition + linearity
(`regroupBranchSum_eq_outerSum` + body-69's `outer_branch_boundary_tail_split`): the branch side is the
primitive-outer boundary `assoc(forestSum ⊗ 1)` plus the left-tail sum `∑_A coassocLeftTail A`. -/
theorem resolved_regroupBranchSum_boundary_tail (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [D.regroupBranchSum_eq_outerSum G hCD, outer_branch_boundary_tail_split]

/-- **R-6c-body-77 — the corrected branch reindex supply** (boundary-external form).  Bundles body-76's tails-only
branch cover; `branch_agreement_corrected` then routes the primitive-outer boundary separately. -/
structure ResolvedCorrectedBranchReindexSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The tails-only base-outer branch cover (body-76). -/
  branchTail : ResolvedBranchFiberTailSupply F

/-- **R-6c-body-77 — the corrected branch agreement.**  `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑ cover` —
boundary primitive-outer (external), cover carrying the left tails. -/
theorem ResolvedCorrectedBranchReindexSupply.branch_agreement_corrected
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedCorrectedBranchReindexSupply F)
    (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ((∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
            + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)) := by
  rw [resolved_regroupBranchSum_boundary_tail hCD, S.branchTail.branch_tail_cover]

end GaugeGeometry.QFT.Combinatorial
