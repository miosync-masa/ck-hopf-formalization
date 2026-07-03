import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverWiringCheck
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchFiberBody

/-!
# R-6c-body-76 — corrected BRANCH wiring check: the branch cover is tails-only (boundary cover-external)

Seventy-sixth genuine-body step, the BRANCH mirror of body-75.  Body-75 found the IMAGE cover matches body-54's
`outer_image_cover` via the boundary-IN summand form.  The BRANCH is DIFFERENT: its base-outer fibering lands on
the tail alone, and body-54's `outer_branch_cover` (boundary-IN) is NOT wiring-compatible — the branch boundary
is cover-external (body-70).

## The branch fibering is free (proved)

Exactly like body-73's IMAGE fibering: `resolvedBranchForestFiber F q = q.1.1` (the base outer) is always a
carrier element (`Finset.mem_attach`), so `Finset.sum_fiberwise_of_maps_to` gives, unconditionally,

```text
∑_A ((∑ q ∈ F.forestCarrier with q.1.1 = A, splitTerm q.1) + (∑ mixed)) = ∑ cover
```

(`resolved_branch_cover_fibered`).

## The base-outer fiber is the TAIL, not the summand

Each base-outer fiber sums to `coassocLeftTail (leftTerm A ⊗ rightTerm A)`: `splitTerm s = assoc((∏
localChoiceTerm) ⊗ rightTerm s.1)`, so `∑_{s.1 = A} splitTerm = assoc((∑ ∏ localChoiceTerm) ⊗ rightTerm A) =
assoc(Δᵣ(leftTerm A) ⊗ rightTerm A) = coassocLeftTail A` (body-61's `coassocLeftTail_eq_splitChoiceTermSum`,
modulo `F`-completeness of the base-`A` choices).  So the fiber is the TAIL `coassocLeftTail A` — NOT the branch
summand `assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail A`.

The boundary `assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)` (inner-third factor `1`) is NOT a split term (body-64/70):
every split term has `rightTerm A` in that slot.  So it CANNOT appear in any base-outer fiber.

## The wiring decision: BRANCH ≠ IMAGE

Summing the tail fibers gives `∑ cover = ∑_A coassocLeftTail A` (`ResolvedBranchFiberTailSupply.branch_tail_cover`)
— tails only.  But body-54's `outer_branch_cover` requires `∑ cover = ∑_A (assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)
+ coassocLeftTail A) = assoc(forestSum ⊗ 1) + ∑_A coassocLeftTail A` (boundary IN).  They differ by the branch
boundary `assoc(forestSum ⊗ 1)`.

So — unlike IMAGE (body-75, where the boundary IS the `∅`-fiber and distributes into the summand fibers) — the
BRANCH boundary is cover-EXTERNAL and cannot be a base-outer fiber.  **body-54's `outer_branch_cover` is the wrong
form for the branch**; the wiring-compatible branch primitive is the TAILS-ONLY `fiber_eq_tail` (per-`A`
`coassocLeftTail A`), and the branch reindex must route `assoc(forestSum ⊗ 1)` SEPARATELY (matching body-70's
cover-external classification): `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑ cover`.  The branch adopts the
full-sum boundary+tail shape (body-69), NOT the per-`A` summand shape.

This surfaces a deeper coassoc bookkeeping (the SAME `∑ cover` is `regroupImageSum` on the image side but only
the tail part of `regroupBranchSum` on the branch side — the branch boundary being the extra primitive-outer
term); settling that is the branch reindex correction, not this check.

Per the HALT, the branch cover body is not proved (`fiber_eq_tail` is fielded); the fibering is proved; only the
wiring form is decided.

Landed:

* `resolved_branch_cover_fibered` — the branch cover = the sum of its base-outer fibers (PROVED, unconditional);
* `ResolvedBranchFiberTailSupply F` — the tails-only per-`A` branch leaf (`fiber_eq_tail`);
* `.branch_tail_cover` — `∑ cover = ∑_A coassocLeftTail A` (the corrected, tails-only branch cover).

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

/-- **R-6c-body-76 — the BRANCH cover fibers freely by base outer.**  The split-choice cover equals the sum over
base outers `A` of its `s.1 = A` fibers — unconditionally (`s.1` is always a carrier element, `mem_attach`).  The
branch analogue of body-73. -/
theorem resolved_branch_cover_fibered (F : ResolvedCoassocGrandFullSupply D G) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((∑ q ∈ F.forestCarrier with resolvedBranchForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedBranchMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) := by
  have hf : ∀ q ∈ F.forestCarrier, resolvedBranchForestFiber F q ∈ (D.supply G).forestCarrier :=
    fun q _ => Finset.mem_attach _ _
  have hm : ∀ q ∈ F.mixedCarrier, resolvedBranchMixedFiber F q ∈ (D.supply G).forestCarrier :=
    fun q _ => Finset.mem_attach _ _
  rw [Finset.sum_add_distrib,
    Finset.sum_fiberwise_of_maps_to hf (fun q => D.resolvedSplitChoiceTerm q.1),
    Finset.sum_fiberwise_of_maps_to hm (fun q => D.resolvedSplitChoiceTerm q.1)]

/-- **R-6c-body-76 — the tails-only per-`A` BRANCH leaf.**  Each base-outer fiber sums to the LEFT tail
`coassocLeftTail A` (NOT the branch summand — the boundary `assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)` is
cover-external, body-64/70).  This is the wiring-compatible branch primitive. -/
structure ResolvedBranchFiberTailSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The `s.1 = A` base-outer fiber sum = the LEFT tail `coassocLeftTail A`. -/
  fiber_eq_tail : ∀ A ∈ (D.supply G).forestCarrier,
    (∑ q ∈ F.forestCarrier with resolvedBranchForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedBranchMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)
      = D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-76 — the corrected (tails-only) branch cover.**  Body-76's free fibering plus `fiber_eq_tail`:
`∑ cover = ∑_A coassocLeftTail A` — the branch cover is the LEFT-tail sum, with the boundary `assoc(forestSum ⊗
1)` cover-external (routed separately in the corrected reindex). -/
theorem ResolvedBranchFiberTailSupply.branch_tail_cover
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedBranchFiberTailSupply F) :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [← resolved_branch_cover_fibered F]
  exact Finset.sum_congr rfl (fun A hA => S.fiber_eq_tail A hA)

end GaugeGeometry.QFT.Combinatorial
