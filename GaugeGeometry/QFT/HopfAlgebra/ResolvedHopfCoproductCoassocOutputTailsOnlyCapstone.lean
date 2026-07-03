import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchReindexCorrection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEmptyPivot

/-!
# R-6c-body-85 — the canonical tails-only OUTPUT capstone (Case A), with the coassoc-bridge flag

Eighty-fifth genuine-body step, fixing the OUTPUT form to Case A (`∅ ∉ carrier`, body-84): the split-choice
cover carries only the TAILS, and the two boundaries are cover-external primitive-outer terms.  This supersedes
the boundary-IN path (bodies 78/80–83) and records honestly a bridge tension the Case A form exposes.

## The canonical tails-only form

Under Case A the cover value is the base-outer LEFT tails:

```text
cover_tail_eq :  ∑ cover  =  ∑_A coassocLeftTail A  =  coassocLeftTail(forestSum)
```

(the base-outer fibering of `∑ cover`, body-76, provable via the split-term DEFINITION +
`coassocLeftTail_eq_splitChoiceTermSum` modulo `F`-completeness — fielded here).  Then the BRANCH regroup sum is
boundary + cover:

```text
regroupBranchSum = assoc(forestSum ⊗ 1)  +  ∑ cover
```

(`regroupBranch_boundary_tail`, PROVED via body-77's `resolved_regroupBranchSum_boundary_tail` + `cover_tail_eq`).
This is the clean Case A branch agreement — boundary external, cover the left tails.

## The bridge tension (flagged, honest)

The original σ-cover chain (body-38/54) proves `coassoc_gen` from `regroupImageSum = ∑ cover = regroupBranchSum`
— i.e. BOTH regroup sums equal the cover.  Under Case A that is IMPOSSIBLE: `∑ cover = coassocLeftTail(forestSum)`
(branch tails), but `regroupImageSum = 1 ⊗ forestSum + coassocRightTail(forestSum)` and `coassocRightTail(forestSum)
≠ coassocLeftTail(forestSum)` (they are `(id ⊗ Δᵣ)` vs `(Δᵣ ⊗ 1)` on `forestSum`, unequal since `forestSum` is not
`Δᵣ` of anything).  So `regroupImageSum ≠ ∑ cover` and `regroupBranchSum ≠ ∑ cover`; the cover does NOT bridge the
two regroup sums.

So Case A (`∅ ∉ carrier`) makes the tails-only cover UNABLE to prove `coassoc_gen` by the "both = ∑ cover" route.
The pivotal question is which holds:

* **(A1) the coassoc σ-cover uses an EXTENDED carrier including `∅`** (the trivial selected outer), so the
  boundaries ARE in the cover and `∑ cover = regroupImageSum = regroupBranchSum` (boundary-IN, body-78's form
  restored) — Case A applies to the coproduct carrier, but the coassoc reindex carrier differs; OR
* **(A2) `coassoc_gen` is proven DIRECTLY** as `regroupImageSum = regroupBranchSum` (the boundary + tail
  rearrangement), not via a common cover value.

This is the genuine remaining OUTPUT question, exposed by the `∅`-pivot.  The branch tails-only agreement below is
correct regardless (it is one half of either route); the IMAGE side / bridge awaits the (A1)/(A2) decision.

Per the HALT, `cover_tail_eq` is not proved (F-completeness); no boundary-IN file is used except as superseded
documentation; the branch agreement is proved; the bridge tension is flagged, not forced.

Landed:

* `ResolvedOutputTailsCoverSupply F` — the Case A tails cover (`cover_tail_eq`);
* `.regroupBranch_boundary_tail` — `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑ cover` (PROVED).

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

/-- **R-6c-body-85 — the Case A tails-only OUTPUT cover.**  Under `∅ ∉ carrier` (body-84) the split-choice cover
is the base-outer LEFT tails `∑_A coassocLeftTail A` (the boundaries are cover-external, body-84). -/
structure ResolvedOutputTailsCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- `∑ cover = ∑_A coassocLeftTail A` (the base-outer tails). -/
  cover_tail_eq :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-85 — the Case A branch agreement.**  `regroupBranchSum = assoc(forestSum ⊗ 1) + ∑ cover` — the
primitive-outer boundary (external) plus the tails cover. -/
theorem ResolvedOutputTailsCoverSupply.regroupBranch_boundary_tail
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedOutputTailsCoverSupply F)
    (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ((∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
            + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)) := by
  rw [resolved_regroupBranchSum_boundary_tail hCD, S.cover_tail_eq]

end GaugeGeometry.QFT.Combinatorial
