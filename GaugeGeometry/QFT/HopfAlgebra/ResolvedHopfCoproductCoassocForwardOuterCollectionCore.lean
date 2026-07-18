import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestTag

/-!
# R-6c-body-334 — forward-outer collection core (PROVED, carrier/choice-free)

Three-hundred-and-thirty-fourth genuine-body step — the mathematical CORE of `forward_outer_value` at orphans, proved
carrier-free and choice-free: the union of the promoted inner forests over the star-touching quotient components equals
the represented outer components, and with the left residual exhausts `z.1.1.elements`.  This is the D5+M3 payoff — NO
floor-297, NO singleton collapse.  Choice alignment (`leftOf`/`promotedOf` of an actual split choice = these) is the only
remaining step (Front-2 adjacent).

## Banked here

* `promotedTouchedUnion z` — `⋃ δ ∈ forestDomain z, (promote (parent δ) (innerIdx δ).1).elements`.
* `promote_parent_innerIdx_elements` — M3 re-stated in `parent`/`innerIdx` terms: each promoted inner forest's
  components are `touchedOuterComponents z δ.1`.
* `promotedTouchedUnion_eq_represented` — `promotedTouchedUnion z = representedForestTouched z` (M3 +
  `representedForestTouched_eq_biUnion`, body-323).
* `leftResidual_union_promotedTouched` — `leftResidualTouched z ∪ promotedTouchedUnion z = z.1.1.elements` (D5
  `touched_coverage`, body-323).

Given an actual split choice `q` with `leftOf q .elements = leftResidualTouched z` and
`promotedOf q .elements = promotedTouchedUnion z`, `selectedOuterRawOf q .elements = z.1.1.elements` is immediate.

## Remaining gates (NOT collection-level — recorded, not proved)

`recovered_raw_mem` (recovered outer ∈ D.carrier G); right/left/forest cross-disjointness; the choice's `inl false` on
right components / `inr (innerIdx δ)` on parents; the D4-uniqueness `forestTag` alignment; and `forestTag_agrees` (the
forward-image occurrence identity, Front-2 confluent).

Per the HALT: only the carrier/choice-FREE collection core is proved; this is NOT "full forward_outer" — CHOICE ALIGNMENT
remains; no `recovered_raw_mem`, no cross-disjointness, no occurrence/V.Remnant; no facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-334 — M3 in `parent`/`innerIdx` terms.** -/
theorem promote_parent_innerIdx_elements (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    (ResolvedAdmissibleSubgraph.promote (M.parent z δ) (M.innerIdx z δ).1).elements
      = touchedOuterComponents z δ.1 :=
  promote_innerRaw_elements z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)

/-- **R-6c-body-334 — the union of the promoted inner forests.** -/
noncomputable def promotedTouchedUnion (z : ForestBlockCodType D G) :
    Finset (ResolvedFeynmanSubgraph G) :=
  (forestDomain z).attach.biUnion (fun δ =>
    (ResolvedAdmissibleSubgraph.promote (M.parent z δ) (M.innerIdx z δ).1).elements)

/-- **R-6c-body-334 — the promoted union is the represented outer components** (M3 + D5-biUnion). -/
theorem promotedTouchedUnion_eq_represented (z : ForestBlockCodType D G) :
    M.promotedTouchedUnion z = representedForestTouched z := by
  rw [representedForestTouched_eq_biUnion]
  ext x
  simp only [promotedTouchedUnion, Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists,
    M.promote_parent_innerIdx_elements, exists_prop]

/-- **R-6c-body-334 — the forward-outer collection core: left residual ∪ promoted union = the outer components.** -/
theorem leftResidual_union_promotedTouched (z : ForestBlockCodType D G) :
    leftResidualTouched z ∪ M.promotedTouchedUnion z = z.1.1.elements := by
  rw [M.promotedTouchedUnion_eq_represented]
  exact touched_coverage z

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
