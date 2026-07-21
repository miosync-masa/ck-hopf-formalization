import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceInversionScope
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSplitDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemnantCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaValueForwardLayer
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromoteGen

/-!
# R-6c-body-503 — faithful alpha OccurrenceInversion canonical inhabitant (PROVED)

Five-hundred-and-third genuine-body step — the canonical construction of body-502's faithful socket
`ResolvedForwardForestOccurrenceInversionAlphaValueSupply`, WITHOUT the legacy `∀ s` `OccRaw`.  The core insight: `δ.2`
already knows which corrected-remnant occurrence `δ` is; body-485's parent uniqueness pins that occurrence to `o`, and
body-502's promote equality is stripped by `promote_injective`.  No new geometry.

## Step 1 — the promote cancellation + `ForestIdx` `HEq` lift (generic)

* `promote_elements_cancel` — from `hpar : P = γ` and `(promote P A).elements = (promote γ B).elements`, the promoted
  images cancel (`ResolvedFeynmanSubgraph.promote_injective` + `Finset.image_injective`) to `HEq A.elements B.elements`.
* `heq_forestIdx_of_graph_eq` — from `H₁ = H₂` and `HEq B₁.1.elements B₂.1.elements`, lift to `HEq B₁ B₂` (the `.elements`
  determine the admissible subgraph via `ext_elements`; the carrier proof is irrelevant).

## Step 2/3 — the canonical inhabitant

`canonicalForwardForestOccurrenceInversionAlphaValueSupply` builds the socket over the canonical `M` / `Fmem` (body-496) /
`V` (body-482).  On the field: `δ.2` → `forestDomain_value_mem_alpha` (body-497 canonical `Split`) →
`remnantForest_elements` image → occurrence `o'` with `HEq (remnantComponent q.1 o') δ.1`; body-485 pins
`M.parent (fwd q) δ = o'.γ.1`; with `hparent` and `eq_of_parent_eq` (body-464), `o' = o`; body-502's promote equality +
`promote_elements_cancel` gives the element `HEq`, lifted to `HEq (M.innerIdx (fwd q) δ) o.B` once.

Per the HALT/guards: nothing is back-computed from body-495 `remnant_mem` / body-492 quotient `HEq` / coassoc; body-489's
round-trip is NOT used (it takes `hidx` as input — circular); the legacy `∀ s` `OccRaw` is NOT canonically inhabited (it
stays a valid conditional); no `promote`-equality is `simp`ed to a full-forest equality without cancellation; `quot_eq` /
`legComplete` are NOT entered; the body-495 closed theorem is NOT edited; strict `StarProm` / `InnerStarRaw` stay ZERO; NO
unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton
/ floor-297.  Alpha consumer migration is body-504.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## Step 1 — promote cancellation + `ForestIdx` `HEq` lift -/

/-- **R-6c-body-503 ∎ — the promote cancellation.**  Equal promoted collections, over equal parents, have equal source
collections (`promote_injective` cancels the image). -/
theorem promote_elements_cancel {P γ : ResolvedFeynmanSubgraph G} (hpar : P = γ)
    {A : ResolvedAdmissibleSubgraph P.toResolvedFeynmanGraph}
    {B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph}
    (hprom : (ResolvedAdmissibleSubgraph.promote P A).elements
      = (ResolvedAdmissibleSubgraph.promote γ B).elements) :
    HEq A.elements B.elements := by
  cases hpar
  apply heq_of_eq
  have h2 := hprom
  rw [ResolvedAdmissibleSubgraph.promote_elements, ResolvedAdmissibleSubgraph.promote_elements] at h2
  refine Finset.image_injective P.promote_injective ?_
  convert h2 using 2

/-- **R-6c-body-503 ∎ — the `ForestIdx` `HEq` lift from a graph equality.**  Two carrier `ForestIdx`s over equal graphs
with equal component sets are `HEq`. -/
theorem heq_forestIdx_of_graph_eq {H₁ H₂ : ResolvedFeynmanGraph}
    (B₁ : (D.supply H₁).ForestIdx) (B₂ : (D.supply H₂).ForestIdx)
    (hgraph : H₁ = H₂) (helem : HEq B₁.1.elements B₂.1.elements) :
    HEq B₁ B₂ := by
  cases hgraph
  exact heq_of_eq (Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements (eq_of_heq helem)))

/-! ## Step 2/3 — the canonical faithful socket inhabitant -/

/-- **R-6c-body-503 ∎ — the canonical faithful forward occurrence-inversion socket, CONSTRUCTED.**  Over the canonical
`M` (`ValueGeometry`'s de-contraction), `Fmem` (body-496), and `V` (body-482), WITHOUT the legacy `∀ s` `OccRaw`: `δ.2`
recovers the corrected-remnant occurrence, body-485 pins the parent, and body-502's promote equality is stripped by
`promote_elements_cancel` + lifted to the `ForestIdx` `HEq`. -/
noncomputable def canonicalForwardForestOccurrenceInversionAlphaValueSupply
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedForwardForestOccurrenceInversionAlphaValueSupply
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue where
  occurrence_inner_idx_alpha := fun {G} q δ o hparent => by
    have hmem : δ.1 ∈ (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantForest q.1).elements :=
      ((canonicalUniqueAlphaValueQuotientRegionSplitSupply VBuild E).forestDomain_value_mem_alpha q δ.1).mp δ.2
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hmem
    obtain ⟨γ', -, hγ'⟩ := Finset.mem_image.mp hmem
    set o' := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ' with ho'
    have hδ' : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o') δ.1 :=
      heq_of_eq hγ'
    have hpar' : (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
          (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore)).parent
          (fwdMapFilteredAlphaValue (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
            VBuild.toCanonicalFilteredValue q) δ = o'.γ.1 :=
      parent_remnantComponent_of_multiStar_alpha_geometry VBuild ValueGeometry q o' δ hδ'
    have hoeq : o = o' := ForestChoiceOccurrence.eq_of_parent_eq (hparent.symm.trans hpar')
    have hprom := promoted_innerIdx_elements_eq_promoted_B_alpha
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
      VBuild q o' δ hδ'
    have helem := promote_elements_cancel hpar' hprom
    exact hoeq.symm ▸ heq_forestIdx_of_graph_eq _ o'.B
      (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hpar') helem

end GaugeGeometry.QFT.Combinatorial
