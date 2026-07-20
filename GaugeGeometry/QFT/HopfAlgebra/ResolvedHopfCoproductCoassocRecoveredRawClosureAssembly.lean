import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionCount
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawClosureDemotion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCoreClosureAssembly

/-!
# R-6c-body-439 — the union assembly; `recovered_raw_mem` demoted; the canonical carrier-closure bundle (PROVED)

Four-hundred-and-thirty-ninth genuine-body step — the final assembly.  Body-437 was the last geometry; body-438 the last
arithmetic.  This body is bookkeeping and record assembly.

* `regionRawUnion_component_count_lt` — the component-level dispatch: a component of the raw recovered-outer union is a
  left / right / forest component (one `regionRawUnion` unfold + membership-level `Finset.mem_union`, so no `DecidableEq`
  diamond), each bounded `< count e G` by bodies 432 / 434 / 438.
* `regionRawUnion_count_lt` — the whole-union bound: if the residual preimage's raw count is `0`, ambient positivity
  (`e ∈ G.internalEdges`) closes it; otherwise the body-432 owner lemma pins the raw count to its single owner
  component's, which the dispatch bounds.
* `canonicalMultiStarCarrierClosureBundleSupply` — the culmination: given the measure leaves (`cd_nonempty` /
  `cd_positiveInternalEdges`) and the `Ids` gate, and a de-contraction value core over `W`, the entire
  `ResolvedMultiStarCarrierClosureBundleSupply` is DERIVED — `Closure := canonicalInnerRawCarrierClosureSupply` (body-427)
  and `recovered_raw_mem` from the count chain (bodies 439 → 431 → 429), with the ambient support / CD read off the outer
  block's own `W`-carrier membership `z.1.2` (body-426).

**Status.**  `ResolvedMultiStarCarrierClosureBundleSupply` is fully derived from the canonical supported carrier, the value
core, and the existing geometry / model inputs (measure leaves + `EdgeIdsUnique`).  This does NOT unconditionalize the
`Core`, the `DivergenceMeasure`, or the `Ids` gate — but the two carrier-membership fields `innerRaw_mem` (body-427) and
`recovered_raw_mem` (this body) are BOTH demoted to theorems.

Per the HALT/guards: forward-outer / identity / cover are not used anywhere in the closure line; everything stays in
`count`; no occurrence / `StarProm` / `Wiring`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO strict
`star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-439 — component-level dispatch.**  Each component of the raw recovered-outer union counts the residual
preimage strictly less than the ambient, by the left / right / forest exclusions. -/
theorem regionRawUnion_component_count_lt (F : ResolvedCanonicalStarFacts D)
    (hId : G.EdgeIdsUnique) (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (regionRawUnion M F z).elements)
    (he : quotientResidualEdgePreimage P z ∈ γ.internalEdges) :
    Multiset.count (quotientResidualEdgePreimage P z) γ.internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
  simp only [regionRawUnion, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hγ
  rcases hγ with (hl | hr) | hf
  · exact leftRegion_component_count_lt P z hl he
  · exact rightRegion_component_count_lt hId P z hr he
  · exact forestRegion_component_count_lt F hId P M z hf he

/-- **R-6c-body-439 — the whole-union count bound.**  The residual preimage's count in the raw recovered-outer union is
strictly below its ambient count: zero-count is closed by ambient positivity, positive-count by the owner lemma. -/
theorem regionRawUnion_count_lt (F : ResolvedCanonicalStarFacts D)
    (hId : G.EdgeIdsUnique) (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G) :
    Multiset.count (quotientResidualEdgePreimage P z) (regionRawUnion M F z).internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
  by_cases hzero : Multiset.count (quotientResidualEdgePreimage P z)
      (regionRawUnion M F z).internalEdges = 0
  · rw [hzero]
    exact Multiset.count_pos.mpr (ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges
      (quotientResidualEdgePreimage_mem_complement P z))
  · have hmem : quotientResidualEdgePreimage P z ∈ (regionRawUnion M F z).internalEdges :=
      Multiset.count_pos.mp (Nat.pos_of_ne_zero hzero)
    obtain ⟨γ, hγ, heγ⟩ := ResolvedAdmissibleSubgraph.mem_internalEdges.mp hmem
    rw [ResolvedAdmissibleSubgraph.count_internalEdges_eq_of_mem_component hγ heγ]
    exact regionRawUnion_component_count_lt F hId P M z hγ heγ

/-- **R-6c-body-439 ∎ — the canonical carrier-closure bundle, fully derived over `W`.**  Both carrier-membership fields
are theorems: `Closure` (body-427) and `recovered_raw_mem` (the count chain, ambient support / CD from the outer block's
own carrier membership `z.1.2`). -/
noncomputable def canonicalMultiStarCarrierClosureBundleSupply
    (Nne : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply G)
    (Ppos : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (hId : ∀ G : ResolvedFeynmanGraph, G.EdgeIdsUnique)
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalSupportedCarrierProperSupply.toData) :
    ResolvedMultiStarCarrierClosureBundleSupply Core canonicalStarFactsOfW where
  Closure := canonicalInnerRawCarrierClosureSupply Core
  recovered_raw_mem := fun {G} z =>
    regionRawUnion_mem_canonicalSupportedCarrier_of_complement
      (Nne G) (Ppos G)
      (Core.toDecontractionSupply (canonicalInnerRawCarrierClosureSupply Core))
      canonicalStarFactsOfW z
      (canonicalSupportedCarrier_ambientSupported z.1.2)
      (canonicalSupportedCarrier_ambientCD z.1.2)
      (regionRawUnion_complementEdges_card_pos_of_count_lt
        canonicalSupportedCarrierProperSupply.toCarrierProperProvider
        (Core.toDecontractionSupply (canonicalInnerRawCarrierClosureSupply Core))
        canonicalStarFactsOfW z
        (regionRawUnion_count_lt canonicalStarFactsOfW (hId G)
          canonicalSupportedCarrierProperSupply.toCarrierProperProvider
          (Core.toDecontractionSupply (canonicalInnerRawCarrierClosureSupply Core)) z))

end GaugeGeometry.QFT.Combinatorial
