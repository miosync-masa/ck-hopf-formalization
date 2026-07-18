import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractVertexEq

/-!
# R-6c-body-357 — hardcoded-star swap: `contractedSourceGraph`'s star = the explicit star (PROVED)

Three-hundred-and-fifty-seventh genuine-body step — the star-map swap bridging body-353/356's explicit-star
re-contract section to the remnant's hardcoded star map.  `contractedSourceGraph o` uses the hardcoded
`D.starOf (parent graph) (innerIdx)`; on the inner-forest components this AGREES with the explicit
`touchedInnerStarTotal` (body-349's `innerStar_agrees`, via `innerSource`), so — `contractWithStars` reads the
star map only on components (member-congruence) — the hardcoded re-contract has `δ`'s three data.

Landed axiom-clean:

* `retargetVertex_congr` / `retargetEdge_congr` / `retargetExternalLeg_congr` — the star map is used only on `A`'s
  components, so agreement there suffices;
* `contractWithStars_vertices_congr` / `_internalEdges_congr` / `_externalLegs_congr` — `contractWithStars`
  respects star-map agreement on components;
* `hardcodedStar_eq_touchedInnerStarTotal` — the two star maps agree on `innerRaw.elements`;
* `recontract_hardcoded_vertices` / `_internalEdges` / `_externalLegs` — the HARDCODED re-contract's three data
  are `δ`'s (compose the congruence + body-353/356).

Per the HALT: only the star swap + the hardcoded-star three data are proved; the occurrence transport
(`o.B = innerIdx`, body-343), `houter` (body-341), and `subgraph_heq_of_data` (body-346) assembling the remnant
component `HEq` are the next body; the full `V.Remnant` provider (with its extra fields) is NOT claimed complete
— only the component construction/round-trip; no forward quotient / global forward round-trip.  No facade, no
flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-357 — `retargetVertex` respects star agreement on components.** -/
theorem retargetVertex_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) (v : VertexId) :
    A.retargetVertex starOf₁ v = A.retargetVertex starOf₂ v := by
  by_cases hv : v ∈ A.vertices
  · rw [ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem A hv,
      ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem A hv]
    exact hstar _ (A.componentAt_mem hv)
  · rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv]

/-- **R-6c-body-357 — `retargetEdge` respects star agreement on components.** -/
theorem retargetEdge_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) (e : ResolvedFeynmanEdge) :
    A.retargetEdge starOf₁ e = A.retargetEdge starOf₂ e := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [retargetVertex_congr A starOf₁ starOf₂ hstar, retargetVertex_congr A starOf₁ starOf₂ hstar]

/-- **R-6c-body-357 — `retargetExternalLeg` respects star agreement on components.** -/
theorem retargetExternalLeg_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) (ℓ : ResolvedExternalLeg) :
    A.retargetExternalLeg starOf₁ ℓ = A.retargetExternalLeg starOf₂ ℓ := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
  rw [retargetVertex_congr A starOf₁ starOf₂ hstar]

/-- **R-6c-body-357 — `contractWithStars` vertices respect star agreement on components.** -/
theorem contractWithStars_vertices_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) :
    (A.contractWithStars starOf₁).vertices = (A.contractWithStars starOf₂).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  congr 1
  rw [ResolvedAdmissibleSubgraph.starVertices, ResolvedAdmissibleSubgraph.starVertices]
  exact Finset.image_congr (fun η hη => hstar η hη)

/-- **R-6c-body-357 — `contractWithStars` internal edges respect star agreement on components.** -/
theorem contractWithStars_internalEdges_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) :
    (A.contractWithStars starOf₁).internalEdges = (A.contractWithStars starOf₂).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact Multiset.map_congr rfl (fun e _ => retargetEdge_congr A starOf₁ starOf₂ hstar e)

/-- **R-6c-body-357 — `contractWithStars` external legs respect star agreement on components.** -/
theorem contractWithStars_externalLegs_congr (A : ResolvedAdmissibleSubgraph G)
    (starOf₁ starOf₂ : ResolvedFeynmanSubgraph G → VertexId)
    (hstar : ∀ η ∈ A.elements, starOf₁ η = starOf₂ η) :
    (A.contractWithStars starOf₁).externalLegs = (A.contractWithStars starOf₂).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  exact Multiset.map_congr rfl (fun ℓ _ => retargetExternalLeg_congr A starOf₁ starOf₂ hstar ℓ)

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)

/-- **R-6c-body-357 — the hardcoded star equals the explicit star on the inner forest.** -/
theorem hardcodedStar_eq_touchedInnerStarTotal
    (S : ResolvedInnerStarCoherenceSupply M) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (B : ResolvedFeynmanSubgraph (M.parent z δ).toResolvedFeynmanGraph)
    (hB : B ∈ (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).elements) :
    D.starOf (M.parent z δ).toResolvedFeynmanGraph (M.innerIdx z δ).1 B
      = touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B := by
  rw [touchedInnerStarTotal_of_mem z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) B hB, touchedInnerStar]
  have hia := S.innerStar_agrees z δ (innerSource z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩)
  rw [innerSource_spec z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) ⟨B, hB⟩] at hia
  exact hia

/-- **R-6c-body-357 — the hardcoded re-contract's vertices are `δ`'s.** -/
theorem recontract_hardcoded_vertices (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedInnerStarCoherenceSupply M) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    ((M.innerIdx z δ).1.contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph (M.innerIdx z δ).1)).vertices = δ.1.vertices := by
  rw [contractWithStars_vertices_congr (M.innerIdx z δ).1 _
      (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
      (fun B hB => M.hardcodedStar_eq_touchedInnerStarTotal S z δ B hB)]
  exact recontract_innerRaw_vertices z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) Fstar hConn hPos

/-- **R-6c-body-357 — the hardcoded re-contract's internal edges are `δ`'s.** -/
theorem recontract_hardcoded_internalEdges
    (S : ResolvedInnerStarCoherenceSupply M) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    ((M.innerIdx z δ).1.contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph (M.innerIdx z δ).1)).internalEdges
      = δ.1.internalEdges := by
  rw [contractWithStars_internalEdges_congr (M.innerIdx z δ).1 _
      (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
      (fun B hB => M.hardcodedStar_eq_touchedInnerStarTotal S z δ B hB)]
  exact recontract_innerRaw_internalEdges z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)

/-- **R-6c-body-357 — the hardcoded re-contract's external legs are `δ`'s.** -/
theorem recontract_hardcoded_externalLegs
    (S : ResolvedInnerStarCoherenceSupply M) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    ((M.innerIdx z δ).1.contractWithStars
        (D.starOf (M.parent z δ).toResolvedFeynmanGraph (M.innerIdx z δ).1)).externalLegs
      = δ.1.externalLegs := by
  rw [contractWithStars_externalLegs_congr (M.innerIdx z δ).1 _
      (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
      (fun B hB => M.hardcodedStar_eq_touchedInnerStarTotal S z δ B hB)]
  exact recontract_innerRaw_externalLegs z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
