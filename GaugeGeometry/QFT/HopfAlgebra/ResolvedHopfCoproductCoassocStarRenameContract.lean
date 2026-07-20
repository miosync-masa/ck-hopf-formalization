import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCorrectingPerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawClosureDemotion

/-!
# R-6c-body-451 — the star-rename contraction equality (from the two point laws only) (PROVED)

Four-hundred-and-fifty-first genuine-body step — the layer that turns a correcting permutation `ρ` (fixing the ambient,
relabeling stars) into a CONTRACTION-GRAPH equality, with NO freshness / injectivity (those were spent building `ρ`).
Only the two point laws are consumed: `ρ` fixes `H.vertices`, and `ρ (s₁ γ) = s₂ γ`.

* `resolvedStarRename_retargetVertex` — `ρ (A.retargetVertex s₁ v) = A.retargetVertex s₂ v` (component-star law inside
  `A`, ambient fixing outside);
* `resolvedStarRename_contractWithStars` — `A.contractWithStars s₂ = (A.contractWithStars s₁).mapPerm ρ` (three fields:
  vertices by fixing + star image, internal edges / external legs by the retarget lemma with ambient endpoint support);
* `innerStarCorrected_contract_eq` — the inner instantiation: `innerRaw.contractWithStars touchedInnerStarTotal =
  (innerRaw.contractWithStars hardcodedStar).mapPerm innerStarCorrectingPerm`, support from body-427
  `resolvedAmbientSupported_of_subgraphGraph`.

The right-hand side is the corrected `contractWithStars hardcodedStar` relabeled — the seed for the corrected remnant
round-trip; the left-hand side is the explicit touched star map the body-353/356 section returns to `δ`.  So strict
`innerStar_agrees_raw` is replaced by this `mapPerm ρ` equality.

Per the HALT/guards: no freshness / injectivity is required here (consumed in `ρ`); `innerStar_agrees_raw` / strict
`StarProm` are NOT used; `ρ` fixes only the ambient; occurrence / `OccRaw` / `Concrete` / remnant round-trip are body-452;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

variable {H : ResolvedFeynmanGraph}

/-- **R-6c-body-451 — the retarget-vertex transport from the two point laws.** -/
theorem resolvedStarRename_retargetVertex (A : ResolvedAdmissibleSubgraph H)
    (s₁ s₂ : ResolvedFeynmanSubgraph H → VertexId) (ρ : Equiv.Perm VertexId)
    (hfix : ∀ v ∈ H.vertices, ρ v = v)
    (hstar : ∀ γ ∈ A.elements, ρ (s₁ γ) = s₂ γ)
    {v : VertexId} (hv : v ∈ H.vertices) :
    ρ (A.retargetVertex s₁ v) = A.retargetVertex s₂ v := by
  by_cases hvA : v ∈ A.vertices
  · rw [retargetVertex_eq_star_of_mem_element A s₁ (A.componentAt_mem hvA) (A.componentAt_vertex_mem hvA),
      retargetVertex_eq_star_of_mem_element A s₂ (A.componentAt_mem hvA) (A.componentAt_vertex_mem hvA)]
    exact hstar (A.componentAt hvA) (A.componentAt_mem hvA)
  · rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem A s₁ hvA,
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem A s₂ hvA]
    exact hfix v hv

/-- **R-6c-body-451 — the contraction-graph equality from the two point laws.** -/
theorem resolvedStarRename_contractWithStars (A : ResolvedAdmissibleSubgraph H)
    (s₁ s₂ : ResolvedFeynmanSubgraph H → VertexId) (ρ : Equiv.Perm VertexId)
    (hE : AmbientEdgesSupported H) (hL : AmbientLegsSupported H)
    (hfix : ∀ v ∈ H.vertices, ρ v = v)
    (hstar : ∀ γ ∈ A.elements, ρ (s₁ γ) = s₂ γ) :
    A.contractWithStars s₂ = (A.contractWithStars s₁).mapPerm ρ := by
  have hv : (H.vertices \ A.vertices) ∪ A.starVertices s₂
      = ((H.vertices \ A.vertices) ∪ A.starVertices s₁).image ρ := by
    have hsurv : (H.vertices \ A.vertices).image ρ = H.vertices \ A.vertices := by
      ext w; simp only [Finset.mem_image]
      constructor
      · rintro ⟨u, hu, rfl⟩; rwa [hfix u (Finset.mem_sdiff.mp hu).1]
      · intro hw; exact ⟨w, hw, hfix w (Finset.mem_sdiff.mp hw).1⟩
    have hstarim : (A.starVertices s₁).image ρ = A.starVertices s₂ := by
      unfold ResolvedAdmissibleSubgraph.starVertices
      rw [Finset.image_image]
      exact Finset.image_congr (fun γ hγ => hstar γ hγ)
    rw [Finset.image_union, hsurv, hstarim]
  have hi : A.complementEdges.map (A.retargetEdge s₂)
      = (A.complementEdges.map (A.retargetEdge s₁)).map (ResolvedFeynmanEdge.map ρ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun e he => ?_)
    have heH : e ∈ H.internalEdges := Multiset.mem_of_le tsub_le_self he
    obtain ⟨hs, ht⟩ := hE e heH
    show A.retargetEdge s₂ e = ResolvedFeynmanEdge.map ρ (A.retargetEdge s₁ e)
    simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.map,
      ResolvedFeynmanEdge.retarget]
    rw [resolvedStarRename_retargetVertex A s₁ s₂ ρ hfix hstar hs,
      resolvedStarRename_retargetVertex A s₁ s₂ ρ hfix hstar ht]
  have hlegs : H.externalLegs.map (A.retargetExternalLeg s₂)
      = (H.externalLegs.map (A.retargetExternalLeg s₁)).map (ResolvedExternalLeg.map ρ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun ℓ hℓ => ?_)
    have ha := hL ℓ hℓ
    show A.retargetExternalLeg s₂ ℓ = ResolvedExternalLeg.map ρ (A.retargetExternalLeg s₁ ℓ)
    simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.map,
      ResolvedExternalLeg.retarget]
    rw [resolvedStarRename_retargetVertex A s₁ s₂ ρ hfix hstar ha]
  exact congr (congr (congrArg ResolvedFeynmanGraph.mk hv) hi) hlegs

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D) (M : ResolvedMultiStarDecontractionSupply D)
  (z : ForestBlockCodType D G)
  (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})

include Fstar

/-- **R-6c-body-451 ∎ — the inner corrected contraction equality.**  `innerRaw`'s touched-star contraction equals its
hardcoded-star contraction relabeled by the inner correcting permutation. -/
theorem innerStarCorrected_contract_eq :
    (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
        (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
      = ((innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)).contractWithStars
          (D.starOf (M.parent z δ).toResolvedFeynmanGraph
            (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))).mapPerm
        (innerStarCorrectingPerm Fstar M z δ) :=
  resolvedStarRename_contractWithStars (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
    (D.starOf (M.parent z δ).toResolvedFeynmanGraph (innerRaw z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)))
    (touchedInnerStarTotal z δ.1 (M.legLift z δ) (M.hE z) (M.hL z))
    (innerStarCorrectingPerm Fstar M z δ)
    (resolvedAmbientSupported_of_subgraphGraph (M.parent z δ)).1
    (resolvedAmbientSupported_of_subgraphGraph (M.parent z δ)).2
    (fun _ hv => innerStarCorrectingPerm_on_parent_vertices Fstar M z δ hv)
    (fun _ hγ => innerStarCorrectingPerm_on_inner_stars Fstar M z δ hγ)

end GaugeGeometry.QFT.Combinatorial
