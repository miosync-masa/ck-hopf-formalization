import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermStars
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientSupportScopeRepair

/-!
# R-6c-body-410 — the correcting permutation's contraction geometry (PROVED, safe-stop)

Four-hundred-and-tenth genuine-body step — the mixed `σ`/`τ` contraction geometry.  Body-408/409 built the correcting
permutation `τ := correctingPerm Fstar σ A` with its two action laws (`τ = σ` on ambient vertices,
`τ (oldStar γ) = newStar (γ.mapPerm σ)`).  This body promotes those two point laws into the full graph equality

    (A.mapPerm σ).contractWithStars newStar  =  (A.contractWithStars oldStar).mapPerm τ ,

the load-bearing datum behind body-406's `ResolvedContractTwiceClassData` (`new = old.mapPerm τ`).

The existing `mapPerm_contractWithStars` cannot supply this: it needs the strict `hstar : starOf' (γ.mapPerm σ) = σ
(starOf γ)`, i.e. strict star-equivariance, which body-403 proved INCONSISTENT with `starOf_fresh`.  The correcting
permutation `τ` is exactly the fix — the ambient is still relabeled by `σ` (giving `G.mapPerm σ`, `A.mapPerm σ`), but the
contraction result is transported by `τ`, so the star components move by the on-stars law and the survivors by the
on-vertices law.

* `correctingPerm_retargetVertex` — `(A.mapPerm σ).retargetVertex newStar (σ v) = τ (A.retargetVertex oldStar v)`
  (in-component branch = on-stars, off-component branch = on-vertices, needs `v ∈ G.vertices`);
* `correctingPerm_retargetEdge` / `correctingPerm_retargetExternalLeg` — the endpoint-supported edge/leg versions;
* `correctingPerm_starVertices` — `(A.mapPerm σ).starVertices newStar = (A.starVertices oldStar).image τ`;
* `correctingPerm_contractWithStars` — the graph equality (endpoint support supplied by `AmbientEdgesSupported` /
  `AmbientLegsSupported`).

Per the safe stop: the `ResolvedContractTwiceClassData` / `ResolvedRightTermCorrectingPermSupply` assembly is the NEXT
body (it is now a pure `congrArg` off this graph equality); `D.rightTerm_mapPerm` is NOT edited; the raw canonical carrier
builder is untouched.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
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

/-- **R-6c-body-410 — mixed vertex-retarget law.**  Relabeling the ambient by `σ` and retargeting through the relabeled
forest with the relabeled stars equals retargeting through the original and transporting by `τ`.  In-component: the
on-stars law; off-component: the on-vertices law (hence `v ∈ G.vertices`). -/
theorem correctingPerm_retargetVertex (Fstar : ResolvedCanonicalStarFacts D) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) {v : VertexId} (hvG : v ∈ G.vertices) :
    (A.mapPerm σ).retargetVertex (D.starOf (G.mapPerm σ) (A.mapPerm σ)) (σ v)
      = correctingPerm Fstar σ A (A.retargetVertex (D.starOf G A) v) := by
  by_cases hv : v ∈ A.vertices
  · have hσv : σ v ∈ (A.mapPerm σ).vertices := by
      rw [ResolvedAdmissibleSubgraph.mapPerm_vertices]; exact Finset.mem_image_of_mem σ hv
    have hcomp : (A.mapPerm σ).componentAt hσv = (A.componentAt hv).mapPerm σ := by
      refine ResolvedAdmissibleSubgraph.componentAt_eq_of_mem _ hσv ?_ ?_
      · simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image]
        exact ⟨A.componentAt hv, A.componentAt_mem hv, rfl⟩
      · rw [ResolvedFeynmanSubgraph.mapPerm_vertices]
        exact Finset.mem_image_of_mem σ (A.componentAt_vertex_mem hv)
    rw [ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hσv,
        ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv]
    show D.starOf (G.mapPerm σ) (A.mapPerm σ) ((A.mapPerm σ).componentAt hσv)
      = correctingPerm Fstar σ A (D.starOf G A (A.componentAt hv))
    rw [hcomp, correctingPerm_on_stars Fstar σ A (A.componentAt_mem hv)]
  · have hσv : σ v ∉ (A.mapPerm σ).vertices := by
      rw [ResolvedAdmissibleSubgraph.mapPerm_vertices]
      intro hc
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hc
      exact hv (σ.injective hwv ▸ hw)
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hσv,
        ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
        correctingPerm_on_vertices Fstar σ A hvG]

/-- **R-6c-body-410 — mixed internal-edge-retarget law** (endpoints in `G.vertices`). -/
theorem correctingPerm_retargetEdge (Fstar : ResolvedCanonicalStarFacts D) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) (e : ResolvedFeynmanEdge)
    (hsrc : e.source ∈ G.vertices) (htgt : e.target ∈ G.vertices) :
    (A.mapPerm σ).retargetEdge (D.starOf (G.mapPerm σ) (A.mapPerm σ)) (ResolvedFeynmanEdge.map σ e)
      = ResolvedFeynmanEdge.map (correctingPerm Fstar σ A) (A.retargetEdge (D.starOf G A) e) := by
  cases e with | mk eid es et esec =>
  simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.map,
    ResolvedFeynmanEdge.retarget, correctingPerm_retargetVertex Fstar σ A hsrc,
    correctingPerm_retargetVertex Fstar σ A htgt]

/-- **R-6c-body-410 — mixed external-leg-retarget law** (attachment in `G.vertices`). -/
theorem correctingPerm_retargetExternalLeg (Fstar : ResolvedCanonicalStarFacts D) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) (ℓ : ResolvedExternalLeg)
    (hℓ : ℓ.attachedTo ∈ G.vertices) :
    (A.mapPerm σ).retargetExternalLeg (D.starOf (G.mapPerm σ) (A.mapPerm σ)) (ResolvedExternalLeg.map σ ℓ)
      = ResolvedExternalLeg.map (correctingPerm Fstar σ A) (A.retargetExternalLeg (D.starOf G A) ℓ) := by
  cases ℓ with | mk lid la lsec =>
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.map,
    ResolvedExternalLeg.retarget, correctingPerm_retargetVertex Fstar σ A hℓ]

/-- **R-6c-body-410 — the star vertices transport by `τ`.**  Mirrors `mapPerm_starVertices`, with the on-stars law
supplying the per-component compatibility. -/
theorem correctingPerm_starVertices (Fstar : ResolvedCanonicalStarFacts D) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) :
    (A.mapPerm σ).starVertices (D.starOf (G.mapPerm σ) (A.mapPerm σ))
      = (A.starVertices (D.starOf G A)).image (correctingPerm Fstar σ A) := by
  -- routed through `mem_image` / `mem_starVertices` (not `image_image`) to keep clear of the
  -- `ResolvedFeynmanSubgraph (G.mapPerm σ)` `DecidableEq` diamond; the on-stars law is the bridge.
  ext u
  simp only [ResolvedAdmissibleSubgraph.mem_starVertices, ResolvedAdmissibleSubgraph.mapPerm_elements,
    Finset.mem_image]
  constructor
  · rintro ⟨γσ, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨D.starOf G A γ, ⟨γ, hγ, rfl⟩, correctingPerm_on_stars Fstar σ A hγ⟩
  · rintro ⟨w, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ.mapPerm σ, ⟨γ, hγ, rfl⟩, (correctingPerm_on_stars Fstar σ A hγ).symm⟩

/-- **R-6c-body-410 ∎ — the mixed contraction graph equality.**  `(A.mapPerm σ).contractWithStars newStar =
(A.contractWithStars oldStar).mapPerm τ`.  This is the graph datum whose three `congrArg`-projections inhabit body-406's
`ResolvedContractTwiceClassData (new) (old)` with `starPerm = τ`. -/
theorem correctingPerm_contractWithStars (Fstar : ResolvedCanonicalStarFacts D) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G)
    (hE : AmbientEdgesSupported G) (hL : AmbientLegsSupported G) :
    (A.mapPerm σ).contractWithStars (D.starOf (G.mapPerm σ) (A.mapPerm σ))
      = (A.contractWithStars (D.starOf G A)).mapPerm (correctingPerm Fstar σ A) := by
  have hsurv : (G.vertices \ A.vertices).image σ
      = (G.vertices \ A.vertices).image (correctingPerm Fstar σ A) :=
    Finset.image_congr (fun w hw =>
      (correctingPerm_on_vertices Fstar σ A (Finset.mem_sdiff.mp hw).1).symm)
  have hv : ((G.mapPerm σ).vertices \ (A.mapPerm σ).vertices)
        ∪ (A.mapPerm σ).starVertices (D.starOf (G.mapPerm σ) (A.mapPerm σ))
      = ((G.vertices \ A.vertices) ∪ A.starVertices (D.starOf G A)).image (correctingPerm Fstar σ A) := by
    rw [correctingPerm_starVertices Fstar σ A, Finset.image_union,
        ResolvedAdmissibleSubgraph.mapPerm_vertices,
        show (G.mapPerm σ).vertices = G.vertices.image σ from rfl,
        ← Finset.image_sdiff G.vertices A.vertices σ.injective, hsurv]
  have hi : (A.mapPerm σ).complementEdges.map
        ((A.mapPerm σ).retargetEdge (D.starOf (G.mapPerm σ) (A.mapPerm σ)))
      = (A.complementEdges.map (A.retargetEdge (D.starOf G A))).map
          (ResolvedFeynmanEdge.map (correctingPerm Fstar σ A)) := by
    rw [ResolvedAdmissibleSubgraph.mapPerm_complementEdges, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl (fun e he_mem => ?_)
    have heG : e ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he_mem
    exact correctingPerm_retargetEdge Fstar σ A e (hE e heG).1 (hE e heG).2
  have he : (G.mapPerm σ).externalLegs.map
        ((A.mapPerm σ).retargetExternalLeg (D.starOf (G.mapPerm σ) (A.mapPerm σ)))
      = (G.externalLegs.map (A.retargetExternalLeg (D.starOf G A))).map
          (ResolvedExternalLeg.map (correctingPerm Fstar σ A)) := by
    show (G.externalLegs.map (ResolvedExternalLeg.map σ)).map
        ((A.mapPerm σ).retargetExternalLeg (D.starOf (G.mapPerm σ) (A.mapPerm σ)))
      = (G.externalLegs.map (A.retargetExternalLeg (D.starOf G A))).map
          (ResolvedExternalLeg.map (correctingPerm Fstar σ A))
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl
      (fun ℓ hℓ => correctingPerm_retargetExternalLeg Fstar σ A ℓ (hL ℓ hℓ))
  exact congr (congr (congrArg ResolvedFeynmanGraph.mk hv) hi) he

end GaugeGeometry.QFT.Combinatorial
