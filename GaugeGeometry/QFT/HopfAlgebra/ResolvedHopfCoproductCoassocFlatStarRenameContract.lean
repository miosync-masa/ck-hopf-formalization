import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFlatStarRename

/-!
# R-6c-body-424 — the star-renaming contraction relation (PROVED)

Four-hundred-and-twenty-fourth genuine-body step — the flat contraction relation for two fresh star assignments related
by body-423's correcting permutation `ρ`.  This is the flat, `σ = id` analog of body-410's `correctingPerm_contractWithStars`:
the two contractions of the SAME forest differ only by relabeling the fresh stars.

* `flatStarRename_retargetVertex` — the retarget maps agree up to `ρ`: `B.retargetVertex s₂ w = ρ (B.retargetVertex s₁ w)`
  for `w ∈ G.vertices` (in-forest via body-423's on-stars at the component, off-forest via on-ambient);
* `flatStarRename_contractWithStars` — `B.contractWithStars s₂ = (B.contractWithStars s₁).mapPerm ρ`, assembled
  field-by-field (survivors fixed by on-ambient, star vertices moved by on-stars, edges/legs by the retarget agreement;
  endpoint support from `G.WellFormed`).

Per the HALT: NO CD, NO `hCD`, NO RawW here — this is the graph relation only.  Body-425 consumes it: `B :=
A.forget`, `s₁ := resolvedStarOnForget`, `s₂ := A.forget.componentFreshStar`; then the flat canonical CD
(`admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation`, ambient CD from body-418's `ambientCD_of_mem`)
transfers to `s₁` via `mapPerm_isConnectedDivergent_iff` and body-422, giving the RawW `hCD`; then the RawW record and the
real supported `W`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-424 — the retarget maps agree up to `ρ`** (for ambient vertices). -/
theorem flatStarRename_retargetVertex {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s₁ s₂ : FeynmanSubgraph G → VertexId)
    (h₁ : B.IsFreshStarAssignment s₁) (h₂ : B.IsFreshStarAssignment s₂)
    {w : VertexId} (hw : w ∈ G.vertices) :
    B.retargetVertex s₂ w = flatStarRenamePerm B s₁ s₂ h₁ h₂ (B.retargetVertex s₁ w) := by
  by_cases hwB : w ∈ B.vertices
  · rw [AdmissibleSubgraph.retargetVertex, AdmissibleSubgraph.componentAt?_of_mem _ hwB,
        AdmissibleSubgraph.retargetVertex, AdmissibleSubgraph.componentAt?_of_mem _ hwB]
    exact (flatStarRenamePerm_on_stars B s₁ s₂ h₁ h₂ (B.componentAt_mem hwB)).symm
  · rw [AdmissibleSubgraph.retargetVertex_of_not_mem _ _ hwB,
        AdmissibleSubgraph.retargetVertex_of_not_mem _ _ hwB]
    exact (flatStarRenamePerm_on_ambient B s₁ s₂ h₁ h₂ hw).symm

/-- **R-6c-body-424 ∎ — the star-renaming contraction relation.**  Two fresh star assignments on the same forest give
contractions differing only by the correcting permutation `ρ`. -/
theorem flatStarRename_contractWithStars {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s₁ s₂ : FeynmanSubgraph G → VertexId)
    (h₁ : B.IsFreshStarAssignment s₁) (h₂ : B.IsFreshStarAssignment s₂)
    (hWF : G.WellFormed) :
    B.contractWithStars s₂
      = (B.contractWithStars s₁).mapPerm (flatStarRenamePerm B s₁ s₂ h₁ h₂) := by
  set ρ := flatStarRenamePerm B s₁ s₂ h₁ h₂ with hρ
  have hv : (G.vertices \ B.vertices) ∪ B.starVertices s₂
      = ((G.vertices \ B.vertices) ∪ B.starVertices s₁).image ρ := by
    have hsurv : (G.vertices \ B.vertices).image ρ = G.vertices \ B.vertices := by
      ext v
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rwa [flatStarRenamePerm_on_ambient B s₁ s₂ h₁ h₂ (Finset.mem_sdiff.mp hw).1]
      · intro hv
        exact ⟨v, hv, flatStarRenamePerm_on_ambient B s₁ s₂ h₁ h₂ (Finset.mem_sdiff.mp hv).1⟩
    have hstar : (B.starVertices s₁).image ρ = B.starVertices s₂ := by
      unfold AdmissibleSubgraph.starVertices
      rw [Finset.image_image]
      exact Finset.image_congr (fun γ hγ => flatStarRenamePerm_on_stars B s₁ s₂ h₁ h₂ hγ)
    rw [Finset.image_union, hsurv, hstar]
  have hi : B.complementEdges.map (B.retargetEdge s₂)
      = (B.complementEdges.map (B.retargetEdge s₁)).map (FeynmanEdge.map ρ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun e he => ?_)
    have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) he
    obtain ⟨hs, ht⟩ := hWF.1 e heG
    show B.retargetEdge s₂ e = FeynmanEdge.map ρ (B.retargetEdge s₁ e)
    rw [AdmissibleSubgraph.retargetEdge, AdmissibleSubgraph.retargetEdge, FeynmanEdge.map,
      flatStarRename_retargetVertex B s₁ s₂ h₁ h₂ hs,
      flatStarRename_retargetVertex B s₁ s₂ h₁ h₂ ht]
  have hlegs : G.externalLegs.map (B.retargetExternalLeg s₂)
      = (G.externalLegs.map (B.retargetExternalLeg s₁)).map (ExternalLeg.map ρ) := by
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl (fun l hl => ?_)
    have ha := hWF.2 l hl
    show B.retargetExternalLeg s₂ l = ExternalLeg.map ρ (B.retargetExternalLeg s₁ l)
    rw [AdmissibleSubgraph.retargetExternalLeg, AdmissibleSubgraph.retargetExternalLeg,
      ExternalLeg.map, flatStarRename_retargetVertex B s₁ s₂ h₁ h₂ ha]
  exact congr (congr (congrArg FeynmanGraph.mk hv) hi) hlegs

end GaugeGeometry.QFT.Combinatorial
