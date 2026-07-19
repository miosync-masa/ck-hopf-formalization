import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarOnForget

/-!
# R-6c-body-421 — the retarget / star-vertex forget-correspondences (PROVED)

Four-hundred-and-twenty-first genuine-body step — the two load-bearing correspondences of the resolved↔flat
forget-commutativity (the pure-`forget` half of the `hCD` impedance match, before any canonical star or CD is
introduced).  Body-420 descended the resolved fresh star onto `A.forget`; this body proves the resolved contraction's
retarget map and star-vertex set are exactly the flat ones for that descended star.

* `forget_isPairwiseDisjoint` — `A.forget.IsPairwiseDisjoint` (from `A.pairwiseDisjoint`, needed for the flat
  `componentAt` uniqueness);
* `retargetVertex_forget_eq` — `A.forget.retargetVertex resolvedStarOnForget = A.retargetVertex resolvedStar`, pointwise:
  in-forest via the `componentAt` correspondence (`A.forget.componentAt v = (A.componentAt v).forget`, by flat
  disjoint-uniqueness) + body-420's `resolvedStarOnForget_spec`; off-forest both are the identity;
* `starVertices_forget_eq` — `A.forget.starVertices resolvedStarOnForget = A.starVertices resolvedStar`
  (`forget_elements` + `image_image` + the spec).

Per the HALT: the full graph equality `(A.contractWithStars resolvedStar).forget = A.forget.contractWithStars
resolvedStarOnForget` is body-422 — it assembles these two with the complement-edge correspondence
(`A.forget.complementEdges = A.complementEdges.map forget`, a BOUNDED multiset map-subtraction via `Multiset.countP_sub`
under `A.internalEdges ≤ G.internalEdges`, NOT edge-`forget` injectivity) and `forget_contractWithStars`.  The
star-RENAMING to the flat canonical star and the final `hCD`/RawW assembly follow.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-421 — the forgotten forest is pairwise disjoint.**  From `A.pairwiseDisjoint` (`forget` preserves each
component's vertices). -/
theorem forget_isPairwiseDisjoint {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G) :
    A.forget.IsPairwiseDisjoint := by
  intro γ' h₁ δ' h₂ hne
  obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.mp h₂
  have hd : γ.Disjoint δ := A.pairwiseDisjoint hγ hδ (fun h => hne (by rw [h]))
  unfold ResolvedFeynmanSubgraph.Disjoint at hd
  simpa only [ResolvedFeynmanSubgraph.forget_vertices, FeynmanSubgraph.Disjoint] using hd

/-- **R-6c-body-421 — the retarget maps agree.**  Pointwise: in-forest via the `componentAt` correspondence
(`A.forget.componentAt v = (A.componentAt v).forget`) + body-420's spec; off-forest both are the identity. -/
theorem retargetVertex_forget_eq {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (hpf : A.IsProperForest) (v : VertexId) :
    A.forget.retargetVertex (resolvedStarOnForget A) v
      = A.retargetVertex (resolvedComponentFreshStar G A) v := by
  by_cases hv : v ∈ A.vertices
  · have hv' : v ∈ A.forget.vertices := by rw [forget_vertices_eq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
        ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv,
        AdmissibleSubgraph.retargetVertex, AdmissibleSubgraph.componentAt?_of_mem _ hv']
    have hcomp : A.forget.componentAt hv' = (A.componentAt hv).forget := by
      apply AdmissibleSubgraph.componentAt_eq_of_mem_vertices (forget_isPairwiseDisjoint A)
        (Finset.mem_image_of_mem _ (A.componentAt_mem hv))
      rw [ResolvedFeynmanSubgraph.forget_vertices]; exact A.componentAt_vertex_mem hv
    show resolvedStarOnForget A (A.forget.componentAt hv') = _
    rw [hcomp, resolvedStarOnForget_spec A hpf (A.componentAt_mem hv)]
  · have hv' : v ∉ A.forget.vertices := by rw [forget_vertices_eq]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv,
        AdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv']

/-- **R-6c-body-421 — the star-vertex sets agree.**  `A.forget`'s star vertices for the descended star equal `A`'s for
the resolved star (`forget_elements` + `image_image` + body-420's spec). -/
theorem starVertices_forget_eq {G : ResolvedFeynmanGraph} (A : ResolvedAdmissibleSubgraph G)
    (hpf : A.IsProperForest) :
    A.forget.starVertices (resolvedStarOnForget A)
      = A.starVertices (resolvedComponentFreshStar G A) := by
  unfold AdmissibleSubgraph.starVertices ResolvedAdmissibleSubgraph.starVertices
  rw [ResolvedAdmissibleSubgraph.forget_elements, Finset.image_image]
  exact Finset.image_congr (fun γ hγ => resolvedStarOnForget_spec A hpf hγ)

end GaugeGeometry.QFT.Combinatorial
