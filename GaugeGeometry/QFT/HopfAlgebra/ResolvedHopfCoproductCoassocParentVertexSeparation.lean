import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentLegIdSeparationScout

/-!
# R-6c-body-24 — parent vertex-key separation from disjointness + star traceability

Twenty-fourth genuine-body step, PROVING body-23's `vertices_determine_parent` from four atomic structural
facts — the resolved replacement for the flat forest-insertion-uniqueness facade.

`contractedSourceGraph.vertices = (γ.vertices \ B.vertices) ∪ B.starVertices starOf` (body-20).  Given two
occurrences with equal contracted-vertex sets, pick any `w` in the (nonempty) first set; it lies in the second
too.  The surviving part sits inside `G.vertices`, the stars strictly outside it (freshness), so `w` is
"surviving in both" or "a star in both" — the mixed cases are impossible.  Then:

* surviving in both ⇒ `w` is a shared parent vertex ⇒ the parents coincide (forest-component DISJOINTNESS,
  contrapositive);
* a star in both ⇒ `w` is a shared star ⇒ the parents coincide (star TRACEABILITY / injectivity).

So `vertices_determine_parent` follows from `contracted_nonempty` + `star_not_mem_vertices` (freshness) +
`parent_disjoint` (shared vertex ⇒ equal parents) + `star_trace` (shared star ⇒ equal parents).  This file does
the full vertex-chase; the four fields are the genuine structural inputs (to be sourced from
`IsFreshStarAssignment` / the proper-forest pairwise disjointness in a later step).

Per the HALT, `retarget` / support-9 are untouched; the four geometry fields are supplied, not proved here.

Landed:

* `ResolvedParentVertexSeparationGeometrySupply D G s` — the four atomic facts;
* `.toParentVertexSeparationSupply` — body-23's `vertices_determine_parent`, PROVED via the case split.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-24 — the parent vertex-separation geometry supply.**  The four atomic structural facts that
make the contracted-vertex set determine the parent: nonemptiness, star freshness (stars outside `G`),
forest-component disjointness (shared parent vertex ⇒ equal parents), and star traceability (shared star ⇒
equal parents). -/
structure ResolvedParentVertexSeparationGeometrySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The contracted source graph has at least one vertex (a survivor or a star). -/
  contracted_nonempty : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.vertices.Nonempty
  /-- Star vertices are fresh: outside the ambient `G.vertices`. -/
  star_not_mem_vertices : ∀ (o : s.ForestChoiceOccurrence) {w : VertexId},
    w ∈ o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) → w ∉ G.vertices
  /-- Forest-component disjointness (contrapositive): a shared parent vertex forces equal parents. -/
  parent_disjoint : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    (∃ w, w ∈ o₁.γ.1.toResolvedFeynmanGraph.vertices ∧
        w ∈ o₂.γ.1.toResolvedFeynmanGraph.vertices) →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph
  /-- Star traceability: a shared star vertex forces equal parents. -/
  star_trace : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    (∃ w, w ∈ o₁.B.1.starVertices (D.starOf o₁.γ.1.toResolvedFeynmanGraph o₁.B.1) ∧
        w ∈ o₂.B.1.starVertices (D.starOf o₂.γ.1.toResolvedFeynmanGraph o₂.B.1)) →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-24 — body-23's vertex-separation supply, PROVED from the geometry.**  The contracted-vertex
equality determines the parent by the surviving-vs-star case split. -/
def ResolvedParentVertexSeparationGeometrySupply.toParentVertexSeparationSupply
    {s : ResolvedCoassocSplitChoice D G}
    (S : ResolvedParentVertexSeparationGeometrySupply D G s) :
    ResolvedParentVertexSeparationSupply D G s where
  vertices_determine_parent := fun o₁ o₂ h => by
    obtain ⟨w, hw₁⟩ := S.contracted_nonempty o₁
    have hw₂ : w ∈ o₂.contractedSourceGraph.vertices := h ▸ hw₁
    rw [o₁.contractedSourceGraph_vertices, Finset.mem_union] at hw₁
    rw [o₂.contractedSourceGraph_vertices, Finset.mem_union] at hw₂
    rcases hw₁ with hsurv₁ | hstar₁
    · rcases hw₂ with hsurv₂ | hstar₂
      · exact S.parent_disjoint o₁ o₂
          ⟨w, (Finset.mem_sdiff.mp hsurv₁).1, (Finset.mem_sdiff.mp hsurv₂).1⟩
      · exact absurd (o₁.γ.1.vertices_subset (Finset.mem_sdiff.mp hsurv₁).1)
          (S.star_not_mem_vertices o₂ hstar₂)
    · rcases hw₂ with hsurv₂ | hstar₂
      · exact absurd (o₂.γ.1.vertices_subset (Finset.mem_sdiff.mp hsurv₂).1)
          (S.star_not_mem_vertices o₁ hstar₁)
      · exact S.star_trace o₁ o₂ ⟨w, hstar₁, hstar₂⟩

end GaugeGeometry.QFT.Combinatorial
