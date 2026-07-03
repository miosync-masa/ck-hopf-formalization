import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentVertexSeparation

/-!
# R-6c-body-25 — sourcing the parent vertex-separation geometry fields

Twenty-fifth genuine-body step, connecting body-24's four geometry fields to their sources — separating what
is genuinely PROVABLE now from the minimal irreducible star kernel.

* `parent_disjoint` — **PROVED** from the proper-forest pairwise disjointness `s.1.1.pairwiseDisjoint` (the
  input outer forest's components are pairwise vertex-disjoint): a shared parent vertex contradicts
  disjointness of distinct components, so the parents coincide.
* `contracted_nonempty` / `star_not_mem_vertices` / `star_trace` — the STAR kernel.  `D.starOf` is an arbitrary
  field of `ResolvedCoproductProperForestData` constrained only by `hCD` (its contraction is connected
  divergent); it carries NO built-in freshness or injectivity.  Star freshness (`∉ G.vertices`) and GLOBAL
  star traceability (a shared star across two occurrences forces equal parents) are therefore genuine
  assumptions — the honest minimal kernel.  `contracted_nonempty` likewise is not free (a component may have
  an empty forest choice, and `CD → vertices.Nonempty` is itself fielded, body-1).  These three are bundled as
  `ResolvedStarFreshnessTraceSupply`.

So `parent_inj`'s four-field kernel collapses to: **proper-forest disjointness (discharged here) + a compact
star-freshness/traceability + nonemptiness supply**.  This is the precise resolved replacement of the flat
forest-insertion-uniqueness facade — the geometry that remains is exactly the star-id traceability, no more.

Per the HALT, `retarget` / support-9 untouched; no broad axiom is added — only the star kernel is fielded, and
`parent_disjoint` is proved from an existing structural field.

Landed:

* `parent_disjoint_of_pairwiseDisjoint` — `parent_disjoint` from `s.1.1.pairwiseDisjoint`;
* `ResolvedStarFreshnessTraceSupply D G s` — the star kernel (`contracted_nonempty` + `star_not_mem_vertices` +
  `star_trace`);
* `.toParentVertexSeparationGeometrySupply` — body-24's geometry supply (star kernel + proved disjointness).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-25 — `parent_disjoint` from proper-forest pairwise disjointness.**  A shared parent vertex
contradicts disjointness of distinct input-outer components, so the parents coincide. -/
theorem parent_disjoint_of_pairwiseDisjoint {s : ResolvedCoassocSplitChoice D G}
    (o₁ o₂ : s.ForestChoiceOccurrence)
    (hw : ∃ w, w ∈ o₁.γ.1.toResolvedFeynmanGraph.vertices ∧
        w ∈ o₂.γ.1.toResolvedFeynmanGraph.vertices) :
    o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph := by
  obtain ⟨w, hw₁, hw₂⟩ := hw
  by_contra hne
  have hne' : o₁.γ.1 ≠ o₂.γ.1 := fun heq =>
    hne (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph heq)
  exact absurd hw₂ (Finset.disjoint_left.mp (s.1.1.pairwiseDisjoint o₁.γ.2 o₂.γ.2 hne') hw₁)

/-- **R-6c-body-25 — the star freshness/traceability kernel.**  The genuine irreducible geometry over the
arbitrary `D.starOf`: the contracted graph is nonempty, its stars are fresh (outside `G`), and a shared star
traces to equal parents. -/
structure ResolvedStarFreshnessTraceSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The contracted source graph has at least one vertex. -/
  contracted_nonempty : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.vertices.Nonempty
  /-- Star vertices are fresh: outside the ambient `G.vertices`. -/
  star_not_mem_vertices : ∀ (o : s.ForestChoiceOccurrence) {w : VertexId},
    w ∈ o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) → w ∉ G.vertices
  /-- Star traceability: a shared star vertex forces equal parents. -/
  star_trace : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    (∃ w, w ∈ o₁.B.1.starVertices (D.starOf o₁.γ.1.toResolvedFeynmanGraph o₁.B.1) ∧
        w ∈ o₂.B.1.starVertices (D.starOf o₂.γ.1.toResolvedFeynmanGraph o₂.B.1)) →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph

/-- **R-6c-body-25 — body-24's geometry supply from the star kernel + proved disjointness. -/
def ResolvedStarFreshnessTraceSupply.toParentVertexSeparationGeometrySupply
    {s : ResolvedCoassocSplitChoice D G}
    (F : ResolvedStarFreshnessTraceSupply D G s) :
    ResolvedParentVertexSeparationGeometrySupply D G s where
  contracted_nonempty := F.contracted_nonempty
  star_not_mem_vertices := F.star_not_mem_vertices
  parent_disjoint := parent_disjoint_of_pairwiseDisjoint
  star_trace := F.star_trace

end GaugeGeometry.QFT.Combinatorial
