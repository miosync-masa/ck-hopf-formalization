import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentVertexSeparationSources
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts

/-!
# R-6c-body-26 — star kernel source scout: canonical facts are COMPONENT-LOCAL; the residual gap

Twenty-sixth genuine-body step, a source CHECKPOINT for body-25's `ResolvedStarFreshnessTraceSupply` (the
star kernel of `parent_inj`).

## Finding

The codebase records the canonical star properties as `ResolvedCanonicalStarFacts D` (leaf-1):

```text
starOf_fresh     : ∀ G' A η, η ∈ A.elements → D.starOf G' A η ∉ G'.vertices     -- fresh w.r.t. G' = the AMBIENT of A
starOf_injective : ∀ G' A {η δ}, η,δ ∈ A.elements → D.starOf G' A η = D.starOf G' A δ → η = δ  -- WITHIN one A
```

`ResolvedCoproductProperForestData` is purely parametric (no concrete instance exists; the concrete
`componentFreshStar` / `canonicalOuterStarOf` allocators are never assembled into a `D`).  So these two are the
only star facts available, and BOTH are COMPONENT-LOCAL:

* `starOf_fresh` gives freshness w.r.t. `G' = γ`'s intrinsic graph, NOT the global ambient `G ⊇ γ`.  The
  remnant star `D.starOf γG B η` is guaranteed outside `γG.vertices`, but MAY still land in `G.vertices \
  γG.vertices` (another component's vertices).
* `starOf_injective` separates components WITHIN one admissible subgraph, NOT across two different parents.

Body-24's kernel needs the GLOBAL upgrades: `star_not_mem_vertices` (∉ `G.vertices`) and `star_trace`
(cross-parent).  So `ResolvedCanonicalStarFacts` does NOT discharge the star kernel — it reaches exactly the
component-local half.

## What is provable, and the precise residual gap

* `remnant_star_not_mem_component_vertices` — PROVED from `ResolvedCanonicalStarFacts`: the remnant star is
  outside its own component graph `γG` (the local half).
* The residual gap is bundled as `ResolvedStarGlobalGapSupply`: `star_avoids_outer_vertices` (the remnant star
  avoids the REST of `G`, i.e. `G.vertices \ γG.vertices` — the inter-component freshness the local facts do
  not give), `star_trace` (cross-parent traceability), and `contracted_nonempty`.  Global freshness =
  local (canonical) + `star_avoids_outer_vertices`, so `.toStarFreshnessTraceSupply` assembles body-25's
  kernel from `ResolvedCanonicalStarFacts` + this sharper residual.

## Conclusion

The star kernel is NOT dischargeable from the existing canonical star API: it needs GLOBAL (inter-component)
freshness + CROSS-PARENT traceability, strictly stronger than the recorded component-local
`ResolvedCanonicalStarFacts`.  `ResolvedStarGlobalGapSupply` is the honest minimal residual hypothesis (with
the component-local half now discharged).  For a concrete `D` built from a G-globally-fresh allocator these
would hold; no such `D` exists in the codebase yet, so it remains a named hypothesis for parametric `D`.

Per the HALT: no freshness proof is invented, `ResolvedCoproductProperForestData` is unchanged, and the
residual is recorded as a named hypothesis.

Landed:

* `remnant_star_not_mem_component_vertices` — the component-local freshness of the remnant star (from
  `ResolvedCanonicalStarFacts`);
* `ResolvedStarGlobalGapSupply D G s` — the residual gap (outer-avoidance + cross-parent trace + nonempty);
* `.toStarFreshnessTraceSupply` — body-25's star kernel from `ResolvedCanonicalStarFacts` + the residual.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-26 — the remnant star is fresh w.r.t. its own component graph** (the component-local half,
provable from `ResolvedCanonicalStarFacts`). -/
theorem remnant_star_not_mem_component_vertices (F : ResolvedCanonicalStarFacts D)
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) {w : VertexId}
    (hw : w ∈ o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1)) :
    w ∉ o.γ.1.toResolvedFeynmanGraph.vertices := by
  rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hw
  obtain ⟨η, hη, rfl⟩ := hw
  exact F.starOf_fresh o.γ.1.toResolvedFeynmanGraph o.B.1 η hη

/-- **R-6c-body-26 — the residual star gap beyond the component-local canonical facts.**  The remnant star
avoids the REST of `G` (inter-component freshness), traces across parents, and the contracted graph is
nonempty. -/
structure ResolvedStarGlobalGapSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The remnant star avoids the rest of `G` (outside its own component). -/
  star_avoids_outer_vertices : ∀ (o : s.ForestChoiceOccurrence) {w : VertexId},
    w ∈ o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) →
      w ∉ G.vertices \ o.γ.1.toResolvedFeynmanGraph.vertices
  /-- Star traceability: a shared star vertex forces equal parents. -/
  star_trace : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    (∃ w, w ∈ o₁.B.1.starVertices (D.starOf o₁.γ.1.toResolvedFeynmanGraph o₁.B.1) ∧
        w ∈ o₂.B.1.starVertices (D.starOf o₂.γ.1.toResolvedFeynmanGraph o₂.B.1)) →
      o₁.γ.1.toResolvedFeynmanGraph = o₂.γ.1.toResolvedFeynmanGraph
  /-- The contracted source graph has at least one vertex. -/
  contracted_nonempty : ∀ o : s.ForestChoiceOccurrence,
    o.contractedSourceGraph.vertices.Nonempty

/-- **R-6c-body-26 — body-25's star kernel from the canonical facts + the residual gap.**  Global freshness =
component-local freshness (`ResolvedCanonicalStarFacts`) + inter-component avoidance (`star_avoids_outer_vertices`). -/
def ResolvedStarGlobalGapSupply.toStarFreshnessTraceSupply
    {s : ResolvedCoassocSplitChoice D G}
    (F : ResolvedCanonicalStarFacts D) (S : ResolvedStarGlobalGapSupply D G s) :
    ResolvedStarFreshnessTraceSupply D G s where
  contracted_nonempty := S.contracted_nonempty
  star_trace := S.star_trace
  star_not_mem_vertices := by
    intro o w hw hmem
    exact S.star_avoids_outer_vertices o hw
      (Finset.mem_sdiff.mpr ⟨hmem, remnant_star_not_mem_component_vertices F o hw⟩)

end GaugeGeometry.QFT.Combinatorial
