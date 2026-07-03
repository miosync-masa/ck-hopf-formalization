import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetLeftStarEq

/-!
# R-6c-body-47 — left star-allocation compatibility: `retargets_agree` = componentAt agreement + star coherence

Forty-seventh genuine-body step, decomposing body-46's `retargets_agree` (the left-route star-allocation
compatibility) into two clean component-level facts.

`retargets_agree : s.1.1.retargetVertex (D.starOf G s.1.1) v = (imageOf s).selectedOuter.1.retargetVertex
(D.starOf G …) v`.  Since `retargetVertex A starOf v = match A.componentAt? v with | some γ => starOf γ | none
=> v`, the equality splits into:

* `componentAt_agree` — the input outer and the selected outer pick the SAME containing component of `v`
  (`s.1.1.componentAt? v = (imageOf s).selectedOuter.1.componentAt? v`).  (`componentAt := Classical.choose …`,
  so this is a component recovery equality — kept as a field, per the HALT `Classical.choose` barrier.)
* `star_coherence` — on that shared component `γ`, `D.starOf` agrees between the two admissible subgraphs:
  `D.starOf G s.1.1 γ = D.starOf G (imageOf s).selectedOuter.1 γ`.

This is the star-allocation **COHERENCE** — "the same component's star is the same `VertexId` whether allocated
via `s.1.1` or the selected outer".  It is a GENUINELY DIFFERENT `D.starOf` property from the parent kernel's
star **TRACEABILITY** (`star_trace`: equal stars ⇒ equal parents).  Coherence = one geometry seen in two forest
coordinates gives one star; traceability = one star identifies its parent.  For parametric `D` both are
independent star-allocation assumptions.

Per the HALT, `componentAt_agree` (the `Classical.choose` component recovery) and `star_coherence` are fielded;
the match-collapse of `retargetVertex` is proved.

Landed:

* `ResolvedLeftStarCompatibilitySupply D G imageOf App` — `componentAt_agree` + `star_coherence`;
* `.retargets_agree` — body-46's field, PROVED by the `componentAt?` case split.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-47 — the left star-allocation compatibility supply.**  The input-outer / selected-outer
component agreement and the star-allocation coherence on the shared component. -/
structure ResolvedLeftStarCompatibilitySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (App : ResolvedRetargetInnerApplicabilitySupply D G imageOf) where
  /-- The input outer and selected outer pick the same containing component of a left `v`. -/
  componentAt_agree : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId},
    App.innerLeft s v →
    s.1.1.componentAt? v = (imageOf s).selectedOuter.1.componentAt? v
  /-- On the shared component, `D.starOf` agrees between `s.1.1` and the selected outer (star coherence). -/
  star_coherence : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId}
    (γ : ResolvedFeynmanSubgraph G), App.innerLeft s v → s.1.1.componentAt? v = some γ →
    D.starOf G s.1.1 γ = D.starOf G (imageOf s).selectedOuter.1 γ

/-- **R-6c-body-47 — body-46's `retargets_agree`, PROVED from componentAt agreement + star coherence. -/
theorem ResolvedLeftStarCompatibilitySupply.retargets_agree
    {App : ResolvedRetargetInnerApplicabilitySupply D G imageOf}
    (F : ResolvedLeftStarCompatibilitySupply D G imageOf App)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hleft : App.innerLeft s v) :
    s.1.1.retargetVertex (D.starOf G s.1.1) v = rightVertexDomain (imageOf s) v := by
  rw [rightVertexDomain, ResolvedAdmissibleSubgraph.retargetVertex,
    ResolvedAdmissibleSubgraph.retargetVertex, F.componentAt_agree s hleft]
  cases h : (imageOf s).selectedOuter.1.componentAt? v with
  | none => rfl
  | some δ => exact F.star_coherence s δ hleft ((F.componentAt_agree s hleft).trans h)

end GaugeGeometry.QFT.Combinatorial
