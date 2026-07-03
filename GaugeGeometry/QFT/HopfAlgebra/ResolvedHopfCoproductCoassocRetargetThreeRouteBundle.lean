import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetInnerRight

/-!
# R-6c-body-32 — the retarget three-route bundle

Thirty-second genuine-body step, packaging the three retarget routes (outer body-29b + inner-left body-30 +
inner-right body-31) into one record, so `retarget_corr_on_vertices` (leaf-37) flows from a single supply —
matching the Product / Sector leaf-bundle form.

The three route supplies each carry their own `innerLeft` partition predicate; the bundle ties the inner-left
and inner-right predicates together with `same_innerLeft`, then dispatches body-27's total `by_cases`
dichotomy to the three route cases.

Per the HALT, no inner applicability / recovery field is proved, no off-vertex bridge, and no connection to the
old `∀ v` `retargetVertex_eq`.

Landed:

* `ResolvedRetargetThreeRouteSupply D G imageOf Three` — `Outer` + `Left` + `Right` + `same_innerLeft`;
* `.toRetargetCorrCaseSupply` — body-27's case supply from the three routes;
* `.toRetargetOnVerticesConnector` — leaf-37's connector (one record → `retarget_corr_on_vertices`).

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

/-- **R-6c-body-32 — the retarget three-route bundle.**  The outer / inner-left / inner-right route supplies,
with the two inner partition predicates identified. -/
structure ResolvedRetargetThreeRouteSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The survivingOriginal (outer) route (body-29b). -/
  Outer : ResolvedRetargetOuterConcreteSupply D G imageOf Three
  /-- The inner-left route (body-30). -/
  Left : ResolvedRetargetInnerLeftSupply D G imageOf Three
  /-- The inner-right route (body-31). -/
  Right : ResolvedRetargetInnerRightSupply D G imageOf Three
  /-- The inner-left / inner-right partition predicates agree. -/
  same_innerLeft : Right.innerLeft = Left.innerLeft

/-- **R-6c-body-32 — body-27's case supply from the three routes. -/
def ResolvedRetargetThreeRouteSupply.toRetargetCorrCaseSupply
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (B : ResolvedRetargetThreeRouteSupply D G imageOf Three) :
    ResolvedRetargetCorrCaseSupply D G imageOf Three where
  innerLeft := B.Left.innerLeft
  outer_case := B.Outer.outer_case
  inner_left_case := B.Left.inner_left_case
  inner_right_case := B.same_innerLeft ▸ B.Right.inner_right_case

/-- **R-6c-body-32 — leaf-37's connector from the three-route bundle** (one record →
`retarget_corr_on_vertices`). -/
def ResolvedRetargetThreeRouteSupply.toRetargetOnVerticesConnector
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (B : ResolvedRetargetThreeRouteSupply D G imageOf Three) :
    ResolvedRightRetargetOnVerticesConnector D G imageOf Three :=
  B.toRetargetCorrCaseSupply.toRetargetOnVerticesConnector

end GaugeGeometry.QFT.Combinatorial
