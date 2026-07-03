import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRetargetOnVertices

/-!
# R-6c-body-27 — retarget_corr_on_vertices via a three-route case split

Twenty-seventh genuine-body step, decomposing leaf-37's `retarget_corr_on_vertices` (the contract-twice vertex
composition in three-route correspondence coordinates, on `G.vertices`) into the three routes — in the spirit
of the 6a-8c-0 mismatch correction, phrased in the CORRECTED coordinates (not the old star↔star).

For `v ∈ G.vertices` the contract-twice composition splits by where `v` sits relative to the input outer
forest `A = s.1.1`:

* **survivingOriginal** (`v ∉ A.vertices`): the one-stage retarget fixes `v` (`retargetVertex_of_not_mem`),
  and the RHS traces back to `v` through the surviving-original route;
* **inner-left** (`v ∈ A.vertices`, left/selected component): the one-stage star is a two-stage SURVIVOR
  (a LEFT star), recovered through the correspondence's left branch;
* **inner-right** (`v ∈ A.vertices`, forest/right component): the one-stage star is a quotient-forest star,
  recovered through the right branch.

The inner left/right split is by a supplied partition predicate `innerLeft` (its exact definition — the
left-selection classification — is the genuine route geometry; carried as a field so the two inner routes are
discharged in their own coordinates).  The assembly is a total `by_cases` dichotomy (`v ∈ A.vertices`, then
`innerLeft`), so the three route fields fully determine `retarget_corr_on_vertices`.

Per the HALT, the three route equalities are NOT proved (fielded — the genuine three-route action); no
off-vertex bridge, no Perm construction.  Should the routes reveal another coordinate mismatch, that is
recorded at the field boundary rather than forced.

Landed:

* `RetargetCorrOnVerticesTarget` — the target equation as a reusable `Prop`;
* `ResolvedRetargetCorrCaseSupply D G imageOf Three` — `innerLeft` + the three route fields;
* `.toRetargetOnVerticesConnector` — leaf-37's connector, assembled by the `by_cases` dichotomy.

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

/-- **R-6c-body-27 — the contract-twice on-vertices target equation** (leaf-37's `retarget_corr_on_vertices`
statement, as a reusable `Prop`). -/
def RetargetCorrOnVerticesTarget (Three : ResolvedThreeRouteProvedSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices) : Prop :=
  s.1.1.retargetVertex (D.starOf G s.1.1) v
    = ((Three.toVertexCorrespondence s).invFun
        ⟨(imageOf s).quotientForest.retargetVertex
            (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
            (rightVertexDomain (imageOf s) v), resolved_retarget_rhs_mem s hv⟩).1

/-- **R-6c-body-27 — the three-route case supply.**  A partition predicate `innerLeft` for the inner
left/right split, and the target equation on each of the three routes (survivingOriginal / inner-left /
inner-right). -/
structure ResolvedRetargetCorrCaseSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (Three : ResolvedThreeRouteProvedSupply D G imageOf) where
  /-- The inner left/right partition (left-selection classification). -/
  innerLeft : ResolvedCoassocSplitChoice D G → VertexId → Prop
  /-- **survivingOriginal route**: `v` outside the input outer forest. -/
  outer_case : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices),
    v ∉ s.1.1.vertices → RetargetCorrOnVerticesTarget Three s hv
  /-- **inner-left route**: `v` in a left/selected component of the input outer forest. -/
  inner_left_case : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices),
    v ∈ s.1.1.vertices → innerLeft s v → RetargetCorrOnVerticesTarget Three s hv
  /-- **inner-right route**: `v` in a forest/right component of the input outer forest. -/
  inner_right_case : ∀ (s : ResolvedCoassocSplitChoice D G) {v : VertexId} (hv : v ∈ G.vertices),
    v ∈ s.1.1.vertices → ¬ innerLeft s v → RetargetCorrOnVerticesTarget Three s hv

/-- **R-6c-body-27 — leaf-37's connector from the three route cases** (total `by_cases` dichotomy on
`v ∈ A.vertices`, then `innerLeft`). -/
def ResolvedRetargetCorrCaseSupply.toRetargetOnVerticesConnector
    {Three : ResolvedThreeRouteProvedSupply D G imageOf}
    (C : ResolvedRetargetCorrCaseSupply D G imageOf Three) :
    ResolvedRightRetargetOnVerticesConnector D G imageOf Three where
  retarget_corr_on_vertices := by
    intro s v hv
    classical
    by_cases h : v ∈ s.1.1.vertices
    · by_cases hl : C.innerLeft s v
      · exact C.inner_left_case s hv h hl
      · exact C.inner_right_case s hv h hl
    · exact C.outer_case s hv h

end GaugeGeometry.QFT.Combinatorial
