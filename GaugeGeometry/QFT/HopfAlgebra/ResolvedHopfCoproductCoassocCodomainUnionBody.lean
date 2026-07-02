import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainForestChoice

/-!
# R-6c-body-13 — Codomain forest union/disjoint (disjoint reduced to the untransported forests)

Thirteenth genuine-body step, on body-12's two Codomain forest-choice fields (over the TRANSPORTED Product
forests `graph_eq ▸ R.rightSurvivorForest` / `graph_eq ▸ M.remnantForest`):

* `forests_disjoint` — DISCHARGED to the *untransported* disjointness: transport along a graph equality
  preserves `Finset`-disjointness of the element sets (`elements_disjoint_transport`, `subst h; rfl`), and the
  untransported `Disjoint (R.rightSurvivorForest s).elements (M.remnantForest s).elements` is exactly the
  Product `hDisj` (leaf-12, ⟸ body-2 `vertex_cross` + `cd_nonempty`).  So the transported disjointness needs no
  new geometry.
* `quotientForest_elements_eq` — stays a supply field: the quotient forest is the union of the transported
  right / remnant forests.  This is the genuine `fullQuotientOf.toImage = remnant ∪ right` fact (over the
  quotient graph), kept here.

Per the HALT, `quotientForest_elements_eq` is not proved; Sector element shapes / retarget untouched.

Landed:

* `elements_disjoint_transport` — transport preserves element-set disjointness;
* `ResolvedCodomainUnionConnector D G imageOf R M` — `Align` + `quotientForest_elements_eq` +
  `untransported_disjoint`;
* `.toCodomainForestChoiceSupply` — the body-12 supply (`forests_disjoint` from the untransported disjoint).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false in
/-- **R-6c-body-13 — transport along a graph equality preserves element-set disjointness. -/
theorem elements_disjoint_transport {H K : ResolvedFeynmanGraph} (h : H = K)
    (A B : ResolvedAdmissibleSubgraph H) :
    Disjoint (h ▸ A).elements (h ▸ B).elements ↔ Disjoint A.elements B.elements := by
  subst h; rfl

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-body-13 — the Codomain union connector.**  The alignment + the quotient-forest union shape + the
untransported right/remnant disjointness. -/
structure ResolvedCodomainUnionConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- The graph alignment `selectedOuterContractGraph = quotient graph`. -/
  Align : ResolvedSectorForwardGraphAlignment D G imageOf
  /-- The quotient forest is the union of the transported right / remnant forests. -/
  quotientForest_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).quotientForest.elements =
      (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements ∪
        (Align.quotientGraph_eq s ▸ M.remnantForest s).elements
  /-- The UNTRANSPORTED right / remnant forests are element-disjoint (= Product `hDisj`). -/
  untransported_disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (R.rightSurvivorForest s).elements (M.remnantForest s).elements

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-body-13 — the body-12 forest-choice supply (`forests_disjoint` from the untransported disjoint). -/
def ResolvedCodomainUnionConnector.toCodomainForestChoiceSupply
    (S : ResolvedCodomainUnionConnector D G imageOf R M) :
    ResolvedCodomainForestChoiceSupply D G imageOf R M where
  Align := S.Align
  quotientForest_elements_eq := S.quotientForest_elements_eq
  forests_disjoint := fun s => (elements_disjoint_transport _ _ _).mpr (S.untransported_disjoint s)

end GaugeGeometry.QFT.Combinatorial
