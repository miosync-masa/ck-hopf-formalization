import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainUnionBody

/-!
# R-6c-body-14 — quotient-forest elements from the full-quotient `toImage` split

Fourteenth genuine-body step, the last Codomain union leaf.  The quotient forest is the full-quotient image
`fullQuotientOf.toImage`, whose elements are (by `ResolvedFullQuotientForestImageData.toImage_elements`, rfl)
`remnantComponents ∪ rightComponents` — the REMNANT-then-RIGHT order.  With the full-quotient components being
the transported remnant / right forests (body-12's construction choice), this gives

```text
(imageOf s).quotientForest.elements = (transport M.remnantForest).elements ∪ (transport R.rightSurvivorForest).elements
```

(the `toImage_split` field — the genuine `fullQuotient = remnant ∪ right` fact).  Body-13's
`quotientForest_elements_eq` asks for the RIGHT-then-REMNANT order, so it follows by `Finset.union_comm`.

Per the HALT, `toImage_split` is the supply field (the full-quotient union); Sector element shapes / `parent_inj`
untouched.

Landed:

* `ResolvedQuotientForestElementsConnector D G imageOf R M` — `Align` + `toImage_split` + `untransported_disjoint`;
* `.toCodomainUnionConnector` — the body-13 connector (`quotientForest_elements_eq` via `union_comm`).

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

/-- **R-6c-body-14 — the quotient-forest elements connector.**  The full-quotient `toImage` split (remnant ∪
right) + the untransported disjointness. -/
structure ResolvedQuotientForestElementsConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- The graph alignment `selectedOuterContractGraph = quotient graph`. -/
  Align : ResolvedSectorForwardGraphAlignment D G imageOf
  /-- The quotient forest is the full-quotient `toImage`: remnant ∪ right (transported). -/
  toImage_split : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).quotientForest.elements =
      (Align.quotientGraph_eq s ▸ M.remnantForest s).elements ∪
        (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements
  /-- The untransported right / remnant forests are element-disjoint (= Product `hDisj`). -/
  untransported_disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (R.rightSurvivorForest s).elements (M.remnantForest s).elements

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-body-14 — the body-13 union connector (`quotientForest_elements_eq` via `union_comm`). -/
def ResolvedQuotientForestElementsConnector.toCodomainUnionConnector
    (S : ResolvedQuotientForestElementsConnector D G imageOf R M) :
    ResolvedCodomainUnionConnector D G imageOf R M where
  Align := S.Align
  quotientForest_elements_eq := fun s => by rw [S.toImage_split s]; exact Finset.union_comm _ _
  untransported_disjoint := S.untransported_disjoint

end GaugeGeometry.QFT.Combinatorial
