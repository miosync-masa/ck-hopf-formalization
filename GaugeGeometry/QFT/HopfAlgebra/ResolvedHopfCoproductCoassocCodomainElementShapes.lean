import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorIndexSurjBody

/-!
# R-6c-body-5 — concrete Codomain element shapes (one supply → sector surjectivity, via body-4)

Fifth genuine-body step, high-leverage.  The two Codomain forest element shapes — `rightForest.elements` and
`remnantForest.elements` as `ofElements`-images over the component `attach` finsets (the leaf-29/30/body-3
inputs) — are grouped into ONE supply.  Because body-4 PROVED the two index surjectivities
(`sector_right_index_surj` / `sector_forest_index_surj`), this supply alone produces the full body-3 sector
surjectivity connector — so the sector `right_surj` / `forest_surj` now depend only on these two element shapes.

(The other two shapes of the "four" — `quotientForest.elements = rightForest ∪ remnantForest` and
`forests_disjoint` — are already the Codomain `C`'s own fields, `quotientForest_elements_eq` /
`forests_disjoint`; they need no separate supply here.)

Per the HALT, the two element shapes are supply fields (the Codomain `ofElements` construction); Sector inverse
laws / CD untouched.

Landed:

* `ResolvedConcreteCodomainElementShapeSupply C A` — `rightForest_elements_eq` + `remnant_elements_eq`;
* `.toSectorSurjectivityConnector` — the body-3 connector, with the index surjectivities supplied by body-4.

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

open scoped Classical

/-- **R-6c-body-5 — the concrete Codomain element shapes.**  The right / remnant forests are the
`ofElements`-images of the transported local survivor / remnant components. -/
structure ResolvedConcreteCodomainElementShapeSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (A : ResolvedSectorForwardAssemblerSupply C) where
  /-- The right forest is the image of the transported local survivor components. -/
  rightForest_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.rightForest s).elements =
      s.rightComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s)
          (rightSurvivorComponentOf s (A.Local.hne s) (A.Local.hcompl s) γ))
  /-- The remnant forest is the image of the transported remnant components. -/
  remnant_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.remnantForest s).elements =
      s.forestComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (A.Align.quotientGraph_eq s)
          ((A.Local.remnant s).remnantComponent (s.forestComponentOccurrence γ)))

/-- **R-6c-body-5 — the sector surjectivity connector from the element shapes (index surj by body-4). -/
def ResolvedConcreteCodomainElementShapeSupply.toSectorSurjectivityConnector
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {A : ResolvedSectorForwardAssemblerSupply C}
    (S : ResolvedConcreteCodomainElementShapeSupply C A) :
    ResolvedSectorSurjectivityConnector C A where
  right_elements_eq := S.rightForest_elements_eq
  remnant_elements_eq := S.remnant_elements_eq
  right_index_surj := sector_right_index_surj
  forest_index_surj := sector_forest_index_surj

end GaugeGeometry.QFT.Combinatorial
