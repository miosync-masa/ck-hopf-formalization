import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientTermTransports
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardTransport

/-!
# R-6c-body-12 — Codomain forest construction choice (transports become `rfl`)

Twelfth genuine-body step, a CONSTRUCTION CHOICE that discharges the leaf-26 forest-term transports.  The
Codomain forests are DEFINED as the Product forests transported along the graph alignment:

```text
Co.rightForest s  := Align.quotientGraph_eq s ▸ R.rightSurvivorForest s
Co.remnantForest s := Align.quotientGraph_eq s ▸ M.remnantForest s
```

With this choice, leaf-26's `right_transport` / `remnant_transport` (`Co.rightForest s = graph_eq s ▸
R.rightSurvivorForest s`) are `rfl`, so the whole leaf-26 chain (`h_survivor` / `h_remnant` /
`quotient_term_eq`, via `resolvedForestLeftTerm_transport`) is discharged — the Product `hQuot` residual is gone.

The Codomain fields `quotientForest_elements_eq` / `forests_disjoint` (now over the transported forests) remain
genuine geometry, kept as supply fields.

Per the HALT, the two Codomain fields are not proved; Sector membership untouched.

Landed:

* `ResolvedCodomainForestChoiceSupply D G imageOf R M` — `Align` + the two Codomain fields over the transports;
* `.toCodomainConcreteSupply` — the Codomain with forests = transported `R` / `M` forests;
* `.toQuotientTermTransportConnector` — the leaf-26 connector with `rfl` transports.

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

/-- **R-6c-body-12 — the Codomain forest-choice supply.**  The alignment + the two Codomain facts over the
transported Product forests. -/
structure ResolvedCodomainForestChoiceSupply (D : ResolvedCoproductProperForestData)
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
  /-- The transported right / remnant forests are disjoint. -/
  forests_disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (Align.quotientGraph_eq s ▸ R.rightSurvivorForest s).elements
      (Align.quotientGraph_eq s ▸ M.remnantForest s).elements

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-body-12 — the Codomain with forests chosen as the transported Product forests. -/
noncomputable def ResolvedCodomainForestChoiceSupply.toCodomainConcreteSupply
    (S : ResolvedCodomainForestChoiceSupply D G imageOf R M) :
    ResolvedCodomainConcreteSupply D G imageOf where
  rightForest := fun s => S.Align.quotientGraph_eq s ▸ R.rightSurvivorForest s
  remnantForest := fun s => S.Align.quotientGraph_eq s ▸ M.remnantForest s
  quotientForest_elements_eq := S.quotientForest_elements_eq
  forests_disjoint := S.forests_disjoint

/-- **R-6c-body-12 — the leaf-26 quotient-term transport connector with `rfl` transports. -/
noncomputable def ResolvedCodomainForestChoiceSupply.toQuotientTermTransportConnector
    (S : ResolvedCodomainForestChoiceSupply D G imageOf R M) :
    ResolvedQuotientTermTransportConnector D G imageOf R M S.toCodomainConcreteSupply where
  graph_eq := S.Align.quotientGraph_eq
  right_transport := fun _ => rfl
  remnant_transport := fun _ => rfl

end GaugeGeometry.QFT.Combinatorial
