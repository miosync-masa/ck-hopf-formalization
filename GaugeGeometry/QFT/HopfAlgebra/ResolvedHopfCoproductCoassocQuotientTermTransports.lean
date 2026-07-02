import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductConnectorConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainConcrete

/-!
# R-6c-leaf-26 — Product `quotient_term_eq` transports from graph-equality transport

Twenty-first leaf-body discharge — the leaf-14 residual.  `product_quotient_term_eq_of_forest_terms` needs
the two forest-term transports relating the Product-side forests (`R.rightSurvivorForest` /
`M.remnantForest`, over `s.selectedOuterContractGraph`) to the Codomain forests (`Co.rightForest` /
`Co.remnantForest`, over `resolvedCoassocQuotientGraph (imageOf s)`).  Since the two ambient graphs are equal
(`graph_eq`, = leaf-20's `quotientGraph_eq`, `rfl` for the concrete image side, leaf-25), the Codomain forests
are the transports of the Product forests along `graph_eq`, and `resolvedForestLeftTerm` is transport-invariant
(`subst h; rfl`).

* `resolvedForestLeftTerm_transport` — `resolvedForestLeftTerm (h ▸ A) = resolvedForestLeftTerm A`;
* `ResolvedQuotientTermTransportConnector D G imageOf R M Co` — `graph_eq` + `right_transport` +
  `remnant_transport` (the Codomain forests are the transported Product forests);
* `.h_survivor` / `.h_remnant` — the leaf-14 residual transports;
* `.quotient_term_eq` — the Product connector's `hQuot` core (via `product_quotient_term_eq_of_forest_terms`).

Per the HALT, `occurrence_inj` untouched; `quotientForest_elements_eq` is leaf-15's; the transports are stated
via `graph_eq` (the caller supplies the concrete `Codomain = transport of R/M`).

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
/-- **R-6c-leaf-26 — `resolvedForestLeftTerm` is invariant under transport along a graph equality. -/
theorem resolvedForestLeftTerm_transport
    {H K : ResolvedFeynmanGraph} (h : H = K) (A : ResolvedAdmissibleSubgraph H) :
    resolvedForestLeftTerm (h ▸ A) = resolvedForestLeftTerm A := by
  subst h; rfl

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-leaf-26 — the quotient-term transport connector.**  The Codomain right / remnant forests are the
transports of the Product right-survivor / remnant forests along the graph equality. -/
structure ResolvedQuotientTermTransportConnector (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G)
    (Co : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The split choice's contract graph equals the image's quotient graph (leaf-20). -/
  graph_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    s.selectedOuterContractGraph = resolvedCoassocQuotientGraph (imageOf s)
  /-- The Codomain right forest is the transported right-survivor forest. -/
  right_transport : ∀ s : ResolvedCoassocSplitChoice D G,
    Co.rightForest s = (graph_eq s) ▸ (R.rightSurvivorForest s)
  /-- The Codomain remnant forest is the transported remnant forest. -/
  remnant_transport : ∀ s : ResolvedCoassocSplitChoice D G,
    Co.remnantForest s = (graph_eq s) ▸ (M.remnantForest s)

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}
  {Co : ResolvedCodomainConcreteSupply D G imageOf}

/-- **R-6c-leaf-26 — the right-survivor forest-term transport (leaf-14 residual). -/
theorem ResolvedQuotientTermTransportConnector.h_survivor
    (T : ResolvedQuotientTermTransportConnector D G imageOf R M Co)
    (s : ResolvedCoassocSplitChoice D G) :
    resolvedForestLeftTerm (R.rightSurvivorForest s) = resolvedForestLeftTerm (Co.rightForest s) := by
  rw [T.right_transport s, resolvedForestLeftTerm_transport]

/-- **R-6c-leaf-26 — the remnant forest-term transport (leaf-14 residual). -/
theorem ResolvedQuotientTermTransportConnector.h_remnant
    (T : ResolvedQuotientTermTransportConnector D G imageOf R M Co)
    (s : ResolvedCoassocSplitChoice D G) :
    resolvedForestLeftTerm (M.remnantForest s) = resolvedForestLeftTerm (Co.remnantForest s) := by
  rw [T.remnant_transport s, resolvedForestLeftTerm_transport]

/-- **R-6c-leaf-26 — the Product connector's `quotient_term_eq` from the transports (via leaf-14). -/
theorem ResolvedQuotientTermTransportConnector.quotient_term_eq
    (T : ResolvedQuotientTermTransportConnector D G imageOf R M Co)
    (s : ResolvedCoassocSplitChoice D G) :
    resolvedForestLeftTerm (M.remnantForest s) * resolvedForestLeftTerm (R.rightSurvivorForest s)
      = resolvedForestLeftTerm (imageOf s).quotientForest :=
  product_quotient_term_eq_of_forest_terms R M Co s (T.h_remnant s) (T.h_survivor s)

end GaugeGeometry.QFT.Combinatorial
