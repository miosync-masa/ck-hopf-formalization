import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductConnectors
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainConcrete

/-!
# R-6c-leaf-14 — Product connector term bodies (`selectedOuter_term_eq`, `quotient_term_eq`)

Tenth leaf-body discharge, working on the two `ResolvedProductConnectorSupply` term connectors (leaf-3).

**Ambient correction.**  Leaf-3's docstring claimed `selectedOuter_term_eq` compares `resolvedForestLeftTerm`
over *different* ambient graphs.  That is WRONG: `resolvedSelectedOuterTerm (imageOf s) =
resolvedForestLeftTerm (imageOf s).selectedOuter.1` (rfl) with `(imageOf s).selectedOuter.1 :
ResolvedAdmissibleSubgraph G`, and `selectedOuterRawOf s : ResolvedAdmissibleSubgraph G` — BOTH over `G`.  So
`selectedOuter_term_eq` reduces to a forest equality over `G`.

* `product_selectedOuter_term_eq_of_forest_eq` — `selectedOuter_term_eq` from `(imageOf s).selectedOuter.1 =
  selectedOuterRawOf s` (`congrArg resolvedForestLeftTerm`).
* `quotientForest_term_eq_right_mul_remnant` — the FULLY-PROVED Codomain-side decomposition: the quotient
  forest term is the product of the right-survivor and remnant forest terms *in the quotient graph* (via
  `quotientForest_elements_eq` + `forests_disjoint` + `Finset.prod_union`).
* `product_quotient_term_eq_of_forest_terms` — `quotient_term_eq` from that decomposition + the two
  forest-term transports (`M.remnantForest`/`R.rightSurvivorForest` terms = the Codomain forests' terms).

The quotient graph of `(imageOf s)` is `selectedOuter.1.contractWithStars …`, whereas `R`/`M`'s forests live
over `s.selectedOuterContractGraph`; the residual transports are exactly that ambient bridge (genuine
de-contraction geometry), left as hypotheses.

Per the HALT, `selectedOuter_eq` and the two transports are NOT proved; `occurrence_inj` / RIGHT leaves untouched.

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

/-- **R-6c-leaf-14 — the Product `selectedOuter_term_eq` leaf from the selected-outer forest equality.**  Both
sides are `resolvedForestLeftTerm` over `G`, so a forest equality closes it. -/
theorem product_selectedOuter_term_eq_of_forest_eq
    (selectedOuter_eq : ∀ s : ResolvedCoassocSplitChoice D G,
      (imageOf s).selectedOuter.1 = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
    (s : ResolvedCoassocSplitChoice D G) :
    resolvedSelectedOuterTerm (imageOf s)
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) :=
  congrArg resolvedForestLeftTerm (selectedOuter_eq s)

/-- **R-6c-leaf-14 — the Codomain-side quotient-forest decomposition (fully proved).**  The quotient forest
term is the product of the right-survivor and remnant forest terms in the quotient graph. -/
theorem quotientForest_term_eq_right_mul_remnant
    (Co : ResolvedCodomainConcreteSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    resolvedForestLeftTerm (imageOf s).quotientForest
      = resolvedForestLeftTerm (Co.rightForest s) * resolvedForestLeftTerm (Co.remnantForest s) := by
  classical
  rw [resolvedForestLeftTerm_eq_prod, resolvedForestLeftTerm_eq_prod, resolvedForestLeftTerm_eq_prod,
    Co.quotientForest_elements_eq s]
  exact Finset.prod_union (Co.forests_disjoint s)

/-- **R-6c-leaf-14 — the Product `quotient_term_eq` leaf from the Codomain decomposition + forest-term
transports.**  Given that the Product-side remnant / right-survivor forest terms equal the Codomain-side
remnant / right forest terms, the quotient decomposition yields `quotient_term_eq` (with `mul_comm`). -/
theorem product_quotient_term_eq_of_forest_terms
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G)
    (Co : ResolvedCodomainConcreteSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (h_remnant : resolvedForestLeftTerm (M.remnantForest s)
      = resolvedForestLeftTerm (Co.remnantForest s))
    (h_survivor : resolvedForestLeftTerm (R.rightSurvivorForest s)
      = resolvedForestLeftTerm (Co.rightForest s)) :
    resolvedForestLeftTerm (M.remnantForest s) * resolvedForestLeftTerm (R.rightSurvivorForest s)
      = resolvedForestLeftTerm (imageOf s).quotientForest := by
  rw [h_remnant, h_survivor, quotientForest_term_eq_right_mul_remnant Co s, mul_comm]

end GaugeGeometry.QFT.Combinatorial
