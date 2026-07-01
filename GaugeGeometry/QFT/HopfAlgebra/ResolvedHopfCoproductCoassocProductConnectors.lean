import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductGrandSupply

/-!
# R-6c-leaf-3 — Product `hSel` / `hQuot` connectors (grouped, `hQuot` reduced to a product form)

Third leaf-discharge step.  The two term connectors of `ResolvedProductEqGrandSupply` (6a-11b) are grouped
into ONE record and `hQuot` is reduced to a simpler leaf:

* `hSel` — `resolvedSelectedOuterTerm (imageOf s) = resolvedForestLeftTerm (selectedOuterRawOf s)`; the two
  sides are `resolvedForestLeftTerm` over *different* ambient graphs (`G` vs `selectedOuterContractGraph`),
  so it stays a term equality (the connector field `selectedOuter_term_eq`).
* `hQuot` — `resolvedForestLeftTerm ((remnantForest s).union (rightSurvivorForest s) (hCross s)) =
  resolvedForestLeftTerm (imageOf s).quotientForest`.  `resolvedForestLeftTerm_union` (LeftFactor) splits the
  union into a product, so `hQuot` follows from the union-free product leaf `quotient_term_eq :
  remnant term * right-survivor term = quotient-forest term` plus the element-disjointness `hDisj` — the
  `(hCross s)`-baked union proof term drops out of the leaf.

Per the HALT, the two connector fields (`selectedOuter_term_eq` / `quotient_term_eq`) are NOT proved; no
`survivorInj` / `remnantInj`; no full quotient equality.

Landed:

* `ResolvedProductConnectorSupply D G imageOf R M` — `selectedOuter_term_eq` + `quotient_term_eq`;
* `.hSel` — the Product `hSel` leaf (definitional);
* `.hQuot hCross hDisj` — the Product `hQuot` leaf (via `resolvedForestLeftTerm_union`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-3 — the Product term-connector supply.**  Groups the two `ResolvedProductEqGrandSupply`
term connectors, with the quotient side in the union-free product form. -/
structure ResolvedProductConnectorSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- The selected-outer term connector (`hSel`). -/
  selectedOuter_term_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    resolvedSelectedOuterTerm (imageOf s)
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
  /-- The quotient-forest term as a product (union-free form of `hQuot`). -/
  quotient_term_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    resolvedForestLeftTerm (M.remnantForest s) * resolvedForestLeftTerm (R.rightSurvivorForest s)
      = resolvedForestLeftTerm (imageOf s).quotientForest

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
  {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-leaf-3 — the Product `hSel` leaf (definitional). -/
theorem ResolvedProductConnectorSupply.hSel (C : ResolvedProductConnectorSupply D G imageOf R M) :
    ∀ s : ResolvedCoassocSplitChoice D G,
      resolvedSelectedOuterTerm (imageOf s)
        = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) :=
  C.selectedOuter_term_eq

/-- **R-6c-leaf-3 — the Product `hQuot` leaf, via `resolvedForestLeftTerm_union`.**  Takes the same
`hCross` (union proof) and element-disjointness `hDisj` that the grand record carries. -/
theorem ResolvedProductConnectorSupply.hQuot (C : ResolvedProductConnectorSupply D G imageOf R M)
    (hCross : ∀ (s : ResolvedCoassocSplitChoice D G),
      ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
        γ ≠ δ → γ.Disjoint δ)
    (hDisj : ∀ s : ResolvedCoassocSplitChoice D G,
      Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements) :
    ∀ s : ResolvedCoassocSplitChoice D G,
      resolvedForestLeftTerm ((M.remnantForest s).union (R.rightSurvivorForest s) (hCross s))
        = resolvedForestLeftTerm (imageOf s).quotientForest := by
  intro s
  rw [resolvedForestLeftTerm_union (M.remnantForest s) (R.rightSurvivorForest s) (hCross s) (hDisj s)]
  exact C.quotient_term_eq s

end GaugeGeometry.QFT.Combinatorial
