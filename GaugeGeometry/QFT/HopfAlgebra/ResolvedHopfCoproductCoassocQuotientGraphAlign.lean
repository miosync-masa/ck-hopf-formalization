import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductConnectorConcrete

/-!
# R-6c-leaf-20 — quotient-graph alignment (one `selectedOuter_eq` → Sector `quotientGraph_eq` + Product `hSel`)

Fifteenth leaf-body discharge, a high-leverage one: a SINGLE selected-outer forest equality feeds BOTH the
RIGHT sector (Align's `quotientGraph_eq`, leaf-19b) and the Product connector (`selectedOuter_term_eq` /
`hSel`, leaf-14).

Both `s.selectedOuterContractGraph` and `resolvedCoassocQuotientGraph (imageOf s)` are `contractWithStars`:

```text
s.selectedOuterContractGraph        = (selectedOuterRawOf s).contractWithStars (D.starOf G (selectedOuterRawOf s))
resolvedCoassocQuotientGraph (imageOf s) = (imageOf s).selectedOuter.1.contractWithStars (D.starOf G (imageOf s).selectedOuter.1)
```

so the graph equality is `congrArg (·.contractWithStars (D.starOf G ·)) selectedOuter_eq` — and the term
equality is exactly leaf-14's `product_selectedOuter_term_eq_of_forest_eq` of the same hypothesis.

Per the HALT, `selectedOuter_eq` (the concrete selected-outer = the promote body's `selectedOuterRawOf`) is a
supply field; Perm / Retarget / sector membership untouched.

Landed:

* `ResolvedSelectedOuterAlignment D G imageOf` — the single `selectedOuter_eq` field;
* `.toSectorForwardGraphAlignment` — the Sector Align's `quotientGraph_eq`;
* `.selectedOuter_term_eq` — the Product connector's `hSel` (via leaf-14).

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

/-- **R-6c-leaf-20 — the selected-outer alignment.**  The image's selected-outer forest is the concrete
`selectedOuterRawOf` (the promote body) — the single fact behind the Sector graph identification and the
Product selected-outer term connector. -/
structure ResolvedSelectedOuterAlignment (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- `(imageOf s).selectedOuter.1 = selectedOuterRawOf s`. -/
  selectedOuter_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).selectedOuter.1 = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s

/-- **R-6c-leaf-20 — the Sector forward graph alignment (`quotientGraph_eq`) from the selected-outer
equality.**  Both graphs are `contractWithStars` of equal selected-outer forests. -/
def ResolvedSelectedOuterAlignment.toSectorForwardGraphAlignment
    (Al : ResolvedSelectedOuterAlignment D G imageOf) :
    ResolvedSectorForwardGraphAlignment D G imageOf where
  quotientGraph_eq := fun s =>
    (congrArg (fun A => A.contractWithStars (D.starOf G A)) (Al.selectedOuter_eq s)).symm

/-- **R-6c-leaf-20 — the Product connector's `hSel` from the selected-outer equality (via leaf-14). -/
theorem ResolvedSelectedOuterAlignment.selectedOuter_term_eq
    (Al : ResolvedSelectedOuterAlignment D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    resolvedSelectedOuterTerm (imageOf s)
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) :=
  product_selectedOuter_term_eq_of_forest_eq Al.selectedOuter_eq s

end GaugeGeometry.QFT.Combinatorial
