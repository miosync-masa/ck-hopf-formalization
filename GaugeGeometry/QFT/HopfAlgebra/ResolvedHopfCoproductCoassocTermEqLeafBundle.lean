import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductInjectionLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightLeafBundle
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEqGrandSupply

/-!
# R-6c-leaf-7 — `term_eq` leaf bundle (the WHOLE heart leaf boundary, one record tree)

The two flat leaf bundles (Product, leaf-5; RIGHT, leaf-6) plus the inner strict-summand supply are collected
into ONE record `ResolvedTermEqLeafBundle`, which produces the `ResolvedTermEqGrandSupply` (6a-11c) and hence
the heart `term_eq`.  So the entire algebra/geometry term boundary of resolved coassociativity is a single
record tree:

```text
ResolvedTermEqLeafBundle
  = { Product : ResolvedProductLeafBundle,  Right : ResolvedRightLeafBundle,  Inner }
  → term_eq
```

Per the HALT, no leaf bodies are proved; `GrandFullSupply` (finite cover) is not reached; the
`GrandImageSideSupply` (whose `imageOf` is *derived* from the inner strict-summand's image side) is deferred.

Landed:

* `ResolvedTermEqLeafBundle D G imageOf` — `Product` + `Right` + `Inner`;
* `.toProductEqGrandSupply` / `.toRightGrandSupply` / `.toTermEqGrandSupply`;
* `.term_eqs` — the heart term agreement from the bundle.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-7 — the `term_eq` leaf bundle.**  The two flat leaf bundles + the inner strict-summand
supply — the whole heart term boundary in one record. -/
structure ResolvedTermEqLeafBundle (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The Product leaf bundle (leaf-5) → `product_eq`. -/
  Product : ResolvedProductLeafBundle D G imageOf
  /-- The RIGHT leaf bundle (leaf-6) → `right_eq`. -/
  Right : ResolvedRightLeafBundle D G imageOf
  /-- The inner quotient-of-quotient generator supply. -/
  Inner : ResolvedCoassocInnerRightSupply D G

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-leaf-7 — the Product grand supply from the bundle. -/
def ResolvedTermEqLeafBundle.toProductEqGrandSupply
    (B : ResolvedTermEqLeafBundle D G imageOf) : ResolvedProductEqGrandSupply D G imageOf :=
  B.Product.toProductEqGrandSupply

/-- **R-6c-leaf-7 — the RIGHT grand supply from the bundle. -/
noncomputable def ResolvedTermEqLeafBundle.toRightGrandSupply
    (B : ResolvedTermEqLeafBundle D G imageOf) : ResolvedRightGrandSupply D G imageOf :=
  B.Right.toRightGrandSupply

/-- **R-6c-leaf-7 — the `term_eq` grand supply (6a-11c) from the leaf bundle. -/
noncomputable def ResolvedTermEqLeafBundle.toTermEqGrandSupply
    (B : ResolvedTermEqLeafBundle D G imageOf) : ResolvedTermEqGrandSupply D G imageOf where
  Product := B.Product.toProductEqGrandSupply
  Right := B.Right.toRightGrandSupply
  Inner := B.Inner

/-- **R-6c-leaf-7 — the heart term agreement from the leaf bundle. -/
theorem ResolvedTermEqLeafBundle.term_eqs (B : ResolvedTermEqLeafBundle D G imageOf) :
    ∀ s, D.resolvedSplitChoiceTerm s
      = B.Inner.toStrictSummandSupply.resolvedCoassocQuotientTerm (imageOf s) :=
  B.toTermEqGrandSupply.term_eqs

end GaugeGeometry.QFT.Combinatorial
