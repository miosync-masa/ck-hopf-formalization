import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductGrandSupply
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightGrandSupply
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEq

/-!
# R-6c-heart-6a-11c — `term_eq` GRAND ASSEMBLER (the heart, from PRODUCT + RIGHT records)

The resolved coassociativity heart — `term_eq` (`resolvedSplitChoiceTerm s = imageWeight (imageOf s)`) —
is closed here from the two grand records: `ResolvedProductEqGrandSupply` (`product_eq`, 6a-11b) and
`ResolvedRightGrandSupply` (`right_eq`, 6a-11a), plus the inner strict-summand supply.

HEART-2's `term_eq_of_factorization` proved `term_eq = product_eq + right_eq` by pure tensor associativity;
this file feeds it the two grand records.  The `right_eq` of `ResolvedRightGrandSupply` targets
`Inner.innerRightTerm`, which is defeq to `(Inner.toStrictSummandSupply).innerRightTerm` — the `T` the
factorization needs.

Per the HALT, no leaf fields are proved; `FullCompatibility` / `coassoc_gen` are NOT reached (only `term_eq`).

Landed:

* `ResolvedTermEqGrandSupply D G imageOf` — `Product` + `Right` + `Inner`;
* `.factorization` — the per-split-choice `ResolvedSplitPhiTermEqFactorization`;
* `.term_eq` / `.term_eqs` — the term agreement (the heart field).

So `term_eq` now flows from ONE top-level record built from PRODUCT + RIGHT.

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

/-- **R-6c-heart-6a-11c — the `term_eq` grand supply.**  The two halves (`product_eq` + `right_eq`) plus the
inner strict-summand supply. -/
structure ResolvedTermEqGrandSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The product factorization record (6a-11b). -/
  Product : ResolvedProductEqGrandSupply D G imageOf
  /-- The right-factor record (6a-11a). -/
  Right : ResolvedRightGrandSupply D G imageOf
  /-- The inner quotient-of-quotient generator supply. -/
  Inner : ResolvedCoassocInnerRightSupply D G

/-- **R-6c-heart-6a-11c — the per-split-choice factorization. -/
noncomputable def ResolvedTermEqGrandSupply.factorization
    (Z : ResolvedTermEqGrandSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedSplitPhiTermEqFactorization D Z.Inner.toStrictSummandSupply imageOf s where
  product_eq := Z.Product.product_eq s
  right_eq := Z.Right.right_eq Z.Inner s

/-- **R-6c-heart-6a-11c — the term agreement (the heart) from the grand record. -/
theorem ResolvedTermEqGrandSupply.term_eq
    (Z : ResolvedTermEqGrandSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    D.resolvedSplitChoiceTerm s
      = Z.Inner.toStrictSummandSupply.resolvedCoassocQuotientTerm (imageOf s) :=
  term_eq_of_factorization (Z.factorization s)

/-- **R-6c-heart-6a-11c — the `∀ s` term agreement (the heart field). -/
theorem ResolvedTermEqGrandSupply.term_eqs
    (Z : ResolvedTermEqGrandSupply D G imageOf) :
    ∀ s, D.resolvedSplitChoiceTerm s
      = Z.Inner.toStrictSummandSupply.resolvedCoassocQuotientTerm (imageOf s) :=
  term_eq_of_factorizations Z.factorization

end GaugeGeometry.QFT.Combinatorial
