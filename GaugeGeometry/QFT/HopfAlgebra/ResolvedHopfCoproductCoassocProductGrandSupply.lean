import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductEqAssembly

/-!
# R-6c-heart-6a-11b — PRODUCT factor grand supply (one record → `product_eq`)

Mirror of the RIGHT grand supply (6a-11a) for the OTHER half of `term_eq`: this collects all leaf
hypotheses of 5c-1i's `product_eq_of_region_data` into one top-level record, so `product_eq` flows from a
single `ResolvedProductEqGrandSupply`.

Together with `ResolvedRightGrandSupply` (6a-11a), the two records will assemble `term_eq` (= `product_eq`
+ `right_eq`) — the heart of the resolved coassociativity.

Per the HALT, none of the leaf fields are proved; no connection to `right_eq` yet; remnant containments
untouched.

Landed:

* `ResolvedProductEqGrandSupply D G imageOf` — `R` / `M` + the region/disjoint/gen/connector fields;
* `.product_eq` — the branch product factorization (via `product_eq_of_region_data`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-11b — the product-factor grand supply.**  All leaf hypotheses of
`product_eq_of_region_data` (5c-1i), collected into one record. -/
structure ResolvedProductEqGrandSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right-survivor supply. -/
  R : ResolvedRightSurvivorSupply D G
  /-- The remnant component supply. -/
  M : ResolvedRemnantComponentSupply D G
  /-- Promoted-component pairwise disjointness (forest region). -/
  hPD : ∀ s : ResolvedCoassocSplitChoice D G,
    (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}).PairwiseDisjoint
      s.promotedComponentElements
  /-- Left / promoted disjointness. -/
  hLP : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
      ((resolvedPromotedOfSupply D G).promotedOf s).elements
  /-- Survivor component injectivity. -/
  survivorInj : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ s.rightComponents.attach, ∀ γ₂ ∈ s.rightComponents.attach,
      R.survivorComponent s γ₁ = R.survivorComponent s γ₂ → γ₁ = γ₂
  /-- Survivor component generator equality. -/
  survivorGen : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
    resolvedComponentGenTerm (R.survivorComponent s γ) = resolvedComponentGenTerm γ.1.1
  /-- Remnant component injectivity. -/
  remnantInj : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ s.forestComponents.attach, ∀ γ₂ ∈ s.forestComponents.attach,
      M.remnantComponent s (s.forestComponentOccurrence γ₁)
        = M.remnantComponent s (s.forestComponentOccurrence γ₂) → γ₁ = γ₂
  /-- Remnant component generator equality. -/
  remnantGen : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents}),
    resolvedComponentGenTerm (M.remnantComponent s (s.forestComponentOccurrence γ))
      = D.rightFactorOf s γ.1
  /-- Cross-disjointness of remnants and right-survivors. -/
  hCross : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- Element-level disjointness of remnants and right-survivors. -/
  hDisj : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements
  /-- The selected-outer term connector. -/
  hSel : ∀ s : ResolvedCoassocSplitChoice D G,
    resolvedSelectedOuterTerm (imageOf s)
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
  /-- The quotient-forest term connector. -/
  hQuot : ∀ s : ResolvedCoassocSplitChoice D G,
    resolvedForestLeftTerm ((M.remnantForest s).union (R.rightSurvivorForest s) (hCross s))
      = resolvedForestLeftTerm (imageOf s).quotientForest

/-- **R-6c-heart-6a-11b — the branch product factorization from the grand record. -/
theorem ResolvedProductEqGrandSupply.product_eq
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (Q : ResolvedProductEqGrandSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G) :
    D.resolvedSplitChoiceProduct s
      = resolvedSelectedOuterTerm (imageOf s) ⊗ₜ[ℚ] resolvedForestLeftTerm (imageOf s).quotientForest :=
  product_eq_of_region_data Q.R Q.M imageOf s (Q.hPD s) (Q.hLP s) (Q.survivorInj s) (Q.survivorGen s)
    (Q.remnantInj s) (Q.remnantGen s) (Q.hCross s) (Q.hDisj s) (Q.hSel s) (Q.hQuot s)

end GaugeGeometry.QFT.Combinatorial
