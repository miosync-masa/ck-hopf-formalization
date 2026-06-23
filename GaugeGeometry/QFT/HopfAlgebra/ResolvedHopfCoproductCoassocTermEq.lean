import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientTerm

/-!
# R-6c-heart-2 — `term_eq` anatomy with the concrete quotient term

With the concrete `imageWeight = resolvedCoassocQuotientTerm` (heart-1), the heart field

  `term_eq : resolvedSplitChoiceTerm s = resolvedCoassocQuotientTerm (imageOf s)`

has a fixed shape on both sides:

* LHS `resolvedSplitChoiceTerm s = assoc(P ⊗ R)` with `P = ∏ localChoiceTerm` (in `ResolvedHopfH ⊗
  ResolvedHopfH`) and `R = (D.supply G).rightTerm s.1` (the outer forest's quotient gen);
* RHS `resolvedCoassocQuotientTerm (imageOf s) = O ⊗ (QL ⊗ IR)` with `O = selectedOuterTerm`,
  `QL = leftTerm(quotientForest)`, `IR = innerRightTerm`.

So `term_eq` decomposes into exactly **two** genuine facts plus a pure tensor assembly:

1. **`product_eq`** (the product-factorization, resolved analogue of `...ProductFactorizationCanonical`):
   `P = O ⊗ QL` — the product over local choices factors into the selected-outer component product
   tensored with the quotient-subforest component product.  This is the combinatorial heart (which
   components go left→outer / forest→quotient); algebra + the de-contraction classification.
2. **`right_eq`** (the forest-right de-contraction, resolved analogue of `...ForestRightHopfHCanonical`):
   `R = IR` — the outer forest's quotient gen equals the inner quotient-of-quotient gen.  This is the
   id-bearing class equality (contracting the whole outer = contracting selectedOuter then its quotient).
3. **assembly**: `assoc((O ⊗ QL) ⊗ R) = O ⊗ (QL ⊗ R)` — pure `assoc_tmul`.

This file PROVES the assembly (`term_eq_of_factorization`), confirming the decomposition is exact, and
isolates `product_eq` / `right_eq` as the two remaining obligations (deferred — the de-contraction
geometry).  After this, `term_eq` is no longer the heart but two named vessels.

Landed:

* `ResolvedCoproductProperForestData.resolvedSplitChoiceProduct` (+ `resolvedSplitChoiceTerm_eq_assoc`,
  rfl) — the branch product `P` named, and `resolvedSplitChoiceTerm = assoc(P ⊗ R)`;
* `ResolvedSplitPhiTermEqFactorization D T imageOf s` — the two obligations `product_eq` / `right_eq`;
* `term_eq_of_factorization` — assembles `term_eq` from the two (pure tensor algebra), PROVED.

No facade, no flat term, no `forgetHopf`; `product_eq` / `right_eq` (the de-contraction geometry) are
the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-heart-2 — the branch product `P`.**  The product over local choices that forms the left
factor of `resolvedSplitChoiceTerm` (before the associator), in `ResolvedHopfH ⊗ ResolvedHopfH`. -/
noncomputable def ResolvedCoproductProperForestData.resolvedSplitChoiceProduct
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  ∏ γ ∈ (s.1.1.elements.attach).attach,
    D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ.1) (s.2 γ.1 γ.2)

/-- `resolvedSplitChoiceTerm` as the associator applied to `P ⊗ R` (the named product ⊗ the outer
quotient gen).  Definitional. -/
theorem ResolvedCoproductProperForestData.resolvedSplitChoiceTerm_eq_assoc
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.resolvedSplitChoiceTerm s =
      (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
        (D.resolvedSplitChoiceProduct s ⊗ₜ[ℚ] (D.supply G).rightTerm s.1) := rfl

/-- **R-6c-heart-2 — the term-agreement factorization obligations.**  For a split choice `s` and a
candidate image `imageOf s`, the two genuine facts that imply the term agreement: the product
factorization (`product_eq`) and the forest-right de-contraction (`right_eq`).  These are the resolved
analogues of the flat canonical lemmas `...ProductFactorizationCanonical` / `...ForestRightHopfHCanonical`
— left as obligations here (the de-contraction geometry). -/
structure ResolvedSplitPhiTermEqFactorization (D : ResolvedCoproductProperForestData)
    {G : ResolvedFeynmanGraph} (T : ResolvedQuotientStrictSummandSupply D G)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- Product factorization: the branch product factors into selected-outer ⊗ quotient-subforest. -/
  product_eq : D.resolvedSplitChoiceProduct s
    = resolvedSelectedOuterTerm (imageOf s) ⊗ₜ[ℚ] resolvedForestLeftTerm (imageOf s).quotientForest
  /-- Forest-right de-contraction: the outer quotient gen equals the inner quotient-of-quotient gen. -/
  right_eq : (D.supply G).rightTerm s.1 = T.innerRightTerm (imageOf s)

/-- **R-6c-heart-2 — assemble `term_eq` from the factorization (PROVED).**  Given the product
factorization and the forest-right de-contraction, the term agreement `resolvedSplitChoiceTerm s =
resolvedCoassocQuotientTerm (imageOf s)` follows by pure tensor associativity (`assoc_tmul`).  This
confirms the decomposition is exact: `term_eq` reduces to `product_eq` + `right_eq`. -/
theorem term_eq_of_factorization {D : ResolvedCoproductProperForestData}
    {G : ResolvedFeynmanGraph} {T : ResolvedQuotientStrictSummandSupply D G}
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G}
    (F : ResolvedSplitPhiTermEqFactorization D T imageOf s) :
    D.resolvedSplitChoiceTerm s = T.resolvedCoassocQuotientTerm (imageOf s) := by
  rw [D.resolvedSplitChoiceTerm_eq_assoc, F.product_eq, F.right_eq]
  simp only [ResolvedQuotientStrictSummandSupply.resolvedCoassocQuotientTerm,
    ResolvedQuotientStrictSummandSupply.strictSummandTerm,
    AlgEquiv.coe_algHom, Algebra.TensorProduct.assoc_tmul]

/-- **R-6c-heart-2 — the `∀ s` term agreement from a factorization family.**  A per-split-choice
factorization family yields the full `term_eq` (the heart field), against the concrete quotient-term
image weight. -/
theorem term_eq_of_factorizations {D : ResolvedCoproductProperForestData}
    {G : ResolvedFeynmanGraph} {T : ResolvedQuotientStrictSummandSupply D G}
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (F : ∀ s, ResolvedSplitPhiTermEqFactorization D T imageOf s) :
    ∀ s, D.resolvedSplitChoiceTerm s = T.resolvedCoassocQuotientTerm (imageOf s) :=
  fun s => term_eq_of_factorization (F s)

end GaugeGeometry.QFT.Combinatorial
