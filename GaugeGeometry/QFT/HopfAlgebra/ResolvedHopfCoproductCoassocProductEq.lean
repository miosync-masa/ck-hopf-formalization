import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTensorProd

/-!
# R-6c-heart-5c-1 — `product_eq`, the algebra/Finset side

`product_eq` (heart-2) is

  `resolvedSplitChoiceProduct s = resolvedSelectedOuterTerm (imageOf s) ⊗ₜ
     resolvedForestLeftTerm (imageOf s).quotientForest`,

where `resolvedSplitChoiceProduct s = ∏ γ, localChoiceTerm γ (s.2 γ)` and each `localChoiceTerm` is a
**pure tensor** `aγ ⊗ₜ bγ`:

* `Sum.inl true`  → `X(gen γ) ⊗ₜ 1`     (left primitive);
* `Sum.inl false` → `1 ⊗ₜ X(gen γ)`     (right primitive);
* `Sum.inr B`     → `leftTerm B ⊗ₜ rightTerm B` (forest choice).

So the left/right tensor factors split: `localChoiceTerm γ c = localChoiceLeftFactor γ c ⊗ₜ
localChoiceRightFactor γ c`.  By `resolvedTensorProduct_prod_tmul` (5a-1) the whole product factors,

  `resolvedSplitChoiceProduct s = (∏ γ, leftFactor γ) ⊗ₜ (∏ γ, rightFactor γ)`,

reducing `product_eq` to **two named factor equalities** — the genuine de-contraction content:

* `leftFactorProduct s = resolvedSelectedOuterTerm (imageOf s)`
  (left primitives + promoted forest pieces assemble the selected-outer component product);
* `rightFactorProduct s = resolvedForestLeftTerm (imageOf s).quotientForest`
  (right survivors + remnant pieces assemble the quotient-forest component product).

This file PROVES the pure-algebra reduction (`splitChoiceProduct_eq_factor_tmul`,
`product_eq_of_factors`) and isolates the two factor equalities as obligations (they need the
survivor/remnant/promote generator relations — the de-contraction, still supplied).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The two factor equalities (and `right_eq`,
5c-2) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## The left/right tensor factors of a local choice -/

/-- **R-6c-heart-5c-1 — the left tensor factor of a local choice.**  `X(gen)` on a left primitive,
`1` on a right primitive, `leftTerm B` on a forest choice. -/
noncomputable def ResolvedCoproductProperForestData.localChoiceLeftFactor
    (D : ResolvedCoproductProperForestData) (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    (Bool ⊕ (D.supply γG).ForestIdx) → ResolvedHopfH :=
  Sum.elim (fun b => bif b then MvPolynomial.X (γG.toResolvedHopfGen hCD) else 1)
    (fun B => (D.supply γG).leftTerm B)

/-- **R-6c-heart-5c-1 — the right tensor factor of a local choice.**  `1` on a left primitive,
`X(gen)` on a right primitive, `rightTerm B` on a forest choice. -/
noncomputable def ResolvedCoproductProperForestData.localChoiceRightFactor
    (D : ResolvedCoproductProperForestData) (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    (Bool ⊕ (D.supply γG).ForestIdx) → ResolvedHopfH :=
  Sum.elim (fun b => bif b then 1 else MvPolynomial.X (γG.toResolvedHopfGen hCD))
    (fun B => (D.supply γG).rightTerm B)

/-- A local choice term is the tensor of its left and right factors. -/
theorem ResolvedCoproductProperForestData.localChoiceTerm_eq_tmul
    (D : ResolvedCoproductProperForestData) (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) (c : Bool ⊕ (D.supply γG).ForestIdx) :
    D.localChoiceTerm γG hCD c
      = D.localChoiceLeftFactor γG hCD c ⊗ₜ[ℚ] D.localChoiceRightFactor γG hCD c := by
  rcases c with b | B
  · cases b <;> rfl
  · rfl

/-! ## The factored products -/

/-- **R-6c-heart-5c-1 — the left-factor product.**  The product over the input outer components of their
local-choice left factors — the candidate selected-outer component product. -/
noncomputable def ResolvedCoproductProperForestData.leftFactorProduct
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ResolvedHopfH :=
  ∏ γ ∈ (s.1.1.elements.attach).attach,
    D.localChoiceLeftFactor (γ.1.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ.1) (s.2 γ.1 γ.2)

/-- **R-6c-heart-5c-1 — the right-factor product.**  The product over the input outer components of
their local-choice right factors — the candidate quotient-forest component product. -/
noncomputable def ResolvedCoproductProperForestData.rightFactorProduct
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ResolvedHopfH :=
  ∏ γ ∈ (s.1.1.elements.attach).attach,
    D.localChoiceRightFactor (γ.1.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ.1) (s.2 γ.1 γ.2)

/-- **R-6c-heart-5c-1 — the branch product factors into the two factor products (pure algebra).**
`resolvedSplitChoiceProduct s = leftFactorProduct s ⊗ₜ rightFactorProduct s`, by splitting each pure
tensor and applying `resolvedTensorProduct_prod_tmul`. -/
theorem ResolvedCoproductProperForestData.splitChoiceProduct_eq_factor_tmul
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.resolvedSplitChoiceProduct s
      = D.leftFactorProduct s ⊗ₜ[ℚ] D.rightFactorProduct s := by
  rw [ResolvedCoproductProperForestData.resolvedSplitChoiceProduct,
    Finset.prod_congr rfl (fun γ _ =>
      D.localChoiceTerm_eq_tmul (γ.1.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ.1) (s.2 γ.1 γ.2)),
    resolvedTensorProduct_prod_tmul]
  rfl

/-- **R-6c-heart-5c-1 — `product_eq` from the two factor equalities.**  Given that the left-factor
product is the selected-outer term and the right-factor product is the quotient-forest left term,
`product_eq` follows by the pure-algebra factorization.  The two hypotheses are the genuine
de-contraction obligations (the selected-outer / quotient-forest component classifications). -/
theorem ResolvedCoproductProperForestData.product_eq_of_factors
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (s : ResolvedCoassocSplitChoice D G)
    (hleft : D.leftFactorProduct s = resolvedSelectedOuterTerm (imageOf s))
    (hright : D.rightFactorProduct s = resolvedForestLeftTerm (imageOf s).quotientForest) :
    D.resolvedSplitChoiceProduct s
      = resolvedSelectedOuterTerm (imageOf s) ⊗ₜ[ℚ] resolvedForestLeftTerm (imageOf s).quotientForest := by
  rw [D.splitChoiceProduct_eq_factor_tmul, hleft, hright]

end GaugeGeometry.QFT.Combinatorial
