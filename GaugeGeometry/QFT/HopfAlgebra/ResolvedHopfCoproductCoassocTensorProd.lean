import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTermEq

/-!
# R-6c-heart-5a-1 — the tensor-product factorization of a product of pure tensors

The pure-algebra core of `product_eq` (heart-5), isolated from the de-contraction geometry: a product of
pure tensors `∏ (aᵢ ⊗ₜ bᵢ)` in `ResolvedHopfH ⊗[ℚ] ResolvedHopfH` factors as `(∏ aᵢ) ⊗ₜ (∏ bᵢ)` (the
tensor product of commutative algebras multiplies componentwise).  This reduces `product_eq` to matching
the left-factor product with `resolvedForestLeftTerm selectedOuter` and the right-factor product with
`resolvedForestLeftTerm quotientForest` — the genuine combinatorial/geometric content.

Landed:

* `resolvedTensorProduct_prod_tmul` — `∏ x ∈ s, (a x ⊗ₜ b x) = (∏ x ∈ s, a x) ⊗ₜ (∏ x ∈ s, b x)`.

No facade, no flat term, no `forgetHopf`.  The product partition (left/right factor matching) and the
de-contraction class equalities are the remaining heart-5 work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]

/-- **R-6c-heart-5a-1 — a product of pure tensors factors componentwise.**  In the tensor product of
commutative `ℚ`-algebras, `∏ (aᵢ ⊗ₜ bᵢ) = (∏ aᵢ) ⊗ₜ (∏ bᵢ)` (by `tmul_mul_tmul`). -/
theorem resolvedTensorProduct_prod_tmul {ι : Type*} (s : Finset ι)
    (a b : ι → ResolvedHopfH) :
    (∏ x ∈ s, (a x ⊗ₜ[ℚ] b x)) = (∏ x ∈ s, a x) ⊗ₜ[ℚ] (∏ x ∈ s, b x) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact Algebra.TensorProduct.one_def
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

end GaugeGeometry.QFT.Combinatorial
