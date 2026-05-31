import GaugeGeometry.QFT.HopfAlgebra.Bialgebra
import GaugeGeometry.QFT.HopfAlgebra.Antipode
import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Antipode via the convolution ring (Track D-core-Cut2)

The convolution wrapper layer for the forest antipode.  `WithConv (HopfH →ₗ[ℚ] HopfH)`
is a (non-commutative) `Ring` given only `[Coalgebra ℚ HopfH]` (Mathlib
`LinearMap.convRing`) — it does **not** require the full `HopfAlgebra` structure,
so there is no circularity with the right antipode axiom we are trying to prove.
The coalgebra is supplied by `instCoalgebraHopfHStrictForest`, gated on the
coassociativity facade `[CoassocStrictForestH58Ready]` (now itself synthesizable
from the two boundary facades + the power-counting reflection, but kept abstract
here).

This file establishes the **convolution restatement** of the existing left
antipode axiom:

* `convS * convId = 1`  (the unconditional left axiom H6.6b, recast in `WithConv`),

and the **unit-uniqueness deduction**:

* if `convId` is a unit, then `convId * convS = 1`  (the right axiom).

The remaining mathematical kernel is therefore isolated as `IsUnit convId`
(equivalently, local nilpotency of `convId - 1` on the connected-graded carrier);
the explicit nested-forest cancellation of `AntipodeForestRightCoreIdentity` is
no longer the target.  Building `IsUnit convId` (geometric series on the forest
filtration) and bridging `convId * convS = 1` back to the per-generator core
identity are deferred to later cuts.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

open WithConv
open scoped TensorProduct

-- Ambient power-counting environment (same block as `Coproduct`/`Coassoc`/
-- `Bialgebra`/`HopfAlgebra`): `HopfH`, `coproduct_strict_forest`, `antipode_forest`
-- and the `Coalgebra ℚ HopfH` instance are all defined under these.
variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
         [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- The endomorphism carrier of the convolution ring `WithConv (HopfH →ₗ[ℚ] HopfH)`. -/
abbrev HopfHEnd := HopfH →ₗ[ℚ] HopfH

/-- `LinearMap.id` as an element of the convolution ring. -/
noncomputable def convId : WithConv HopfHEnd :=
  WithConv.toConv (LinearMap.id : HopfH →ₗ[ℚ] HopfH)

/-- The forest antipode `antipode_forest` as an element of the convolution ring. -/
noncomputable def convS : WithConv HopfHEnd :=
  WithConv.toConv antipode_forest

-- The coassociativity facade is needed only by the theorems below (it supplies
-- `Coalgebra ℚ HopfH`, hence the convolution `Ring` structure on `WithConv HopfHEnd`).
variable [CoassocStrictForestH58Ready]

/-- **Cut2 — the left antipode axiom as a convolution left inverse.**
The unconditional left axiom H6.6b
(`mul_antipode_rTensor_coproduct_strict_forest`,
`mul' ∘ (S ⊗ id) ∘ Δ = η ∘ ε`) is exactly the statement `convS * convId = 1`
in `WithConv (HopfH →ₗ[ℚ] HopfH)`: convolution multiplication unfolds to
`mul' ∘ map _ _ ∘ comul`, the `comul`/`counit` of `instCoalgebraHopfHStrictForest`
are `coproduct_strict_forest.toLinearMap`/`counit.toLinearMap`, and
`map antipode_forest id = antipode_forest.rTensor HopfH`. -/
theorem convS_mul_convId_eq_one : convS * convId = (1 : WithConv HopfHEnd) := by
  unfold convS convId
  rw [LinearMap.convMul_def, LinearMap.convOne_def]
  exact congrArg WithConv.toConv mul_antipode_rTensor_coproduct_strict_forest

/-- **Cut2 — the right axiom from unit-uniqueness.**  Given that `convId` is a
unit of the convolution ring, the left inverse `convS` is its two-sided inverse,
so `convId * convS = 1` (the right antipode axiom).  This isolates the remaining
mathematical content as `IsUnit convId`. -/
theorem convId_mul_convS_eq_one_of_isUnit (hUnit : IsUnit convId) :
    convId * convS = (1 : WithConv HopfHEnd) := by
  obtain ⟨u, hu⟩ := hUnit
  have hSu : convS * (u : WithConv HopfHEnd) = 1 := by
    rw [hu]; exact convS_mul_convId_eq_one
  have hSinv : convS = (↑u⁻¹ : WithConv HopfHEnd) := by
    calc convS = convS * ((u : WithConv HopfHEnd) * ↑u⁻¹) := by
                rw [u.mul_inv, mul_one]
      _ = (convS * (u : WithConv HopfHEnd)) * ↑u⁻¹ := by rw [mul_assoc]
      _ = (↑u⁻¹ : WithConv HopfHEnd) := by rw [hSu, one_mul]
  rw [← hu, hSinv, u.mul_inv]

/-! ## Track D-core-Cut3a — local nilpotency foundations

`reducedConv := convId - 1` is the augmentation part `id - η∘ε` of `convId` in
the convolution ring.  These lemmas control its action on the unit and on
generators (the primitive part of the coproduct), the base ingredients for the
local-nilpotency strong induction `reducedConv_pow_gen_eq_zero`. -/

/-- The augmentation part `id - η∘ε` of `convId`. -/
noncomputable def reducedConv : WithConv HopfHEnd := convId - 1

/-- Convolution subtraction is pointwise. -/
private theorem withConv_sub_apply (f g : WithConv HopfHEnd) (x : HopfH) :
    (f - g) x = f x - g x := by
  show (f - g).ofConv x = f.ofConv x - g.ofConv x
  rw [ofConv_sub, LinearMap.sub_apply]

/-- Convolution multiplication applied to `1` factorizes, since `Δ 1 = 1 ⊗ 1`. -/
private theorem withConv_mul_apply_one (f h : WithConv HopfHEnd) :
    (f * h) (1 : HopfH) = f 1 * h 1 := by
  rw [LinearMap.convMul_apply]
  rw [show (Coalgebra.comul (R := ℚ) (1 : HopfH)) = (1 : HopfH ⊗[ℚ] HopfH) from
        coproduct_strict_forest_one,
      Algebra.TensorProduct.one_def, TensorProduct.map_tmul, LinearMap.mul'_apply]

/-- `reducedConv` acts as `x ↦ x - ε(x)·1`.  Both `convId x = x` and
`(1 : WithConv) x = algebraMap ℚ HopfH (counit x)` (`convOne_apply`) hold
definitionally, so the pointwise subtraction is exactly the claim. -/
private theorem reducedConv_apply (x : HopfH) :
    reducedConv x = x - algebraMap ℚ HopfH (counit x) :=
  withConv_sub_apply convId 1 x

/-- `reducedConv 1 = 0` — the unit is grouplike (counit-`1`). -/
@[simp] theorem reducedConv_one : reducedConv (1 : HopfH) = 0 := by
  rw [reducedConv_apply, counit_one, map_one, sub_self]

/-- `reducedConv (X g) = X g` — generators are primitive (counit-`0`). -/
@[simp] theorem reducedConv_gen (g : HopfGen) :
    reducedConv (MvPolynomial.X g) = MvPolynomial.X g := by
  rw [reducedConv_apply, counit_X, map_zero, sub_zero]

/-- Every positive convolution power of `reducedConv` annihilates the unit:
`reducedConv 1 = 0`, so the product factorizes to `0`. -/
theorem reducedConv_pow_one_eq_zero {n : ℕ} (hn : 0 < n) :
    ((reducedConv ^ n : WithConv HopfHEnd)) (1 : HopfH) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [pow_succ', withConv_mul_apply_one, reducedConv_one, zero_mul]

/-- **Track D-core-Cut3b — local nilpotency of `reducedConv` on generators.**
`reducedConv^n` annihilates `X g` once `n` exceeds the edge count of `g` by more
than one.  Strong induction on edge count: expanding `reducedConv * reducedConv^k`
over the generator coproduct (primitive part + proper-forest sum), the two
primitive terms vanish (`reducedConv 1 = 0`, `reducedConv^k 1 = 0`), and every
proper-forest summand has right tensor factor `gen (right A)` with strictly fewer
edges (`antipodeForestRight_internalEdges_card_lt`), killed by the induction
hypothesis.  The `+ 1` slack accommodates `0`-edge (primitive) generators, which
need power `2`.  This is the kernel that yields `IsUnit convId`. -/
theorem reducedConv_pow_gen_eq_zero (g : HopfGen) {n : ℕ}
    (h : (repG g).toFeynmanGraph.internalEdges.card + 1 < n) :
    ((reducedConv ^ n : WithConv HopfHEnd)) (MvPolynomial.X g) = 0 := by
  classical
  suffices H : ∀ m : ℕ, ∀ g : HopfGen,
      (repG g).toFeynmanGraph.internalEdges.card = m →
      ∀ n, m + 1 < n →
        ((reducedConv ^ n : WithConv HopfHEnd)) (MvPolynomial.X g) = 0 by
    exact H _ g rfl n h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro g hgm n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : 0 < k := by omega
    rw [pow_succ', LinearMap.convMul_apply,
        show (Coalgebra.comul (R := ℚ) (MvPolynomial.X g))
            = coproduct_strict_forest (MvPolynomial.X g) from rfl,
        coproduct_strict_forest_X_canonicalBody_eq g]
    simp only [map_add, map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [show ((reducedConv ^ k : WithConv HopfHEnd)).ofConv (1 : HopfH) = 0
          from reducedConv_pow_one_eq_zero hk,
        show (reducedConv : WithConv HopfHEnd).ofConv (1 : HopfH) = 0
          from reducedConv_one,
        mul_zero, zero_mul, add_zero, zero_add]
    refine Finset.sum_eq_zero (fun A hA => ?_)
    have hAprop := (mem_forestCoproductProperForestIndex g A).mp hA
    rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1,
        TensorProduct.map_tmul, LinearMap.mul'_apply]
    have hrlt : (repG (FeynmanGraph.admissibleForestRightWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1)
          ).toFeynmanGraph.internalEdges.card < m := by
      rw [← hgm]; exact antipodeForestRight_internalEdges_card_lt g A hA
    rw [show ((reducedConv ^ k : WithConv HopfHEnd)).ofConv
            (gen (FeynmanGraph.admissibleForestRightWithCanonicalStars
              (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1)) = 0
          from ih _ hrlt _ rfl k (by omega),
        mul_zero]

/-- **Track D-core-Cut4-1 — generic remainder lemma.**  For *any* convolution
endomorphism `F`, multiplying on the right by a high enough power of `reducedConv`
annihilates a generator: `(F * reducedConv^k)(X g) = 0` once `k > edgeCount g + 1`.
One-shot expansion of the convolution over the generator coproduct (no induction):
every right tensor factor of `Δ (X g)` (the unit, `X g` itself, and each
`gen (right A)`) is a generator of edge count `< k`, hence killed by `reducedConv^k`
via `reducedConv_pow_one_eq_zero` / `reducedConv_pow_gen_eq_zero`.  Used with
`F := convId * convS - 1` to push the right antipode axiom through generator-wise. -/
private theorem withConv_mul_reducedConv_pow_gen_eq_zero
    (F : WithConv HopfHEnd) (g : HopfGen) {k : ℕ}
    (hk : (repG g).toFeynmanGraph.internalEdges.card + 1 < k) :
    ((F * reducedConv ^ k : WithConv HopfHEnd)) (MvPolynomial.X g) = 0 := by
  classical
  rw [LinearMap.convMul_apply,
      show (Coalgebra.comul (R := ℚ) (MvPolynomial.X g))
          = coproduct_strict_forest (MvPolynomial.X g) from rfl,
      coproduct_strict_forest_X_canonicalBody_eq g]
  simp only [map_add, map_sum, TensorProduct.map_tmul, LinearMap.mul'_apply]
  rw [show ((reducedConv ^ k : WithConv HopfHEnd)).ofConv (1 : HopfH) = 0
        from reducedConv_pow_one_eq_zero (by omega),
      show ((reducedConv ^ k : WithConv HopfHEnd)).ofConv (gen g) = 0
        from reducedConv_pow_gen_eq_zero g hk,
      mul_zero, mul_zero, add_zero, zero_add]
  refine Finset.sum_eq_zero (fun A hA => ?_)
  have hAprop := (mem_forestCoproductProperForestIndex g A).mp hA
  rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
  have hrlt : (repG (FeynmanGraph.admissibleForestRightWithCanonicalStars
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1)
        ).toFeynmanGraph.internalEdges.card
      < (repG g).toFeynmanGraph.internalEdges.card :=
    antipodeForestRight_internalEdges_card_lt g A hA
  rw [show ((reducedConv ^ k : WithConv HopfHEnd)).ofConv
          (gen (FeynmanGraph.admissibleForestRightWithCanonicalStars
            (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAprop.1)) = 0
        from reducedConv_pow_gen_eq_zero _ (by omega),
      mul_zero]

/-- Pure ring lemma: if `P * (1 + N) = 0` then `P = P * N ^ (2 j)` for all `j`.
From `P * (1 + N) = 0` we get `P * N = -P`, hence `P * N ^ 2 = P`, and the even
powers stabilize.  (Stated for a general noncommutative `Ring`; no `ring` tactic,
which would require commutativity.) -/
private theorem self_eq_mul_pow_of_mul_one_add_eq_zero {R : Type*} [Ring R] {P N : R}
    (h : P * (1 + N) = 0) (j : ℕ) : P = P * N ^ (2 * j) := by
  have h2 : P + P * N = 0 := by
    have hh := h; rwa [mul_add, mul_one] at hh
  have hPN : P * N = -P := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2
  have hN2 : P * N ^ 2 = P := by
    rw [pow_two, ← mul_assoc, hPN, neg_mul, hPN, neg_neg]
  induction j with
  | zero => simp
  | succ j ih =>
    have he : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [he, pow_add, ← mul_assoc, ← ih, hN2]

/-- **Track D-core-Cut4-2 — right antipode axiom on generators (P-trick).**
`(convId * convS)(X g) = 1 (X g)` for every generator.  Set `P := convId*convS - 1`;
the left axiom (`convS * convId = 1`) gives `P * convId = 0`, hence (with
`convId = 1 + reducedConv`) `P = P * reducedConv ^ (2 j)` for all `j`; taking `j`
large and applying the generic remainder lemma kills `P (X g)`.  No explicit
forest cancellation, no global inverse — only the local nilpotency of `reducedConv`. -/
private theorem convId_mul_convS_apply_gen_eq_one (g : HopfGen) :
    ((convId * convS : WithConv HopfHEnd)) (MvPolynomial.X g)
      = (1 : WithConv HopfHEnd) (MvPolynomial.X g) := by
  set P : WithConv HopfHEnd := convId * convS - 1 with hP
  have hPconvId : P * convId = 0 := by
    rw [hP, sub_mul, one_mul, mul_assoc, convS_mul_convId_eq_one, mul_one, sub_self]
  have hsum : (1 : WithConv HopfHEnd) + reducedConv = convId := by
    unfold reducedConv; abel
  have hPadd : P * (1 + reducedConv) = 0 := by rw [hsum]; exact hPconvId
  have hPj := self_eq_mul_pow_of_mul_one_add_eq_zero hPadd
    ((repG g).toFeynmanGraph.internalEdges.card + 1)
  have hPzero : (P : WithConv HopfHEnd) (MvPolynomial.X g) = 0 := by
    rw [hPj]
    exact withConv_mul_reducedConv_pow_gen_eq_zero P g (by omega)
  rw [hP, withConv_sub_apply] at hPzero
  exact sub_eq_zero.mp hPzero

/-- **Track D-core-Cut4-3.**  LinearMap-applied generator form of the right
antipode axiom, bridged from the WithConv equality
`convId_mul_convS_apply_gen_eq_one`.  Both sides are *definitionally* the WithConv
applications `(convId * convS) (X g)` and `(1) (X g)` (`map id S = lTensor S`,
`comul = coproduct_strict_forest.toLinearMap`, `counit = counit.toLinearMap`),
so the equality is the same proposition up to `rfl`. -/
private theorem mul_antipode_lTensor_coproduct_strict_forest_X (g : HopfGen) :
    ((LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.lTensor HopfH).comp coproduct_strict_forest.toLinearMap))
        (MvPolynomial.X g)
      = ((Algebra.linearMap ℚ HopfH).comp counit.toLinearMap) (MvPolynomial.X g) :=
  convId_mul_convS_apply_gen_eq_one g

/-- AlgHom packaging of the right-axiom LHS (`id ⊗ S`). -/
private noncomputable def rightAxiomLHSAlg : HopfH →ₐ[ℚ] HopfH :=
  (Algebra.TensorProduct.lmul' ℚ).comp
    ((Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) antipodeAlgHom_forest).comp
      coproduct_strict_forest)

private theorem rightAxiomLHSAlg_eq :
    rightAxiomLHSAlg = (Algebra.ofId ℚ HopfH).comp counit := by
  refine MvPolynomial.algHom_ext (fun g => ?_)
  unfold rightAxiomLHSAlg
  have h := mul_antipode_lTensor_coproduct_strict_forest_X g
  simpa [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply] using h

noncomputable instance AntipodeStrictForestRightReady_ofConvolution :
    AntipodeStrictForestRightReady where
  mul_antipode_lTensor_coproduct_strict_forest := by
    have hLM := congrArg AlgHom.toLinearMap rightAxiomLHSAlg_eq
    simpa [rightAxiomLHSAlg, AlgHom.comp_toLinearMap, Algebra.TensorProduct.toLinearMap_map,
      TensorProduct.AlgebraTensorModule.map_eq, LinearMap.lTensor_def,
      Algebra.TensorProduct.lmul'_toLinearMap] using hLM

end GaugeGeometry.QFT.Combinatorial
