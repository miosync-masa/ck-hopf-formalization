import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoproductCoassociativity

/-!
# QFT-R1-body-652 — the PUBLIC stable resolved φ⁴ coproduct coassociativity LAW

Body-651 proved the whole-algebra coassociativity of the concrete φ⁴₄ stable resolved coproduct
`Δᵣˢ = coproduct_resolved_stable_phi4` through the internal names `stableCoassocLeft = stableCoassocRight`.
This body is the thin FINALE: it re-states that terminus in the STANDARD, downstream/paper-facing coassociativity
form

    assoc ∘ (Δᵣˢ ⊗ id) ∘ Δᵣˢ  =  (id ⊗ Δᵣˢ) ∘ Δᵣˢ

as a LITERAL algebra-hom equality (Step 1) and its pointwise instance (Step 2), plus a generator-facing anchor
(Step 3).  Every proof is `change` (definitional unfold of `stableCoassocLeft` / `stableCoassocRight`) + a body-651
term — NO new mathematics, NO `simp` unfolding of the coproduct formula, NO representative recovery re-run.

## Steps
* **Step 1 — the literal AlgHom law.**  `coproduct_resolved_stable_phi4_coassociativity_law`: the two iterated
  coproducts, written out in full (`assoc ∘ (Δᵣˢ ⊗ id) ∘ Δᵣˢ` and `(id ⊗ Δᵣˢ) ∘ Δᵣˢ`), are EQUAL as algebra homs
  `H →ₐ[ℚ] H ⊗ (H ⊗ H)` — `change` to `stableCoassocLeft = stableCoassocRight` + body-651.
* **Step 2 — the pointwise literal law.**  `…_law_apply p`: the same equality applied to any `p`.
* **Step 3 — the generator-facing anchor.**  `…_law_X x`: Step 2 specialized to `MvPolynomial.X x` (a direct
  read; NO representative recovery).

## HALT compliance
NO new mathematics / definition / `structure` / `class` / `instance`; `Quotient.out` / forest / alpha / finite sum
are NOT re-consumed in code; NO `simp` expansion of the coproduct formula (`change` connects definitionally); ZERO
`HEq` / `cast` / graph-data `▸`; ZERO forbidden divergence class in any declaration TYPE; NO `counit` / `antipode` /
`Bialgebra` claim; body-651 and all upstream UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Campaign status
With this body, the **QFT-R1 φ⁴ stable resolved coproduct realization campaign is CLOSED**: the public terminus
`assoc ∘ (Δᵣˢ ⊗ id) ∘ Δᵣˢ = (id ⊗ Δᵣˢ) ∘ Δᵣˢ` is fixed as a downstream/paper-readable theorem.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

/-! ## Step 1 — the literal AlgHom coassociativity law -/

/-- **body-652 (Step 1) — the PUBLIC coassociativity law of `Δᵣˢ`.**  `assoc ∘ (Δᵣˢ ⊗ id) ∘ Δᵣˢ = (id ⊗ Δᵣˢ) ∘ Δᵣˢ`
as an equality of algebra homs `StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH ⊗ (StableResolvedPhi4HopfH ⊗
StableResolvedPhi4HopfH)`.  The literal spelling of body-651's `stableCoassocLeft = stableCoassocRight`
(`change` + the internal terminus). -/
theorem coproduct_resolved_stable_phi4_coassociativity_law :
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ
        StableResolvedPhi4HopfH StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom.comp
      (Algebra.TensorProduct.map coproduct_resolved_stable_phi4
        (AlgHom.id ℚ StableResolvedPhi4HopfH))).comp
      coproduct_resolved_stable_phi4
      = (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
          coproduct_resolved_stable_phi4).comp
        coproduct_resolved_stable_phi4 := by
  change stableCoassocLeft = stableCoassocRight
  exact coproduct_resolved_stable_phi4_coassociative

/-! ## Step 2 — the pointwise literal law -/

/-- **body-652 (Step 2) — the pointwise coassociativity law.**  For every `p`,
`assoc ((Δᵣˢ ⊗ id) (Δᵣˢ p)) = (id ⊗ Δᵣˢ) (Δᵣˢ p)`. -/
theorem coproduct_resolved_stable_phi4_coassociativity_law_apply (p : StableResolvedPhi4HopfH) :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ
        StableResolvedPhi4HopfH StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom
        ((Algebra.TensorProduct.map coproduct_resolved_stable_phi4
          (AlgHom.id ℚ StableResolvedPhi4HopfH)) (coproduct_resolved_stable_phi4 p))
      = (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
          coproduct_resolved_stable_phi4) (coproduct_resolved_stable_phi4 p) := by
  change stableCoassocLeft p = stableCoassocRight p
  exact coproduct_resolved_stable_phi4_coassoc p

/-! ## Step 3 — the generator-facing public anchor -/

/-- **body-652 (Step 3) — the coassociativity law on a generator.**  Step 2 specialized to `MvPolynomial.X x`;
a direct read — NO representative recovery. -/
theorem coproduct_resolved_stable_phi4_coassociativity_law_X (x : StableResolvedPhi4HopfGen) :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ
        StableResolvedPhi4HopfH StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom
        ((Algebra.TensorProduct.map coproduct_resolved_stable_phi4
          (AlgHom.id ℚ StableResolvedPhi4HopfH))
          (coproduct_resolved_stable_phi4 (MvPolynomial.X x)))
      = (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
          coproduct_resolved_stable_phi4) (coproduct_resolved_stable_phi4 (MvPolynomial.X x)) :=
  coproduct_resolved_stable_phi4_coassociativity_law_apply (MvPolynomial.X x)

end GaugeGeometry.QFT.Combinatorial
