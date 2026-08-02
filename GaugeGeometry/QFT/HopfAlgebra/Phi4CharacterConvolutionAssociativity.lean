import GaugeGeometry.QFT.HopfAlgebra.Phi4RegularizedCharacterConvolution

/-!
# QFT-R2-body-658 — character convolution ASSOCIATIVITY (652 coassoc → convolution assoc), + counit/unit frontier

Body-657 assembled the counit-free DIRECT convolution character
`phi4CharacterConvolution f g := (phi4CharacterTensorMul f g).comp coproduct_resolved_stable_phi4`
(the Connes–Kreimer `(f ⋆ g)(x) = mul ∘ (f ⊗ g)(Δᵣˢ x)`).  **657 gave the product; 658 makes the bracket
vanish** — the character convolution is ASSOCIATIVE, `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`, obtained by pushing
body-652's coproduct COASSOCIATIVITY (`coproduct_resolved_stable_phi4_coassociative :
stableCoassocLeft = stableCoassocRight`) through a triple-tensor evaluator.  The proof is **PURELY
STRUCTURAL** — `mul_assoc` + the tensor associator + 652 as a single BLACK-BOX rewrite — with **NO generator
(`MvPolynomial.algHom_ext` / `X g`) expansion and NO forest / `stableForestSum` re-expansion** anywhere.

## Construction

* **Step 1 — triple-tensor evaluators.**  `phi4CharacterTripleTensorMul f g h := lift f (phi4CharacterTensorMul
  g h)` on `H ⊗ (H ⊗ H)` (`x ⊗ (y ⊗ z) ↦ f x * (g y * h z)`), and the LEFT-associated
  `phi4CharacterTripleTensorMulLeft f g h := lift (phi4CharacterTensorMul f g) h` on `(H ⊗ H) ⊗ H`
  (`(x ⊗ y) ⊗ z ↦ f x * g y * h z`).
* **Step 2 — associator compatibility** (the ONLY place `mul_assoc` enters): `tripleMul ∘ assoc = tripleLeft`
  as algebra homs `(H⊗H)⊗H →ₐ A`, by threefold tensor `ext` + `assoc_tmul` + `mul_assoc`.
* **Step 3 — tensor-level convolution factorizations** (tensor `ext'`, NO generators): `phi4CharacterTensorMul
  (f ⋆ g) h = tripleLeft ∘ (Δ ⊗ id)` and `phi4CharacterTensorMul f (g ⋆ h) = tripleMul ∘ (id ⊗ Δ)`.
* **Step 4 — the two nested convolutions as `tripleMul ∘ (iterated coproduct)`**: `(f ⋆ g) ⋆ h = tripleMul ∘
  stableCoassocLeft` and `f ⋆ (g ⋆ h) = tripleMul ∘ stableCoassocRight` (composition-level regrouping via the
  `rfl` `AlgHom.comp_assoc`, unfolding `stableCoassocLeft/Right(Tail)`, and Steps 2–3).
* **Step 5 — HEADLINE**: `phi4CharacterConvolution_assoc` — a single `rw` of 652's coassociativity under the
  common `tripleMul ∘ ·`.
* **Step 6 — regularized specialization**: `phi4RegularizedConvolution_assoc` on three Feynman-rule characters.

## Counit / unit frontier VERDICT (honest — stated, NOT proved)

(i) Character convolution is ASSOCIATIVE (proved here).  (ii) The convolution UNIT is OPEN — no stable counit
`ε` is issued yet, so `f ⋆ ε = f` is NOT available and is NOT claimed.  (iii) NO `Semigroup` / `Monoid` /
`One` / `Mul` / `Coalgebra` instance on the character space is created (associativity is a bare `theorem`, not
an algebraic-structure field).  (iv) The natural next owner is the CANDIDATE counit `ε := MvPolynomial.aeval
(fun _ => (0 : ℚ)) : StableResolvedPhi4HopfH →ₐ[ℚ] ℚ`, recorded below as `phi4StableCounitCandidate` — a PLAIN
`def` with ZERO counit / unit theorems attached: it stays a CANDIDATE until the counit laws AND the
convolution-unit laws are proved (body-659).

## HALT / red lines

652/651 coassociativity is consumed as a BLACK BOX (never reproved).  NO generator (`MvPolynomial.algHom_ext`
/ `X g`) expansion; NO forest / `stableForestSum` / `_of_graph` re-expansion.  NO convolution UNIT
(`f ⋆ ε = f`), NO convolution COMMUTATIVITY, NO antipode, NO counit LAW.  NO `Semigroup` / `Monoid` / `One` /
`Mul` / `Coalgebra` instance; NO reuse of the old `WithConv` / `AntipodeConvolution`.  Target stays at
`CommSemiring A` + `Algebra ℚ A` (no `CommRing` / field).  Every declaration is a `def` / `theorem`; ZERO new
`structure` / `class` / permanent `instance`.  ZERO `cast` / `HEq` / graph-data `▸`; ZERO forbidden divergence
class in any declaration TYPE; ZERO `sorry` / `admit` / `native_decide`.  Bodies ≤657 UNEDITED; axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap

658 (associativity + counit/unit frontier) → 659 (stable counit `ε` + convolution unit `f ⋆ ε = f`) →
660 (Rota–Baxter subtraction) → 661+ (Bogoliubov / counterterm recursion).  HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct BigOperators

set_option linter.unusedVariables false

variable {A : Type*} [CommSemiring A] [Algebra ℚ A]

/-! ## Step 1 — triple tensor evaluators -/

/-- **body-658 (Step 1) — the RIGHT-associated triple-tensor evaluator.**  `lift f (phi4CharacterTensorMul g h)`
on `H ⊗ (H ⊗ H)`: the unique algebra map sending `x ⊗ (y ⊗ z) ↦ f x * (g y * h z)`. -/
noncomputable def phi4CharacterTripleTensorMul (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    StableResolvedPhi4HopfH ⊗[ℚ] (StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH) →ₐ[ℚ] A :=
  Algebra.TensorProduct.lift f (phi4CharacterTensorMul g h) (fun _ _ => Commute.all _ _)

/-- **body-658 (Step 1) — the RIGHT-associated evaluator on a pure tensor.** -/
@[simp] theorem phi4CharacterTripleTensorMul_tmul (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (x y z : StableResolvedPhi4HopfH) :
    phi4CharacterTripleTensorMul f g h (x ⊗ₜ[ℚ] (y ⊗ₜ[ℚ] z)) = f x * (g y * h z) := by
  simp only [phi4CharacterTripleTensorMul, Algebra.TensorProduct.lift_tmul, phi4CharacterTensorMul_tmul]

/-- **body-658 (Step 1) — the LEFT-associated triple-tensor evaluator.**  `lift (phi4CharacterTensorMul f g) h`
on `(H ⊗ H) ⊗ H`: the unique algebra map sending `(x ⊗ y) ⊗ z ↦ f x * g y * h z`. -/
noncomputable def phi4CharacterTripleTensorMulLeft (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    (StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH) ⊗[ℚ] StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  Algebra.TensorProduct.lift (phi4CharacterTensorMul f g) h (fun _ _ => Commute.all _ _)

/-- **body-658 (Step 1) — the LEFT-associated evaluator on a pure tensor.** -/
@[simp] theorem phi4CharacterTripleTensorMulLeft_tmul (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (x y z : StableResolvedPhi4HopfH) :
    phi4CharacterTripleTensorMulLeft f g h ((x ⊗ₜ[ℚ] y) ⊗ₜ[ℚ] z) = f x * g y * h z := by
  simp only [phi4CharacterTripleTensorMulLeft, Algebra.TensorProduct.lift_tmul,
    phi4CharacterTensorMul_tmul]

/-! ## Step 2 — associator compatibility (the ONLY place `mul_assoc` enters) -/

/-- **body-658 (Step 2) — associator compatibility.**  The RIGHT-associated evaluator precomposed with the
tensor associator equals the LEFT-associated evaluator: `tripleMul ∘ assoc = tripleLeft` as algebra homs
`(H ⊗ H) ⊗ H →ₐ A`.  Threefold tensor `ext` reduces to pure tensors `(x ⊗ y) ⊗ z`; `assoc_tmul` reassociates
to `x ⊗ (y ⊗ z)`; the two evaluators give `f x * (g y * h z)` vs `f x * g y * h z`, closed by `mul_assoc`. -/
theorem phi4CharacterTriple_assoc_comp (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    (phi4CharacterTripleTensorMul f g h).comp
        (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
          StableResolvedPhi4HopfH).toAlgHom
      = phi4CharacterTripleTensorMulLeft f g h := by
  apply Algebra.TensorProduct.ext'
  intro a z
  induction a using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.zero_tmul, map_zero]
  | tmul x y =>
      simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
        Algebra.TensorProduct.assoc_tmul, phi4CharacterTripleTensorMul_tmul,
        phi4CharacterTripleTensorMulLeft_tmul, mul_assoc]
  | add p q hp hq =>
      rw [TensorProduct.add_tmul, map_add, map_add, hp, hq]

/-! ## Step 3 — the two tensor-level convolution factorizations (structural, tensor `ext`) -/

/-- **body-658 (Step 3, LEFT) — the tensor-level LEFT convolution factorization.**  Multiplying the convolution
`f ⋆ g` against `h` on a tensor equals the LEFT-associated evaluator precomposed with `Δ ⊗ id`.  Tensor `ext'`
on `a ⊗ b`: both sides reduce to `phi4CharacterTensorMul f g (Δ a) * h b` (LHS via
`phi4CharacterConvolution_apply`, RHS via `map_tmul` + `lift_tmul`).  NO generators. -/
theorem phi4CharacterTensorMul_convolution_left (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterTensorMul (phi4CharacterConvolution f g) h
      = (phi4CharacterTripleTensorMulLeft f g h).comp
          (Algebra.TensorProduct.map coproduct_resolved_stable_phi4
            (AlgHom.id ℚ StableResolvedPhi4HopfH)) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [phi4CharacterTensorMul_tmul, phi4CharacterConvolution_apply, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi4CharacterTripleTensorMulLeft,
    Algebra.TensorProduct.lift_tmul]

/-- **body-658 (Step 3, RIGHT) — the tensor-level RIGHT convolution factorization.**  Multiplying `f` against
the convolution `g ⋆ h` on a tensor equals the RIGHT-associated evaluator precomposed with `id ⊗ Δ`.  Tensor
`ext'` on `a ⊗ b`: both sides reduce to `f a * phi4CharacterTensorMul g h (Δ b)`.  NO generators. -/
theorem phi4CharacterTensorMul_convolution_right (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterTensorMul f (phi4CharacterConvolution g h)
      = (phi4CharacterTripleTensorMul f g h).comp
          (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
            coproduct_resolved_stable_phi4) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  simp only [phi4CharacterTensorMul_tmul, phi4CharacterConvolution_apply, AlgHom.comp_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, phi4CharacterTripleTensorMul,
    Algebra.TensorProduct.lift_tmul]

/-! ## Step 4 — the two nested convolutions as `tripleMul ∘ (iterated coproduct)` -/

/-- **body-658 (Step 4, LEFT) — the LEFT nested convolution factors through `stableCoassocLeft`.**
`(f ⋆ g) ⋆ h = tripleMul ∘ stableCoassocLeft`.  Unfold the outer convolution to `(mul (f⋆g) h) ∘ Δ`, apply
Step 3-left, reassociate the LEFT evaluator via Step 2 (`tripleLeft = tripleMul ∘ assoc`), and recognize
`assoc ∘ (Δ ⊗ id) ∘ Δ = stableCoassocLeft` — all at composition level (`AlgHom.comp_assoc` is `rfl`). -/
theorem phi4CharacterConvolution_assoc_left (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution (phi4CharacterConvolution f g) h
      = (phi4CharacterTripleTensorMul f g h).comp stableCoassocLeft := by
  have hL : phi4CharacterConvolution (phi4CharacterConvolution f g) h
      = (phi4CharacterTensorMul (phi4CharacterConvolution f g) h).comp
          coproduct_resolved_stable_phi4 := rfl
  rw [hL, phi4CharacterTensorMul_convolution_left, ← phi4CharacterTriple_assoc_comp]
  unfold stableCoassocLeft stableCoassocLeftTail
  rfl

/-- **body-658 (Step 4, RIGHT) — the RIGHT nested convolution factors through `stableCoassocRight`.**
`f ⋆ (g ⋆ h) = tripleMul ∘ stableCoassocRight`.  Unfold the outer convolution to `(mul f (g⋆h)) ∘ Δ`, apply
Step 3-right, and recognize `(id ⊗ Δ) ∘ Δ = stableCoassocRight` — all at composition level. -/
theorem phi4CharacterConvolution_assoc_right (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution f (phi4CharacterConvolution g h)
      = (phi4CharacterTripleTensorMul f g h).comp stableCoassocRight := by
  have hR : phi4CharacterConvolution f (phi4CharacterConvolution g h)
      = (phi4CharacterTensorMul f (phi4CharacterConvolution g h)).comp
          coproduct_resolved_stable_phi4 := rfl
  rw [hR, phi4CharacterTensorMul_convolution_right]
  unfold stableCoassocRight stableCoassocRightTail
  rfl

/-! ## Step 5 — HEADLINE: character convolution is ASSOCIATIVE -/

/-- **body-658 (Step 5, HEADLINE) — the stable character convolution is ASSOCIATIVE.**
`(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`.  Both sides factor through the common triple-tensor evaluator `tripleMul` after
the two iterated coproducts (Step 4), which AGREE by body-652's coassociativity
`coproduct_resolved_stable_phi4_coassociative : stableCoassocLeft = stableCoassocRight` — consumed as a single
BLACK-BOX rewrite under `tripleMul ∘ ·`.  PURELY structural: NO generator / forest expansion. -/
theorem phi4CharacterConvolution_assoc (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution (phi4CharacterConvolution f g) h
      = phi4CharacterConvolution f (phi4CharacterConvolution g h) := by
  rw [phi4CharacterConvolution_assoc_left, phi4CharacterConvolution_assoc_right,
    coproduct_resolved_stable_phi4_coassociative]

/-- **body-658 (Step 5, pointwise) — associativity as a pointwise computation rule.** -/
theorem phi4CharacterConvolution_assoc_apply (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (x : StableResolvedPhi4HopfH) :
    phi4CharacterConvolution (phi4CharacterConvolution f g) h x
      = phi4CharacterConvolution f (phi4CharacterConvolution g h) x :=
  AlgHom.congr_fun (phi4CharacterConvolution_assoc f g h) x

/-! ## Step 6 — the regularized-amplitude specialization -/

/-- **body-658 (Step 6) — regularized convolution associativity.**  Associativity of the character convolution
on the three regularized Feynman-rule characters.  NOTE: `phi4RegularizedConvolution` takes TWO amplitudes and
returns a CHARACTER, so associativity is phrased at the CHARACTER level on the three Feynman-rule characters —
NOT as a nested `phi4RegularizedConvolution (phi4RegularizedConvolution …)` (that would be a type error:
it wants amplitudes, not characters). -/
theorem phi4RegularizedConvolution_assoc (ampL ampM ampR : StablePhi4RegularizedAmplitude A) :
    phi4CharacterConvolution
        (phi4CharacterConvolution (phi4RegularizedFeynmanRule ampL) (phi4RegularizedFeynmanRule ampM))
        (phi4RegularizedFeynmanRule ampR)
      = phi4CharacterConvolution (phi4RegularizedFeynmanRule ampL)
          (phi4CharacterConvolution (phi4RegularizedFeynmanRule ampM) (phi4RegularizedFeynmanRule ampR)) :=
  phi4CharacterConvolution_assoc _ _ _

/-! ## Counit / unit frontier — the CANDIDATE counit (NO law claimed) -/

/-- **body-658 (frontier) — the CANDIDATE stable counit** `ε := MvPolynomial.aeval (fun _ => (0 : ℚ))`.
CANDIDATE ONLY — NO counit law and NO convolution-unit law (`f ⋆ ε = f`) is claimed here; that is body-659's
job.  Recorded as a plain `def` so the next body has a named target, with ZERO theorems attached. -/
noncomputable def phi4StableCounitCandidate : StableResolvedPhi4HopfH →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval (fun _ => (0 : ℚ))

end GaugeGeometry.QFT.Combinatorial
