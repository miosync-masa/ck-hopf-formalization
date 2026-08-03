import GaugeGeometry.QFT.HopfAlgebra.Phi4CarrierGapBogoliubovDroppedSector

/-!
# QFT-R2-body-665 — the PUBLIC renormalization settlement / campaign closure

**665 freezes the QFT-R2 victory condition BEFORE the antipode campaign.**  It re-publishes the
completed results under paper-facing PUBLIC names and bundles the two main theorems — the CK Birkhoff
factorization `φ₋ ⋆ φ = φ₊` and the exact Figure-1 dropped-sector CK-weight identity — under the SAME
`S`, `φ` in one unified settlement crown.  There is **NO new mathematics**: every declaration reads an
already-proved term (`change` / `exact` only).  Its value is that the two headline results now live
together, provably owned by one Rota–Baxter scheme `S` and one character `φ`.

## Contents (all re-exports — zero new math)
* `phi4StableCK_coproduct_coassociative` — 651's `stableCoassocLeft = stableCoassocRight`.
* `phi4StableCK_birkhoff_factorization` — 663's CROWN `φ₋ ⋆ φ = φ₊`.
* `phi4StableCK_figureOne_droppedSector` — 664b's PAPER HEADLINE dropped-sector identity.
* `phi4StableCK_renormalization_settlement` — the FINAL CROWN: the Birkhoff law AND the Figure-1
  dropped-sector identity, bundled under the same `S`, `φ`.
* `phi4StableCK_figureOne_differs_of_isolated_marginal` — 664b's honest, hypothesised numerical
  criterion (marginal weight `≠ 0` + other dropped weights `= 0` ⇒ comparison `≠` renormalized).

## VERDICT — what QFT-R2 has PROVED, and what remains OPEN

**PROVED (unconditional, axiom-clean `[propext, Classical.choice, Quot.sound]`):**
* stable resolved φ⁴ coproduct COASSOCIATIVITY (`Δᵣˢ`, whole-algebra);
* ASSOCIATIVE UNITAL character convolution (product, bracket, two-sided unit `η`) with the stable
  counit `ε` (`(ε ⊗ id) ∘ Δᵣˢ = includeRight`, `(id ⊗ ε) ∘ Δᵣˢ = includeLeft`);
* the WELL-FOUNDED Bogoliubov recursion on generators (termination carried by the W‴ carrier's
  `IsProperForest` positive complement, NOT the fifth axis);
* GENUINE unital ℚ-algebra counterterm / renormalized CHARACTERS `φ₋, φ₊` (via `aeval`);
* the CK BIRKHOFF FACTORIZATION `φ₋ ⋆ φ = φ₊` on the whole polynomial algebra;
* the EXACT Figure-1 dropped-sector CK-weight identity
  `comparisonValue − φ₊(X gap) = ∑_{W″ ∖ W‴} φ₋(L_F)·φ(R_F)`, with the honest numerical criterion.

**OPEN (the QFT-R3 antipode frontier — a SEPARATE campaign, NOT a "last tile"):**
* the antipode `S_H` (connected grading + reduced-coproduct rank descent + recursion over the whole
  polynomial algebra);
* the convolution-inverse representation `φ₋ = φ ∘ S_H`;
* bundled `Bialgebra` / `HopfAlgebra` instances;
* a momentum-space / dimensional-regularization evaluator inhabiting the Rota–Baxter socket;
* the UNCONDITIONAL nonvanishing of the Figure-1 weight (here it is always a hypothesis).

## HALT compliance
Wrapper only — NO existing proof is re-run (each decl is a single `exact`/`change`).  NO new
`structure` / `class` / `instance`; NO antipode / convolution-inverse-suggestive theorem name; the
comparison scalar is NOT called a "W″ character"; non-cancellation is NOT unconditionalised.  NO
`HEq` / `cast` / graph-data `▸`; NO `sorry` / `admit` / `native_decide`.  Bodies ≤664b UNEDITED;
axiom-clean.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

open scoped Classical

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4CarrierGapBogoliubovDroppedSector`), so the W″ / W‴
carrier types in the Figure-1 settlement elaborate. -/
local instance instPhi4DivergenceMeasureFamily665 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 1 — the public stable coproduct coassociativity law -/

/-- **body-665 (Step 1) — PUBLIC: the stable resolved φ⁴ coproduct is coassociative.**  The two iterated
coproducts agree as algebra homs (paper-facing name for body-651's terminus). -/
theorem phi4StableCK_coproduct_coassociative :
    (stableCoassocLeft : StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3) = stableCoassocRight :=
  coproduct_resolved_stable_phi4_coassociative

/-! ## Step 2 — the public CK Birkhoff factorization law -/

/-- **body-665 (Step 2) — PUBLIC: the CK Birkhoff factorization** `φ₋ ⋆ φ = φ₊` (paper-facing name for
body-663's CROWN). -/
theorem phi4StableCK_birkhoff_factorization
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ
      = phi4BogoliubovRenormalizedCharacter S φ :=
  phi4Bogoliubov_birkhoff_factorization S φ

/-! ## Step 3 — the public Figure-1 dropped-sector discrepancy law -/

/-- **body-665 (Step 3) — PUBLIC: the exact Figure-1 dropped-sector CK-weight identity** (paper-facing
name for body-664b's PAPER HEADLINE). -/
theorem phi4StableCK_figureOne_droppedSector
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
        - phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
      = ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
          phi4CarrierGapBogoliubovForestWeight S φ A :=
  phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector S φ

/-! ## Step 4 — the unified renormalization settlement (FINAL CROWN) -/

/-- **body-665 (Step 4, FINAL CROWN) — the QFT-R2 renormalization settlement.**  Under the SAME
Rota–Baxter scheme `S` and character `φ`: the CK Birkhoff factorization `φ₋ ⋆ φ = φ₊` AND the exact
Figure-1 dropped-sector CK-weight identity hold together.  No new mathematics — the value is that the
two main results are provably owned by one `S`, `φ`. -/
theorem phi4StableCK_renormalization_settlement
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    (phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ
        = phi4BogoliubovRenormalizedCharacter S φ)
      ∧ (phi4CarrierGapWDoublePrimeComparisonValue S φ
            - phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
          = ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
                \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
              phi4CarrierGapBogoliubovForestWeight S φ A) :=
  ⟨phi4Bogoliubov_birkhoff_factorization S φ,
    phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector S φ⟩

/-! ## Step 5 — the public conditional numerical corollary -/

/-- **body-665 (Step 5) — PUBLIC: the honest numerical corollary.**  IF the marginal Figure-1 weight is
nonzero (`houter`) and every OTHER dropped forest weight vanishes (`hvanish`), THEN the W″-support
comparison value differs from the genuine stable renormalized character.  Both hypotheses are EXPLICIT
— the Figure-1 weight's nonvanishing is NOT asserted unconditionally (that is the QFT-R3 frontier). -/
theorem phi4StableCK_figureOne_differs_of_isolated_marginal
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (houter : phi4CarrierGapBogoliubovForestWeight S φ phi4CarrierGapOuterForest ≠ 0)
    (hvanish : ∀ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
        A ≠ phi4CarrierGapOuterForest → phi4CarrierGapBogoliubovForestWeight S φ A = 0) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
      ≠ phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen) :=
  phi4CarrierGap_bogoliubov_difference_of_isolated_marginal S φ houter hvanish

end GaugeGeometry.QFT.Combinatorial
