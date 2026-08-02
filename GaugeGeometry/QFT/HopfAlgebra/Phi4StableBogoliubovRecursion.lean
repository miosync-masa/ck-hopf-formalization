import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovRank

/-!
# QFT-R2-body-661b — the well-founded stable Bogoliubov GENERATOR recursion

**661b realizes the well-founded stable Bogoliubov GENERATOR recursion via `WellFounded.fix` on
661a's rank:** the preparation step
`B_φ(x) = φ(X x) + ∑_{F ∈ W‴(rep x)} (∏_{γ ∈ F} φ₋(component γ)) · φ(rightTerm F)`, the counterterm
`φ₋(x) = −R(B_φ(x))`, the renormalized `φ₊(x) = (1 − R)(B_φ(x))`, together with the one-step unfolding
equations.  The recursive calls land **ONLY** on the strictly-lower-rank LEFT component generators
(661a's `stableForestComponent_rank_lt`); the quotient / right factor `stableForestRightTerm` is **NOT**
recursed.  This is **generator-valued** — NO character `φ₋` / `φ₊ : H →ₐ B` is issued yet (that is 662);
here everything is a bare `StableResolvedPhi4HopfGen → B`.

**660's socket `b` now receives a REAL prepared value `B_φ(x)`.**  Body-660 built the weight −1
Rota–Baxter subtraction vessel with `phi4CountertermValue S b = −R b` and
`phi4RenormalizedValue S b = b + (−R b)` over a bare prepared-value SOCKET `b`; 661b feeds the honest
Bogoliubov preparation `B_φ(x)` into that socket.

## Contents
* `phi4BogoliubovPreparationStep` — the lower-rank callback body: `φ(X x)` plus the W‴ forest sum whose
  left factor is the `∏` of the recursive counterterm values on the strictly-lower-rank components.
* `phi4BogoliubovCountertermGen` — `WellFounded.fix` of `x ↦ −R(preparation x)` along 661a's rank.
* `phi4BogoliubovPreparationGen` / `phi4BogoliubovRenormalizedGen` — the unfolded preparation `B_φ` and
  the renormalized `(1 − R)(B_φ)`.
* the one-step unfolding equations (HEADLINEs) and the SIGN-HONEST decomposition
  `preparation + counterterm = renormalized`.

## HALT compliance
661a rank + descent, 660 Rota–Baxter, 651 representative recovery, 629 coproduct summand are consumed as
BLACK BOXES.  The rank descent is NOT re-proved; the recursion does NOT recurse into the quotient /
right factor.  NO counterterm / renormalized CHARACTER `φ₋` / `φ₊ : H →ₐ B` (that is 662); everything is
generator-valued.  NO antipode, NO Laurent / real integral.  The decomposition is stated SIGN-HONESTLY
(`preparation + counterterm = renormalized`, since `counterterm = −R(prep)` and
`renorm = prep + counterterm`).  NO `native_decide` / `Lean.ofReduceBool`; NO `HEq` / `cast` /
graph-data `▸` (only `rfl` / `congrArg` / `rw` / `WellFounded.fix_eq`, and a Prop-level `congrArg` on the
rank equality).  NO forbidden divergence class in any declaration TYPE.  NO `sorry` / `admit`.  ZERO new
`structure` / `class` / permanent `instance` (only a file-scoped `local instance` re-exposing the
existing divergence family).  Bodies ≤661a UNEDITED; axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).

## Roadmap
661a rank + descent → 661b `WellFounded.fix` recursion + Bogoliubov preparation / counterterm /
renormalized unfolding (THIS FILE) → 662 `aeval` `φ₋` / `φ₊` characters → 663 `φ₋ ⋆ φ = φ₊` →
664 Figure-1 dropped-term → renormalization weight + HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4StableBogoliubovRank`), so the W‴ carrier types in
the recursion elaborate. -/
local instance instPhi4DivergenceMeasureFamily661b : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 1 — the preparation step (lower-rank callback) -/

/-- **body-661b (Step 1) — the Bogoliubov preparation step** `B_φ(x)`.  Given the character `φ` and a
lower-rank callback `rec` (supplied later by `WellFounded.fix`), the prepared value is `φ(X x)` plus the
W‴ forest sum over `rep x`: for each live carrier forest `F`, the left factor is the product over the
components `γ ∈ F` of the recursive counterterm value on the component's stable generator, and the right
factor is `φ` of the contraction right term.  **The recursive `rec` calls land ONLY on the strictly-
lower-rank LEFT component generators** (661a `stableForestComponent_rank_lt`); the right factor is NOT
recursed. -/
noncomputable def phi4BogoliubovPreparationStep
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen)
    (rec : ∀ y, stablePhi4GeneratorRank y < stablePhi4GeneratorRank x → B) : B :=
  φ (MvPolynomial.X x)
    + ∑ F ∈ (phi4WTriplePrimeIndex (stablePhi4ResolvedRep x)).attach,
        (∏ γ ∈ F.1.elements.attach,
            rec ((stableLocalBoundaryCompletedGraph γ.1).toStableResolvedPhi4HopfGen
                  (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ.1
                    (F.1.isConnectedDivergent γ.1 γ.2))
                  (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ.1
                    (stablePhi4ResolvedRep_stableBoundaryIds x)))
              (by
                have hxeq : stablePhi4GeneratorRank x
                    = stablePhi4GeneratorRank ((stablePhi4ResolvedRep x).toStableResolvedPhi4HopfGen
                        (stablePhi4ResolvedRep_isConnectedDivergent x)
                        (stablePhi4ResolvedRep_stableBoundaryIds x)) :=
                  congrArg stablePhi4GeneratorRank (stablePhi4ResolvedRep_gen x)
                rw [hxeq]
                exact stableForestComponent_rank_lt (stablePhi4ResolvedRep x)
                  (stablePhi4ResolvedRep_isConnectedDivergent x)
                  (stablePhi4ResolvedRep_stableBoundaryIds x) F.1 F.2 γ.1 γ.2))
          * φ (stableForestRightTerm F.1
                (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) F.1)
                (phi4WTriplePrimeCanonicalSupply.hCD (stablePhi4ResolvedRep x) F.1 F.2)
                (stableResolvedBoundaryIds_contractWithStars F.1
                  (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) F.1)
                  (stablePhi4ResolvedRep_stableBoundaryIds x)))

/-! ## Step 2 — the well-founded counterterm recursion -/

/-- **body-661b (Step 2) — the well-founded stable counterterm generator** `φ₋(x) = −R(B_φ(x))`.  The
`WellFounded.fix` of `x ↦ −R(preparation x)` along 661a's rank (`InvImage.wf stablePhi4GeneratorRank`
of `Nat.lt`).  The `rec` supplied by `WellFounded.fix` has type
`∀ y, InvImage Nat.lt stablePhi4GeneratorRank y x → B`, which reduces definitionally to
`∀ y, stablePhi4GeneratorRank y < stablePhi4GeneratorRank x → B` — matching the preparation step's
callback. -/
noncomputable def phi4BogoliubovCountertermGen
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    StableResolvedPhi4HopfGen → B :=
  WellFounded.fix (InvImage.wf stablePhi4GeneratorRank Nat.lt_wfRel.wf)
    (fun x rec => -S.polePart (phi4BogoliubovPreparationStep S φ x rec))

/-- **body-661b (Step 2) — the unfolded Bogoliubov preparation** `B_φ(x)`.  The preparation step with the
recursive callback instantiated at the fully-recursed counterterm generator. -/
noncomputable def phi4BogoliubovPreparationGen
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) : B :=
  phi4BogoliubovPreparationStep S φ x (fun y _ => phi4BogoliubovCountertermGen S φ y)

/-- **body-661b (Step 2) — the renormalized stable generator** `φ₊(x) = (1 − R)(B_φ(x))`.  The finite
part of the prepared value.  Generator-valued — NOT a character. -/
noncomputable def phi4BogoliubovRenormalizedGen
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) : B :=
  S.finitePart (phi4BogoliubovPreparationGen S φ x)

/-! ## Step 3 — the one-step unfolding equations -/

/-- **body-661b (Step 3, HEADLINE 1) — the counterterm unfolds to `−R` of the prepared value.**  The
`WellFounded.fix` one-step unfolding: the fix's supplied callback `fun y _ => WellFounded.fix … y` is
definitionally the preparation generator's callback `fun y _ => phi4BogoliubovCountertermGen S φ y`. -/
theorem phi4BogoliubovCountertermGen_eq
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovCountertermGen S φ x = -S.polePart (phi4BogoliubovPreparationGen S φ x) := by
  unfold phi4BogoliubovCountertermGen
  rw [WellFounded.fix_eq]
  rfl

/-- **body-661b (Step 3, HEADLINE 2) — the explicit Bogoliubov preparation formula.**
`B_φ(x) = φ(X x) + ∑_{F ∈ W‴(rep x)} (∏_{γ ∈ F} φ₋(component γ)) · φ(rightTerm F)`.  A pure def
unfolding: instantiating the preparation step's callback at the counterterm generator. -/
theorem phi4BogoliubovPreparationGen_eq
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovPreparationGen S φ x
      = φ (MvPolynomial.X x)
        + ∑ F ∈ (phi4WTriplePrimeIndex (stablePhi4ResolvedRep x)).attach,
            (∏ γ ∈ F.1.elements.attach,
                phi4BogoliubovCountertermGen S φ
                  ((stableLocalBoundaryCompletedGraph γ.1).toStableResolvedPhi4HopfGen
                    (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ.1
                      (F.1.isConnectedDivergent γ.1 γ.2))
                    (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ.1
                      (stablePhi4ResolvedRep_stableBoundaryIds x))))
              * φ (stableForestRightTerm F.1
                    (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) F.1)
                    (phi4WTriplePrimeCanonicalSupply.hCD (stablePhi4ResolvedRep x) F.1 F.2)
                    (stableResolvedBoundaryIds_contractWithStars F.1
                      (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) F.1)
                      (stablePhi4ResolvedRep_stableBoundaryIds x))) :=
  rfl

/-- **body-661b (Step 3, HEADLINE 3) — the renormalized generator is the finite part of the prepared
value.** -/
theorem phi4BogoliubovRenormalizedGen_eq
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovRenormalizedGen S φ x = S.finitePart (phi4BogoliubovPreparationGen S φ x) :=
  rfl

/-! ## Step 4 — the SIGN-HONEST decomposition (from 660) -/

/-- **body-661b (Step 4) — the counterterm generator is 660's counterterm value of the prepared
value.**  `φ₋(x) = phi4CountertermValue S (B_φ(x)) = −R(B_φ(x))`. -/
theorem phi4BogoliubovCountertermGen_eq_countervalue
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovCountertermGen S φ x
      = phi4CountertermValue S (phi4BogoliubovPreparationGen S φ x) := by
  rw [phi4BogoliubovCountertermGen_eq, phi4CountertermValue]

/-- **body-661b (Step 4) — the renormalized generator is 660's renormalized value of the prepared
value.**  `φ₊(x) = phi4RenormalizedValue S (B_φ(x)) = B_φ(x) + (−R(B_φ(x)))`. -/
theorem phi4BogoliubovRenormalizedGen_eq_renormvalue
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovRenormalizedGen S φ x
      = phi4RenormalizedValue S (phi4BogoliubovPreparationGen S φ x) := by
  rw [phi4BogoliubovRenormalizedGen_eq, phi4RenormalizedValue_eq_finitePart]

/-- **body-661b (Step 4, SIGN-HONEST DECOMPOSITION) — `preparation + counterterm = renormalized`.**
Since `counterterm = −R(prep)` and `renorm = prep + counterterm = (1 − R)(prep)`, the honest identity is
`B_φ(x) + φ₋(x) = φ₊(x)` — NOT the false "counterterm + renormalized = preparation". -/
theorem phi4Bogoliubov_decomposition
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovPreparationGen S φ x + phi4BogoliubovCountertermGen S φ x
      = phi4BogoliubovRenormalizedGen S φ x := by
  rw [phi4BogoliubovCountertermGen_eq_countervalue, phi4BogoliubovRenormalizedGen_eq_renormvalue,
    phi4RenormalizedValue]

/-- **body-661b (Step 4, pole-part form) — `R(prep) + renormalized = preparation`.**  The pole-part
decomposition of 660 (`phi4SubtractionScheme_decomposition`) instantiated at the prepared value. -/
theorem phi4Bogoliubov_polePart_decomposition
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    S.polePart (phi4BogoliubovPreparationGen S φ x) + phi4BogoliubovRenormalizedGen S φ x
      = phi4BogoliubovPreparationGen S φ x := by
  rw [phi4BogoliubovRenormalizedGen_eq_renormvalue]
  exact phi4SubtractionScheme_decomposition S _

end GaugeGeometry.QFT.Combinatorial
