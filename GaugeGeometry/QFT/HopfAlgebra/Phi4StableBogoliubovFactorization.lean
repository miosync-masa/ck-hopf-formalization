import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovCharacters

/-!
# QFT-R2-body-663 — the CK Birkhoff factorization CROWN `φ₋ ⋆ φ = φ₊`

**663 is the CK Birkhoff factorization CROWN: `φ₋ ⋆ φ = φ₊`** — binding 657 character convolution +
660 Rota–Baxter + 661 Bogoliubov recursion + 662 characters into ONE theorem, with **NO new
geometry / recursion**.  There is nothing new to construct here: the four completed bodies already
carry all the geometry (629 coproduct + W‴ forest sum), the recursion (661b preparation /
counterterm / renormalized), the subtraction (660 Rota–Baxter `−R`), and the character promotion (662
`aeval`).  This body simply *aligns* them.

The generator identity is
`(φ₋ ⋆ φ)(X x) = φ₋(X x) + φ(X x) + ∑_{W‴} φ₋(leftAggregate)·φ(rightTerm)` (657's
`convolution_of_graph`), whose `φ(X x) + ∑_{W‴} φ₋(leftAggregate)·φ(rightTerm)` tail IS 661b's explicit
Bogoliubov preparation `B_φ(x)` once 662's `map_prod` left-aggregate bridge is read BACKWARD (each
forest's `φ₋(leftAggregate)` collapses to the `∏` of counterterm values), so
`(φ₋ ⋆ φ)(X x) = φ₋(X x) + B_φ(x)`.  Adding 662's sign-honest generator decomposition
`B_φ(x) + φ₋(X x) = φ₊(X x)` (a commuted `add`), the generator identity `(φ₋ ⋆ φ)(X x) = φ₊(X x)`
follows.  It lifts to the WHOLE polynomial algebra by `MvPolynomial.algHom_ext` PRECISELY because both
sides are genuine `AlgHom`s (657's convolution is an `AlgHom`; 662's `φ₊` is an `aeval` character), so
agreement on the free generators forces agreement everywhere.

## Contents
* `phi4BogoliubovPreparationGen_eq_characterForestSum` — 661b's preparation read as the *character*
  forest sum (the 662 left-aggregate bridge, BACKWARD): the load-bearing Finset-defeq alignment
  (657's `(index G).carrier.attach` = 661b's `phi4WTriplePrimeIndex.attach`).
* `phi4BogoliubovCountertermConvolution_X_eq` — the generator convolution expansion
  `(φ₋ ⋆ φ)(X x) = φ₋(X x) + B_φ(x)` (657 `convolution_of_graph` + rep recovery + the character
  forest sum).
* `phi4BogoliubovFactorization_X` — the generator Birkhoff identity `(φ₋ ⋆ φ)(X x) = φ₊(X x)`.
* `phi4Bogoliubov_birkhoff_factorization` (CROWN) — `φ₋ ⋆ φ = φ₊` on ALL of `H` via `algHom_ext`, and
  its pointwise form `_apply`.

## HALT compliance
657 convolution, 660 Rota–Baxter, 661a/661b recursion + rank descent + forest geometry, 662 characters
+ decomposition, 651 representative recovery, 629 coproduct are consumed as BLACK BOXES.  NO new
geometry, NO new recursion, NO re-expansion of the 661 recursion / 661a rank descent / 660 RB identity.
This body does NOT claim `φ = φ₋⁻¹ ⋆ φ₊`; it does NOT construct a convolution inverse / antipode / a
`φ₋⁻¹` notation; it does NOT build a preparation CHARACTER; the `−R` relation is NOT extended to
arbitrary Hopf elements (only the generator identity is used, through 662's `_X` anchors).  NO Laurent
/ real integral / Figure-1 evaluation (that is 664).  NO `native_decide` / `Lean.ofReduceBool`; NO
`HEq` / `cast` / graph-data `▸` (only `rfl` / `rw` / `conv` / `add_comm` / `add_assoc` / `algHom_ext` /
`AlgHom.congr_fun`, and a Prop-level `stablePhi4ResolvedRep_gen` rewrite).  NO forbidden divergence
class in any declaration TYPE.  NO `sorry` / `admit`.  ZERO new `structure` / `class` / permanent
`instance` (only a file-scoped `local instance` re-exposing the existing divergence family).  Bodies
≤662 UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap
663 `φ₋ ⋆ φ = φ₊` (THIS FILE) → 664 Figure-1 dropped-term → renormalization weight + HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4StableBogoliubovCharacters`), so the W‴ /
left-aggregate carrier types elaborate. -/
local instance instPhi4DivergenceMeasureFamily663 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 1 — the preparation as the CHARACTER forest sum (662 bridge, BACKWARD) -/

/-- **body-663 (Step 1, LOAD-BEARING) — 661b's Bogoliubov preparation read as the character forest
sum.**  Reversing 662's `map_prod` left-aggregate bridge: each forest's `∏` of counterterm generator
values is `φ₋` of the stable left aggregate.  The forest index is stated in 657's `.carrier.attach`
spelling (defeq to 661b's `phi4WTriplePrimeIndex.attach`), so this RHS matches
`phi4CharacterConvolution_of_graph`'s forest sum verbatim — the alignment that lets Step 3 chain by a
single fold. -/
theorem phi4BogoliubovPreparationGen_eq_characterForestSum
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4BogoliubovPreparationGen S φ x
      = φ (MvPolynomial.X x)
        + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index (stablePhi4ResolvedRep x)).carrier.attach,
            phi4BogoliubovCountertermCharacter S φ
                (stableLeftAggregate A.1 (stablePhi4ResolvedRep_stableBoundaryIds x))
              * φ (stableForestRightTerm A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) A.1)
                    (phi4WTriplePrimeCanonicalSupply.hCD (stablePhi4ResolvedRep x) A.1 A.2)
                    (stableResolvedBoundaryIds_contractWithStars A.1
                      (phi4WTriplePrimeCanonicalSupply.starOf (stablePhi4ResolvedRep x) A.1)
                      (stablePhi4ResolvedRep_stableBoundaryIds x))) := by
  rw [phi4BogoliubovPreparationGen_eq]
  refine congrArg (φ (MvPolynomial.X x) + ·) ?_
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [← phi4BogoliubovCountertermCharacter_stableLeftAggregate S φ A.1
    (stablePhi4ResolvedRep_stableBoundaryIds x)]

/-! ## Step 2 — the generator convolution expansion `(φ₋ ⋆ φ)(X x) = φ₋(X x) + B_φ(x)` -/

/-- **body-663 (Step 2) — the counterterm convolution on a generator.**  `(φ₋ ⋆ φ)(X x)` expands (657
`convolution_of_graph` on the representative `rep x`, via 651's `stablePhi4ResolvedRep_gen`) to
`φ₋(X x) + φ(X x) + ∑_{W‴} φ₋(leftAggregate)·φ(rightTerm)`, whose tail folds (Step 1, backward) into
661b's preparation `B_φ(x)` — giving `φ₋(X x) + B_φ(x)`. -/
theorem phi4BogoliubovCountertermConvolution_X_eq
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ (MvPolynomial.X x)
      = phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X x)
        + phi4BogoliubovPreparationGen S φ x := by
  conv_lhs => rw [stablePhi4ResolvedRep_gen x]
  rw [phi4CharacterConvolution_of_graph (phi4BogoliubovCountertermCharacter S φ) φ
      (stablePhi4ResolvedRep x) (stablePhi4ResolvedRep_isConnectedDivergent x)
      (stablePhi4ResolvedRep_stableBoundaryIds x),
    ← stablePhi4ResolvedRep_gen x, add_assoc,
    ← phi4BogoliubovPreparationGen_eq_characterForestSum]

/-! ## Step 3 — the generator Birkhoff identity (HEADLINE 1) -/

/-- **body-663 (Step 3, HEADLINE 1) — the generator Birkhoff factorization** `(φ₋ ⋆ φ)(X x) = φ₊(X x)`.
Step 2 gives `φ₋(X x) + B_φ(x)`; commuting the sum yields `B_φ(x) + φ₋(X x)`, which is 662's sign-honest
generator decomposition `B_φ(x) + φ₋(X x) = φ₊(X x)`. -/
theorem phi4BogoliubovFactorization_X
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (x : StableResolvedPhi4HopfGen) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ (MvPolynomial.X x)
      = phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X x) := by
  rw [phi4BogoliubovCountertermConvolution_X_eq,
    add_comm (phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X x))
      (phi4BogoliubovPreparationGen S φ x)]
  exact phi4BogoliubovCharacters_generator_decomposition S φ x

/-! ## Step 4 — the full character factorization (CROWN) -/

/-- **body-663 (Step 4, CROWN) — the CK Birkhoff factorization** `φ₋ ⋆ φ = φ₊`.  The generator identity
`phi4BogoliubovFactorization_X` lifts to the WHOLE polynomial algebra by `MvPolynomial.algHom_ext`,
PRECISELY because both `phi4CharacterConvolution φ₋ φ` and `phi4BogoliubovRenormalizedCharacter` are
genuine `AlgHom`s — agreement on the free generators forces agreement everywhere.  This is the formal
Connes–Kreimer Birkhoff factorization core: stable CK coproduct + Bogoliubov recursion + Rota–Baxter
subtraction + character convolution become ONE theorem. -/
theorem phi4Bogoliubov_birkhoff_factorization
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ
      = phi4BogoliubovRenormalizedCharacter S φ := by
  apply MvPolynomial.algHom_ext
  intro x
  exact phi4BogoliubovFactorization_X S φ x

/-- **body-663 (Step 4, CROWN pointwise) — the CK Birkhoff factorization, applied.**  `φ₋ ⋆ φ = φ₊`
read on an arbitrary Hopf element `h`. -/
theorem phi4Bogoliubov_birkhoff_factorization_apply
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (h : StableResolvedPhi4HopfH) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ h
      = phi4BogoliubovRenormalizedCharacter S φ h :=
  AlgHom.congr_fun (phi4Bogoliubov_birkhoff_factorization S φ) h

end GaugeGeometry.QFT.Combinatorial
