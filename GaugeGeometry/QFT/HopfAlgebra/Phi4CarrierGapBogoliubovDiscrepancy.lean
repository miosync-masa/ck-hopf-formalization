import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovFactorization

/-!
# body-664a (QFT-R2) — the GENUINE CK forest weight on Figure 1 + the renormalized-character forest formula

664a instantiates the 653–655 dropped-sector socket with the GENUINE CK weight
`w(F) = φ₋(L_F)·φ(R_F)` on Figure-1's ambient, and proves HEADLINE 1: the completed renormalized
character
`φ₊(X gap) = φ₋(X gap) + φ(X gap) + Eval(w, vec W‴)`
— the actual stable CK computation from 663's Birkhoff factorization `φ₋ ⋆ φ = φ₊` + 657's
`convolution_of_graph`.  The W″ supply's `starOf`/`hCD` *totalizes* the weight (a `dite` on W″
membership, `0` off-index); on W‴ members it DEFEQ-matches 657's convolution summand (601: the W‴
supply's `starOf`/`hCD` are literally *projected* from the W″ supply, so the two agree by
definitional unfolding + `Prop`-level proof irrelevance of the CD witness).

**NO** W″-comparison value / dropped-sector identity / marginal term / numerical criteria (that is
664b).  **NO** momentum integral / real amplitude; **nothing** here asserts any weight is nonzero.
**NO** antipode / convolution inverse / Laurent series; **NO** W″-"character"/"coproduct" fabrication.
663/662/657/656/655/654/653/601/629/588 are consumed as BLACK BOXES (the recursion / rank / RB /
factorization / supply geometry are NOT re-proved).

## Roadmap
664a forest weight + renormalized formula (THIS FILE) → 664b dropped-sector (655 `sdiff`) + Figure-1
marginal term (654 coeff 1) + honest numerical criteria → HALT (antipode / convolution-inverse
frontier).  664b will supply the W″-comparison value, the exact dropped-sector identity, the marginal
term, and the numerical criteria + roadmap.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

open scoped Classical

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped to this file exactly as in `Phi4StableBogoliubovFactorization`), so the W″ / W‴
carrier types elaborate. -/
local instance instPhi4DivergenceMeasureFamily664a : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {B : Type*} [CommRing B] [Algebra ℚ B]

/-! ## Step 1 — the genuine CK forest weight (W″-totalized) -/

/-- **body-664a (Step 1) — the genuine CK forest weight** `w(F) = φ₋(L_F)·φ(R_F)` on Figure-1's
ambient, totalized over the W″ index via the W″ supply's `starOf`/`hCD` (and `0` off the W″ index).
`φ₋ = phi4BogoliubovCountertermCharacter S φ`; the left factor is the counterterm value of the stable
left aggregate; the right factor is `φ` of the stable forest right term of the W″ contraction. -/
noncomputable def phi4CarrierGapBogoliubovForestWeight
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient) : B :=
  if hA : A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient then
    phi4BogoliubovCountertermCharacter S φ
        (stableLeftAggregate A phi4CarrierGapAmbient_stableBoundaryIds)
      * φ (stableForestRightTerm A
            (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
            (phi4WDoublePrimeCanonicalSupply.hCD phi4CarrierGapAmbient A hA)
            (stableResolvedBoundaryIds_contractWithStars A
              (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
              phi4CarrierGapAmbient_stableBoundaryIds))
  else 0

/-! ## Step 2 — membership anchors -/

/-- **body-664a (Step 2) — the weight on a W″ member.**  `dif_pos` on the totalizing `dite`. -/
theorem phi4CarrierGapBogoliubovForestWeight_of_mem_wDoublePrime
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient)
    (hA : A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient) :
    phi4CarrierGapBogoliubovForestWeight S φ A
      = phi4BogoliubovCountertermCharacter S φ
          (stableLeftAggregate A phi4CarrierGapAmbient_stableBoundaryIds)
        * φ (stableForestRightTerm A
              (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
              (phi4WDoublePrimeCanonicalSupply.hCD phi4CarrierGapAmbient A hA)
              (stableResolvedBoundaryIds_contractWithStars A
                (phi4WDoublePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
                phi4CarrierGapAmbient_stableBoundaryIds)) := by
  rw [phi4CarrierGapBogoliubovForestWeight, dif_pos hA]

/-- **body-664a (Step 2) — the weight off the W″ index is `0`.**  `dif_neg`. -/
theorem phi4CarrierGapBogoliubovForestWeight_of_not_mem_wDoublePrime
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient)
    (hA : A ∉ phi4WDoublePrimeIndex phi4CarrierGapAmbient) :
    phi4CarrierGapBogoliubovForestWeight S φ A = 0 := by
  rw [phi4CarrierGapBogoliubovForestWeight, dif_neg hA]

/-- **body-664a (Step 2, CRUX) — the weight on a W‴ member, in the W‴-supply spelling.**  Reads
`W‴ ⊆ W″` (653b) to hit the W″ anchor, then converts the W″-supply form to the W‴-supply form.  The
conversion is BY DEFEQ: 601's W‴ supply has `starOf := W″.starOf` (literally) and
`hCD … hA := W″.hCD … (phi4WTriplePrime_mem_wDoublePrime hA)`, while `stableForestRightTerm` depends
on its CD witness only through a `Prop`, hence proof-irrelevantly.  This is the load-bearing
alignment that makes each summand of 657's `convolution_of_graph` forest sum equal a value of this
weight. -/
theorem phi4CarrierGapBogoliubovForestWeight_of_mem_wTriplePrime
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient)
    (hA : A ∈ phi4WTriplePrimeIndex phi4CarrierGapAmbient) :
    phi4CarrierGapBogoliubovForestWeight S φ A
      = phi4BogoliubovCountertermCharacter S φ
          (stableLeftAggregate A phi4CarrierGapAmbient_stableBoundaryIds)
        * φ (stableForestRightTerm A
              (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
              (phi4WTriplePrimeCanonicalSupply.hCD phi4CarrierGapAmbient A hA)
              (stableResolvedBoundaryIds_contractWithStars A
                (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A)
                phi4CarrierGapAmbient_stableBoundaryIds)) := by
  rw [phi4CarrierGapBogoliubovForestWeight_of_mem_wDoublePrime S φ A
    (phi4WTriplePrimeIndex_subset_wDoublePrime phi4CarrierGapAmbient hA)]
  -- W″-supply form ↔ W‴-supply form: `starOf`/`hCD` DEFEQ (601 projection) + proof-irrelevant CD witness
  rfl

/-! ## Step 3 — the actual W‴ forest sum + HEADLINE 1 -/

/-- **body-664a (Step 3) — the W‴ forest-support evaluation of the weight is its plain W‴ sum.**
655's `phi4ForestSupportEvaluate_indexVector` at `amp := the weight`, `I := phi4WTriplePrimeIndex …`. -/
theorem phi4CarrierGapBogoliubovWeight_wTriplePrime_sum
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4ForestSupportEvaluate (phi4CarrierGapBogoliubovForestWeight S φ)
        (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient))
      = ∑ A ∈ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
          phi4CarrierGapBogoliubovForestWeight S φ A := by
  rw [phi4ForestSupportEvaluate_indexVector]

/-- **body-664a (Step 3, HEADLINE 1) — the renormalized character on Figure 1 as the forest formula.**
The completed Connes–Kreimer renormalized character on Figure-1's stable generator equals the
counterterm value plus the plain `φ` value plus the genuine CK W‴ forest-weight evaluation:
`φ₊(X gap) = φ₋(X gap) + φ(X gap) + Eval(w, vec W‴)`.

Route: 663's Birkhoff `φ₋ ⋆ φ = φ₊` (backward) exposes `(φ₋ ⋆ φ)(X gap)`; `phi4CarrierGapStableGen`
is definitionally `phi4CarrierGapAmbient.toStableResolvedPhi4HopfGen …`, so 657's
`convolution_of_graph` expands it to `φ₋(X gap) + φ(X gap) + ∑_{W‴} φ₋(L)·φ(R)`; the `.carrier.attach`
forest sum folds onto `Eval(w, vec W‴)` through 655's `indexVector`, `Finset.sum_attach`, and the
Step-2 W‴ anchor.  NO dropped-sector / marginal / numerical content; NO nonzero claim. -/
theorem phi4CarrierGap_renormalizedCharacter_eq_forestFormula
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
      = phi4BogoliubovCountertermCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
        + φ (MvPolynomial.X phi4CarrierGapStableGen)
        + phi4ForestSupportEvaluate (phi4CarrierGapBogoliubovForestWeight S φ)
            (phi4ForestIndexVector (phi4WTriplePrimeIndex phi4CarrierGapAmbient)) := by
  have hgen : phi4CarrierGapStableGen
      = phi4CarrierGapAmbient.toStableResolvedPhi4HopfGen
          phi4CarrierGapAmbient_stableCD phi4CarrierGapAmbient_stableBoundaryIds := rfl
  rw [← phi4Bogoliubov_birkhoff_factorization_apply S φ
        (MvPolynomial.X phi4CarrierGapStableGen),
      hgen,
      phi4CharacterConvolution_of_graph (phi4BogoliubovCountertermCharacter S φ) φ
        phi4CarrierGapAmbient phi4CarrierGapAmbient_stableCD
        phi4CarrierGapAmbient_stableBoundaryIds,
      phi4ForestSupportEvaluate_indexVector]
  -- leading `φ₋(X gap) + φ(X gap)` are now syntactically identical on both sides
  congr 1
  -- goal: ∑_{(W‴.index).carrier.attach} φ₋(L)·φ(R) = ∑_{W‴} weight
  have hsummand :
      ∀ A : ((phi4WTriplePrimeCanonicalSupply.index phi4CarrierGapAmbient).carrier),
        phi4BogoliubovCountertermCharacter S φ
              (stableLeftAggregate A.1 phi4CarrierGapAmbient_stableBoundaryIds)
            * φ (stableForestRightTerm A.1
                  (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A.1)
                  (phi4WTriplePrimeCanonicalSupply.hCD phi4CarrierGapAmbient A.1 A.2)
                  (stableResolvedBoundaryIds_contractWithStars A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A.1)
                    phi4CarrierGapAmbient_stableBoundaryIds))
          = phi4CarrierGapBogoliubovForestWeight S φ A.1 :=
    fun A => (phi4CarrierGapBogoliubovForestWeight_of_mem_wTriplePrime S φ A.1 A.2).symm
  refine (Finset.sum_congr rfl (fun A _ => hsummand A)).trans ?_
  exact Finset.sum_attach _ (phi4CarrierGapBogoliubovForestWeight S φ)

end GaugeGeometry.QFT.Combinatorial
