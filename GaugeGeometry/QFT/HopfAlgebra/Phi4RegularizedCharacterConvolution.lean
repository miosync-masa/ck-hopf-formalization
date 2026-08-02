import GaugeGeometry.QFT.HopfAlgebra.Phi4RegularizedFeynmanRule

/-!
# QFT-R2-body-657 — the stable character convolution evaluator (counit-free direct AlgHom convolution)

Body-656 built the regularized Feynman-rule CHARACTER `phi4RegularizedFeynmanRule amp := MvPolynomial.aeval amp
: StableResolvedPhi4HopfH →ₐ[ℚ] A`.  This body assembles the Connes–Kreimer **convolution** of two such
characters DIRECTLY as an `AlgHom` — the counit-free direct AlgHom convolution
`(f ⋆ g)(x) = mul ∘ (f ⊗ g)(Δᵣˢ x)` — and expands it on a graph generator to
`f(Xx) + g(Xx) + ∑_{W‴ forests} f(leftAggregate)·g(rightTerm)`, the BPHZ forest-weight PROTOTYPE where the
LEFT character will (in a FUTURE body) read counterterms and the RIGHT reads the regularized amplitude.

## Construction

* Step 1 — `phi4CharacterTensorMul f g := Algebra.TensorProduct.lift f g (Commute.all)` — multiplies the two
  characters on a tensor, `(x ⊗ₜ y) ↦ f x * g y` (the target `A` is commutative, so the commuting hypothesis
  is `Commute.all`).
* Step 2 — `phi4CharacterConvolution f g := (phi4CharacterTensorMul f g).comp coproduct_resolved_stable_phi4`
  — the direct convolution character `StableResolvedPhi4HopfH →ₐ[ℚ] A`, `(f ⋆ g)(x) = mul∘(f⊗g)(Δᵣˢ x)`.  NO
  counit, NO `Coalgebra` instance, NO convolution unit / associativity is asserted.
* Step 3 — `phi4RegularizedConvolution ampL ampR` specializes to two regularized amplitudes.
* Step 4/5 — the forest-summand / forest-sum / graph-generator expansion, culminating in the Figure-1
  evaluation `phi4RegularizedConvolution_carrierGap`.

## Physics / scope note

The forest index is the GENUINE `W‴` (`phi4WTriplePrimeIndex` / canonical supply carrier).  By body-653,
Figure 1's OUTER forest `phi4CarrierGapOuterForest` is NOT in `W‴`, so it does NOT appear in this
convolution's forest sum — the carrier-gap discrepancy the earlier bodies isolated persists here.  The LEFT
character `ampL` is where counterterms will (LATER) live and the RIGHT `ampR` reads the regularized amplitude —
but NO such identification is made in this body: `ampL` is a PLAIN socket amplitude.

## HALT / red lines

NO counit / `Coalgebra` instance is fabricated (the stable carrier has none).  NO convolution UNIT
(`f ⋆ ε = f`), NO convolution ASSOCIATIVITY, NO antipode axiom.  NO counterterm character, NO Rota–Baxter /
subtraction operator, NO Bogoliubov recursion.  `ampL` is NOT identified with a counterterm.  NO reuse of the
old `WithConv` / `AntipodeConvolution`.  NO bridge to body-655's forest weight.  Every declaration is a `def` /
`theorem`; the `CommSemiring` / `Algebra ℚ` are ARGUMENT typeclasses — ZERO new `structure` / `class` /
`instance`.

## Roadmap

657 (direct convolution) → 658 (associativity-from-652 + counit frontier audit) → 659 (Rota–Baxter /
subtraction) → 660+ (Bogoliubov / counterterm character).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global instance —
the `local instance` is scoped to this file exactly as in `Phi4StableResolvedHopfCoproduct`), so the W‴
carrier types in the forest-sum statements elaborate. -/
local instance instPhi4DivergenceMeasureFamily657 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {A : Type*} [CommSemiring A] [Algebra ℚ A]

/-! ## Step 1 — tensor evaluation (multiply two characters) -/

/-- **body-657 (Step 1) — the tensor-evaluation of two stable characters.**  `Algebra.TensorProduct.lift`
of `f` and `g` (the commuting hypothesis is `Commute.all`, since `A` is commutative): the unique algebra map
`StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH →ₐ[ℚ] A` sending `x ⊗ₜ y ↦ f x * g y`.  This is the
`mul ∘ (f ⊗ g)` half of the convolution. -/
noncomputable def phi4CharacterTensorMul (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)

/-- **body-657 (Step 1) — the tensor-evaluation on a pure tensor multiplies the two character values.** -/
@[simp] theorem phi4CharacterTensorMul_tmul (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (x y : StableResolvedPhi4HopfH) :
    phi4CharacterTensorMul f g (x ⊗ₜ[ℚ] y) = f x * g y :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-! ## Step 2 — the direct convolution character -/

/-- **body-657 (Step 2) — the counit-free DIRECT convolution character** `f ⋆ g`.  The composition of the
tensor-evaluation `phi4CharacterTensorMul f g` with the stable resolved coproduct `Δᵣˢ`
(`coproduct_resolved_stable_phi4`): `(f ⋆ g)(x) = mul ∘ (f ⊗ g)(Δᵣˢ x)`.  A genuine `AlgHom`
`StableResolvedPhi4HopfH →ₐ[ℚ] A` — NO counit, NO `Coalgebra`, NO convolution unit / associativity. -/
noncomputable def phi4CharacterConvolution (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  (phi4CharacterTensorMul f g).comp coproduct_resolved_stable_phi4

/-- **body-657 (Step 2) — the convolution unfolds as `mul∘(f⊗g)` applied to the coproduct.** -/
theorem phi4CharacterConvolution_apply (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (x : StableResolvedPhi4HopfH) :
    phi4CharacterConvolution f g x
      = phi4CharacterTensorMul f g (coproduct_resolved_stable_phi4 x) := rfl

/-- **body-657 (Step 2) — the convolution character is unital.** -/
@[simp] theorem phi4CharacterConvolution_one (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution f g 1 = 1 := map_one _

/-- **body-657 (Step 2) — the convolution character is multiplicative.** -/
@[simp] theorem phi4CharacterConvolution_mul (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (p q : StableResolvedPhi4HopfH) :
    phi4CharacterConvolution f g (p * q)
      = phi4CharacterConvolution f g p * phi4CharacterConvolution f g q := map_mul _ _ _

/-! ## Step 3 — the regularized-amplitude specialization -/

/-- **body-657 (Step 3) — the direct convolution of two regularized amplitudes.**  The counit-free
convolution `phi4CharacterConvolution` of the two Feynman-rule characters `phi4RegularizedFeynmanRule ampL`
and `phi4RegularizedFeynmanRule ampR`.  `ampL` and `ampR` are PLAIN socket amplitudes — no counterterm
identification. -/
noncomputable def phi4RegularizedConvolution (ampL ampR : StablePhi4RegularizedAmplitude A) :
    StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  phi4CharacterConvolution (phi4RegularizedFeynmanRule ampL) (phi4RegularizedFeynmanRule ampR)

/-! ## Step 4 — the forest summand + forest sum evaluation -/

/-- **body-657 (Step 4) — the tensor-evaluation of one stable W‴ forest summand.**  `phi4CharacterTensorMul`
of `stableForestSummand hSt A` is `f (stableLeftAggregate A.1 hSt) · g (stableForestRightTerm …)`. -/
theorem phi4CharacterTensorMul_stableForestSummand (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    phi4CharacterTensorMul f g (stableForestSummand hSt A)
      = f (stableLeftAggregate A.1 hSt)
        * g (stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
              (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
              (stableResolvedBoundaryIds_contractWithStars A.1
                (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)) := by
  rw [stableForestSummand, phi4CharacterTensorMul_tmul]

/-- **body-657 (Step 4) — the tensor-evaluation of the stable W‴ forest sum.**  `phi4CharacterTensorMul` is an
`AlgHom`, hence additive, so it pushes through `stableForestSum`'s `Finset.sum` termwise. -/
theorem phi4CharacterTensorMul_stableForestSum (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (G : ResolvedFeynmanGraph) (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterTensorMul f g (stableForestSum G hSt)
      = ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
          f (stableLeftAggregate A.1 hSt)
            * g (stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                  (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                  (stableResolvedBoundaryIds_contractWithStars A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)) := by
  rw [stableForestSum, map_sum]
  exact Finset.sum_congr rfl (fun A _ => phi4CharacterTensorMul_stableForestSummand f g hSt A)

/-! ## Step 5 — the graph-generator convolution formula -/

/-- **body-657 (Step 5) — the convolution on a stable resolved-graph generator.**  For a graph `G` owning the
family CD and the stable certificate, `(f ⋆ g)(X x)` expands to `f(Xx) + g(Xx) + ∑_{W‴ forests}
f(leftAggregate)·g(rightTerm)` — the BPHZ forest-weight prototype.  Direct consequence of
`coproduct_resolved_stable_phi4_of_graph` pushed through the additive `phi4CharacterTensorMul`. -/
theorem phi4CharacterConvolution_of_graph (f g : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterConvolution f g (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = f (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
        + g (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
        + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
            f (stableLeftAggregate A.1 hSt)
              * g (stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                    (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                    (stableResolvedBoundaryIds_contractWithStars A.1
                      (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)) := by
  rw [phi4CharacterConvolution_apply, coproduct_resolved_stable_phi4_of_graph G hCD hSt,
    map_add, map_add, phi4CharacterTensorMul_tmul, phi4CharacterTensorMul_tmul,
    phi4CharacterTensorMul_stableForestSum, map_one, map_one, mul_one, one_mul]

/-! ## HEADLINE — the Figure-1 evaluation -/

/-- **body-657 (HEADLINE) — the Figure-1 evaluation of the regularized convolution.**  Evaluated on Figure 1's
concrete stable generator `phi4CarrierGapStableGen`, `(ampL ⋆ ampR)` reads
`ampL(gen) + ampR(gen) + ∑_{W‴ forests} (Feynman ampL)(leftAggregate)·(Feynman ampR)(rightTerm)`.  By
body-653 the OUTER forest `phi4CarrierGapOuterForest` is ABSENT from this `W‴` forest sum — the carrier-gap
discrepancy.  `ampL` is a PLAIN socket amplitude — NO counterterm identification is made. -/
theorem phi4RegularizedConvolution_carrierGap (ampL ampR : StablePhi4RegularizedAmplitude A) :
    phi4RegularizedConvolution ampL ampR (MvPolynomial.X phi4CarrierGapStableGen)
      = ampL phi4CarrierGapStableGen
        + ampR phi4CarrierGapStableGen
        + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index phi4CarrierGapAmbient).carrier.attach,
            (phi4RegularizedFeynmanRule ampL)
                (stableLeftAggregate A.1 phi4CarrierGapAmbient_stableBoundaryIds)
              * (phi4RegularizedFeynmanRule ampR) (stableForestRightTerm A.1
                  (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A.1)
                  (phi4WTriplePrimeCanonicalSupply.hCD phi4CarrierGapAmbient A.1 A.2)
                  (stableResolvedBoundaryIds_contractWithStars A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf phi4CarrierGapAmbient A.1)
                    phi4CarrierGapAmbient_stableBoundaryIds)) := by
  unfold phi4RegularizedConvolution
  show phi4CharacterConvolution (phi4RegularizedFeynmanRule ampL) (phi4RegularizedFeynmanRule ampR)
      (MvPolynomial.X (phi4CarrierGapAmbient.toStableResolvedPhi4HopfGen
        phi4CarrierGapAmbient_stableCD phi4CarrierGapAmbient_stableBoundaryIds)) = _
  rw [phi4CharacterConvolution_of_graph (phi4RegularizedFeynmanRule ampL)
      (phi4RegularizedFeynmanRule ampR) phi4CarrierGapAmbient phi4CarrierGapAmbient_stableCD
      phi4CarrierGapAmbient_stableBoundaryIds,
    phi4RegularizedFeynmanRule_X, phi4RegularizedFeynmanRule_X]
  rfl

end GaugeGeometry.QFT.Combinatorial
