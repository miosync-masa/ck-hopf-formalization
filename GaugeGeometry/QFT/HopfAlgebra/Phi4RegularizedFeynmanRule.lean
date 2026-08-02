import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestEvaluationDiscrepancy
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoproductCoassociativityLaw

/-!
# QFT-R2-body-656 — the regularized Feynman-rule CHARACTER entry

**QFT-R2 opens.**  Figure 1 (the concrete `phi4CarrierGapAmbient`) ascends from a formal *support witness*
(body-653/654/655: a combinatorial carrier-gap graph and its dropped-sector probe weight) to a genuine **Hopf
generator** — a point of the STABLE resolved φ⁴ carrier `StableResolvedPhi4HopfGen` — that a **regularized
Feynman-rule CHARACTER** reads off.  The character is a unital ℚ-algebra homomorphism
`StableResolvedPhi4HopfH →ₐ[ℚ] A` obtained by `MvPolynomial.aeval` from an amplitude assignment
`amp : StableResolvedPhi4HopfGen → A`.

## What this body DOES
* Step 1 — a stable boundary-ID certificate `phi4CarrierGapAmbient_stableBoundaryIds` for Figure 1 (edge/leg
  id uniqueness from body-653b-2b; the boundary-disjointness field is *vacuous* — Figure 1 has NO external
  legs, `externalLegs = 0`).
* Step 2 — the concrete stable generator `phi4CarrierGapStableGen : StableResolvedPhi4HopfGen`, built by
  placing Figure 1 (with its family CD from body-653b-2a and the Step-1 certificate) onto the STABLE carrier,
  plus its class anchor.
* Step 3 — the amplitude assignment `StablePhi4RegularizedAmplitude A` (an `abbrev` for the socket function
  `StableResolvedPhi4HopfGen → A`).
* Step 4 — the genuine Feynman-rule character `phi4RegularizedFeynmanRule amp := MvPolynomial.aeval amp`, with
  its `X` / `1` / `*` computation rules and the headline evaluation at Figure 1's generator.

## ★ SCOPE NOTE — the momentum integral is still a SOCKET ★
`amp : StableResolvedPhi4HopfGen → A` is a **pure socket**.  This body builds **NO** momentum integral, **NO**
real φ⁴ amplitude, **NO** counterterm, **NO** convolution product, **NO** Rota-Baxter / subtraction operator,
**NO** antipode / counit / Bialgebra structure.  Nothing here asserts `amp phi4CarrierGapStableGen ≠ 0`.  There
is **NO** identification between this character value and body-655's forest support weight
(`phi4ForestSupportEvaluate` / `phi4CarrierGapProbeWeight`) — those remain a SEPARATE combinatorial witness.
The character merely evaluates the polynomial algebra through whatever `amp` supplies.

## Roadmap
`656` (this body: the character entry) → `657` (the convolution product on characters) → `658` (the
Rota-Baxter / subtraction operator that renders the amplitude finite) → `659+` (the Bogoliubov recursion /
counterterm character).  Each is a SEPARATE future body; none is entered here.  **HALT** at the character entry.

## HALT / red lines
No constructed integral / counterterm / convolution / antipode / counit / Bialgebra; no nonzero-amplitude
claim; no bridge to body-655's forest weight; ZERO new `structure` / `class` / permanent `instance`
(`StablePhi4RegularizedAmplitude` is an `abbrev`, the character/generator are `def`s, the `CommSemiring` /
`Algebra` are ARGUMENT typeclasses); ZERO forbidden divergence classes in any declaration TYPE (only the
concrete `phi4DivergenceMeasureFamily` / `phi4PermInvariantDivergenceMeasureFamily` family VALUES); ZERO
`sorry` / `admit` / `native_decide`; NO `HEq` / `cast` / graph-data `▸`.  Bodies ≤655 + all stable-carrier +
Figure-1 files UNEDITED.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators

set_option linter.unusedVariables false

/-! ## Step 1 — Figure 1's stable boundary-ID certificate -/

/-- **body-656 (Step 1) — the concrete Figure-1 ambient OWNS the stable boundary-ID certificate.**  Edge/leg
id uniqueness are body-653b-2b's; the boundary-disjointness field is VACUOUS because `phi4CarrierGapAmbient`
has NO external legs (`externalLegs = 0`). -/
theorem phi4CarrierGapAmbient_stableBoundaryIds :
    StableResolvedBoundaryIds phi4CarrierGapAmbient := by
  refine ⟨phi4CarrierGapAmbient_edgeIdsUnique, phi4CarrierGapAmbient_legIdsUnique, ?_⟩
  intro ℓ hℓ e he
  rw [show phi4CarrierGapAmbient.externalLegs = 0 from rfl] at hℓ
  exact absurd hℓ (Multiset.notMem_zero ℓ)

/-! ## Step 2 — the concrete stable generator -/

/-- **body-656 (Step 2) — Figure 1's self-CD existential** for the STABLE carrier constructor.  Recovered from
the body-653b-2a CLASS-level family CD via the `.mp` direction of the resolved-class representative anchor. -/
theorem phi4CarrierGapAmbient_stableCD :
    ∃ hWF : phi4CarrierGapAmbient.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent phi4CarrierGapAmbient.forget
        (phi4DivergenceMeasureFamily phi4CarrierGapAmbient.forget)
        (FeynmanSubgraph.self phi4CarrierGapAmbient.forget hWF) :=
  (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    phi4CarrierGapAmbient).mp phi4CarrierGapAmbient_isConnectedDivergentFor

/-- **body-656 (Step 2) — Figure 1 as a genuine STABLE resolved φ⁴ Hopf GENERATOR.**  The concrete carrier-gap
ambient, carrying both its family CD (body-653b-2a) and the stable boundary-ID certificate (Step 1), placed on
the STABLE carrier `StableResolvedPhi4HopfGen`. -/
noncomputable def phi4CarrierGapStableGen : StableResolvedPhi4HopfGen :=
  phi4CarrierGapAmbient.toStableResolvedPhi4HopfGen
    phi4CarrierGapAmbient_stableCD phi4CarrierGapAmbient_stableBoundaryIds

/-- **body-656 (Step 2, anchor) — the stable generator's class is Figure 1's resolved class.** -/
@[simp] theorem phi4CarrierGapStableGen_val :
    phi4CarrierGapStableGen.val = phi4CarrierGapAmbient.toResolvedClass := rfl

/-! ## Step 3 — the regularized amplitude assignment (SOCKET) -/

/-- **body-656 (Step 3) — the regularized amplitude assignment (a SOCKET).**  An assignment of a value in the
target algebra `A` to each stable resolved φ⁴ generator.  This is the ONLY input to the Feynman-rule character;
the actual momentum integral / regularization that would inhabit it is NOT built here (bodies 657/658/659+). -/
abbrev StablePhi4RegularizedAmplitude (A : Type*) [CommSemiring A] [Algebra ℚ A] :=
  StableResolvedPhi4HopfGen → A

/-! ## Step 4 — the genuine Feynman-rule character -/

/-- **body-656 (Step 4) — the regularized Feynman-rule CHARACTER.**  The unique unital ℚ-algebra homomorphism
`StableResolvedPhi4HopfH →ₐ[ℚ] A` extending the amplitude assignment `amp` on generators, via
`MvPolynomial.aeval`.  A genuine character on the stable resolved φ⁴ Hopf polynomial algebra. -/
noncomputable def phi4RegularizedFeynmanRule
    {A : Type*} [CommSemiring A] [Algebra ℚ A]
    (amp : StablePhi4RegularizedAmplitude A) :
    StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  MvPolynomial.aeval amp

section CharacterRules

variable {A : Type*} [CommSemiring A] [Algebra ℚ A] (amp : StablePhi4RegularizedAmplitude A)

/-- **body-656 (Step 4) — the character reads the amplitude off a single generator.** -/
@[simp] theorem phi4RegularizedFeynmanRule_X (g : StableResolvedPhi4HopfGen) :
    phi4RegularizedFeynmanRule amp (MvPolynomial.X g) = amp g :=
  MvPolynomial.aeval_X amp g

/-- **body-656 (Step 4) — the character is unital.** -/
@[simp] theorem phi4RegularizedFeynmanRule_one :
    phi4RegularizedFeynmanRule amp (1 : StableResolvedPhi4HopfH) = 1 :=
  map_one _

/-- **body-656 (Step 4) — the character is multiplicative.** -/
@[simp] theorem phi4RegularizedFeynmanRule_mul (p q : StableResolvedPhi4HopfH) :
    phi4RegularizedFeynmanRule amp (p * q)
      = phi4RegularizedFeynmanRule amp p * phi4RegularizedFeynmanRule amp q :=
  map_mul _ _ _

end CharacterRules

/-! ## Headline — the character evaluates Figure 1 through the amplitude socket -/

/-- **body-656 (HEADLINE) — the regularized Feynman-rule character reads Figure 1's amplitude.**  On the
generator variable of the concrete carrier-gap ambient, the character returns exactly the socketed amplitude
value `amp phi4CarrierGapStableGen`.  (The value itself is whatever `amp` supplies — NO integral is built, NO
nonzero claim is made, and this is NOT identified with body-655's forest support weight.) -/
theorem phi4RegularizedFeynmanRule_carrierGap
    {A : Type*} [CommSemiring A] [Algebra ℚ A] (amp : StablePhi4RegularizedAmplitude A) :
    phi4RegularizedFeynmanRule amp (MvPolynomial.X phi4CarrierGapStableGen)
      = amp phi4CarrierGapStableGen :=
  phi4RegularizedFeynmanRule_X amp phi4CarrierGapStableGen

end GaugeGeometry.QFT.Combinatorial
