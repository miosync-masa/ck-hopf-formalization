import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCounit

/-!
# QFT-R2-body-659b — the A-valued convolution UNIT and the associative-unital VERDICT

Body-659a promoted `ε` to a genuine stable COUNIT (`(ε⊗id)∘Δᵣˢ = includeRight`, `(id⊗ε)∘Δᵣˢ = includeLeft`)
and — crucially — stated its aeval-zero forest annihilation lemmas GENERICALLY over an arbitrary target `B`.
**659b completes the character algebra**: the `A`-valued convolution **UNIT** `η := aeval (fun _ => 0)
: StableResolvedPhi4HopfH →ₐ[ℚ] A`, the two convolution-unit laws `η ⋆ f = f` and `f ⋆ η = f` (reusing
659a's GENERIC aeval-zero annihilation at `B := A` + body-651 representative recovery + 629's `_of_graph`),
and the associative-unital **VERDICT** issued as BARE THEOREMS — character convolution is an ASSOCIATIVE
UNITAL operation; **NO `Std.Associative` / `Monoid` / `Mul` / `One` instance is created**.

## Construction

* **Step 1 — the convolution unit + basic rules.**  `phi4StableConvolutionUnit := MvPolynomial.aeval
  (fun _ => (0 : A))` (defeq `phi4RegularizedFeynmanRule (fun _ => 0)`), with `phi4StableConvolutionUnit_X`
  (`η (X g) = 0` via `aeval_X`) and `phi4StableConvolutionUnit_one` (`map_one`).
* **Step 2 — unit annihilation of the forest sum.**  Reusing 659a's GENERIC `aevalZero_stableLeftAggregate_eq_zero`
  / `aevalZero_stableForestRightTerm_eq_zero` at `B := A` (nonempty via `isNonempty_of_isProperForest ∘
  mem_phi4WTriplePrimeIndex`), the `phi4CharacterTensorMul η f` LEFT-factor vanish and `phi4CharacterTensorMul
  f η` RIGHT-factor vanish push through the forest SUM termwise.
* **Step 3 — generator unit laws.**  `phi4CharacterConvolution_unit_left_of_graph` / `_right_of_graph`: one
  `_of_graph` unfolding, the forest sum vanishes, and the two primitives collapse `0·f 1 + η 1·f(Xx) + 0 =
  f(Xx)` (LEFT) / `f(Xx)·1 + f 1·0 + 0 = f(Xx)` (RIGHT).
* **Step 4 — HEADLINE.**  `phi4CharacterConvolution_left_unit` / `_right_unit`: `MvPolynomial.algHom_ext` on a
  generator `x`, rewritten to its graph representative by `stablePhi4ResolvedRep_gen`, Step 3 closes.
* **Step 5 — VERDICT (bare theorems).**  `phi4CharacterConvolution_isAssociative` (re-export 658),
  `phi4StableConvolutionUnit_isLeftIdentity` / `_isRightIdentity` — the associative + two-sided-identity
  content as PLAIN `∀`-theorems.  NO `Std.Associative` / `Monoid` / `Mul` / `One` instance.

## HALT / red lines

659a's GENERIC `aevalZero_*` + 658 associativity + 657 convolution + 651 representative recovery + 629
`_of_graph` are consumed as BLACK BOXES; NO forest geometry / ambient transport / W‴ index machinery beyond
`mem_phi4WTriplePrimeIndex` + `isNonempty_of_isProperForest`.  The Hopf frontier stays OPEN — **the antipode is
NOT built** (that + Rota–Baxter subtraction is 660+).  NO antipode / counterterm / Rota–Baxter / Bogoliubov
recursion; NO reuse of the old `Counit` / `WithConv` / `AntipodeConvolution`.  NO `Std.Associative` / `Monoid` /
`Semigroup` / `Mul` / `One` / `Coalgebra` / `Bialgebra` instance (the verdict is BARE THEOREMS).  Target stays
`CommSemiring A` + `Algebra ℚ A`.  ZERO `cast` / `HEq` / graph-data `▸`; ZERO forbidden divergence class in any
declaration TYPE; ZERO `sorry` / `admit` / `native_decide`.  Every declaration is a `def` / `theorem` (a
file-scoped `local instance` re-exposing the EXISTING divergence family is allowed).  Bodies ≤659a UNEDITED;
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap

659b (A-valued convolution unit `η ⋆ f = f`, `f ⋆ η = f` + associative-unital verdict) → 660 (Rota–Baxter
subtraction) → 661+ (Bogoliubov / counterterm recursion).  HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global instance —
scoped to this file exactly as in `Phi4StableCounit` / `Phi4RegularizedCharacterConvolution`), so the W‴
carrier types in the forest-sum statements elaborate. -/
local instance instPhi4DivergenceMeasureFamily659b : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {A : Type*} [CommSemiring A] [Algebra ℚ A]

/-! ## Step 1 — the convolution unit + basic rules -/

/-- **body-659b (Step 1) — the A-valued convolution UNIT** `η := MvPolynomial.aeval (fun _ => (0 : A))`
(defeq `phi4RegularizedFeynmanRule (fun _ => 0)`).  This is the two-sided identity of character convolution
(Steps 3–5). -/
noncomputable def phi4StableConvolutionUnit : StableResolvedPhi4HopfH →ₐ[ℚ] A :=
  MvPolynomial.aeval (fun _ => (0 : A))

/-- **body-659b (Step 1) — the unit annihilates every generator.** -/
@[simp] theorem phi4StableConvolutionUnit_X (g : StableResolvedPhi4HopfGen) :
    (phi4StableConvolutionUnit : StableResolvedPhi4HopfH →ₐ[ℚ] A) (MvPolynomial.X g) = 0 := by
  simp only [phi4StableConvolutionUnit, MvPolynomial.aeval_X]

/-- **body-659b (Step 1) — the unit preserves the algebra unit.** -/
@[simp] theorem phi4StableConvolutionUnit_one :
    (phi4StableConvolutionUnit : StableResolvedPhi4HopfH →ₐ[ℚ] A) 1 = 1 :=
  map_one _

/-! ## Step 2 — unit annihilation of the forest sum through `phi4CharacterTensorMul` -/

/-- **body-659b (Step 2) — the unit kills a live W‴ carrier member's left aggregate**, by 659a's GENERIC
`aevalZero_stableLeftAggregate_eq_zero` at `B := A` (`η` is defeq `aeval (fun _ => 0)`; nonempty via
`isNonempty_of_isProperForest` on the fifth membership conjunct). -/
theorem phi4StableConvolutionUnit_stableLeftAggregate_eq_zero {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G)
    (A' : {A' : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A' ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    (phi4StableConvolutionUnit : StableResolvedPhi4HopfH →ₐ[ℚ] A) (stableLeftAggregate A'.1 hSt) = 0 := by
  have hne : (A'.1.elements).Nonempty :=
    ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest
      ((mem_phi4WTriplePrimeIndex G A'.1).mp A'.2).2.2.2.2.1
  exact aevalZero_stableLeftAggregate_eq_zero hSt hne

/-- **body-659b (Step 2) — the unit kills a right (contraction) term**, by 659a's GENERIC
`aevalZero_stableForestRightTerm_eq_zero` at `B := A`. -/
theorem phi4StableConvolutionUnit_stableForestRightTerm_eq_zero {G : ResolvedFeynmanGraph}
    (A' : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A'.contractWithStars starOf).toResolvedClass)
    (hSt : StableResolvedBoundaryIds (A'.contractWithStars starOf)) :
    (phi4StableConvolutionUnit : StableResolvedPhi4HopfH →ₐ[ℚ] A)
        (stableForestRightTerm A' starOf hCD hSt) = 0 :=
  aevalZero_stableForestRightTerm_eq_zero A' starOf hCD hSt

/-- **body-659b (Step 2, LEFT-unit) — `phi4CharacterTensorMul η f` kills the whole W‴ forest sum.**  Each
summand `η(leftAggregate) · f(rightTerm) = 0 · f(rightTerm) = 0` (the LEFT factor vanishes). -/
theorem phi4CharacterTensorMul_unit_left_stableForestSum_eq_zero
    (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterTensorMul phi4StableConvolutionUnit f (stableForestSum G hSt) = 0 := by
  rw [stableForestSum, map_sum]
  refine Finset.sum_eq_zero (fun A' _ => ?_)
  rw [phi4CharacterTensorMul_stableForestSummand,
    phi4StableConvolutionUnit_stableLeftAggregate_eq_zero hSt A', zero_mul]

/-- **body-659b (Step 2, RIGHT-unit) — `phi4CharacterTensorMul f η` kills the whole W‴ forest sum.**  Each
summand `f(leftAggregate) · η(rightTerm) = f(leftAggregate) · 0 = 0` (the RIGHT factor vanishes). -/
theorem phi4CharacterTensorMul_unit_right_stableForestSum_eq_zero
    (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterTensorMul f phi4StableConvolutionUnit (stableForestSum G hSt) = 0 := by
  rw [stableForestSum, map_sum]
  refine Finset.sum_eq_zero (fun A' _ => ?_)
  rw [phi4CharacterTensorMul_stableForestSummand,
    phi4StableConvolutionUnit_stableForestRightTerm_eq_zero, mul_zero]

/-! ## Step 3 — generator unit laws (one `_of_graph` unfolding) -/

/-- **body-659b (Step 3, LEFT) — the LEFT convolution-unit law on a graph generator.**  `(η ⋆ f)(X x) = f(X x)`.
Unfold `Δᵣˢ` by 629's `_of_graph`, distribute `phi4CharacterTensorMul η f` over the sum and the two primitive
tensors, kill the forest sum, and collapse `η(Xx)·f 1 + η 1·f(Xx) + 0 = 0 + f(Xx) + 0 = f(Xx)`. -/
theorem phi4CharacterConvolution_unit_left_of_graph (f : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterConvolution phi4StableConvolutionUnit f
        (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = f (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt)) := by
  rw [phi4CharacterConvolution_apply, coproduct_resolved_stable_phi4_of_graph G hCD hSt,
    map_add, map_add, phi4CharacterTensorMul_tmul, phi4CharacterTensorMul_tmul,
    phi4CharacterTensorMul_unit_left_stableForestSum_eq_zero]
  simp only [phi4StableConvolutionUnit_X, phi4StableConvolutionUnit_one, zero_mul, one_mul,
    add_zero, zero_add]

/-- **body-659b (Step 3, RIGHT) — the RIGHT convolution-unit law on a graph generator.**  `(f ⋆ η)(X x) = f(X x)`.
Mirror of the LEFT law: the forest sum vanishes and `f(Xx)·η 1 + f 1·η(Xx) + 0 = f(Xx)·1 + f 1·0 + 0 = f(Xx)`. -/
theorem phi4CharacterConvolution_unit_right_of_graph (f : StableResolvedPhi4HopfH →ₐ[ℚ] A)
    (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    phi4CharacterConvolution f phi4StableConvolutionUnit
        (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = f (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt)) := by
  rw [phi4CharacterConvolution_apply, coproduct_resolved_stable_phi4_of_graph G hCD hSt,
    map_add, map_add, phi4CharacterTensorMul_tmul, phi4CharacterTensorMul_tmul,
    phi4CharacterTensorMul_unit_right_stableForestSum_eq_zero]
  simp only [phi4StableConvolutionUnit_X, phi4StableConvolutionUnit_one, mul_zero, mul_one,
    add_zero]

/-! ## Step 4 — HEADLINE: the two whole-algebra convolution-unit laws -/

/-- **body-659b (Step 4, HEADLINE) — the LEFT convolution-unit law** `η ⋆ f = f` as algebra homs
`StableResolvedPhi4HopfH →ₐ[ℚ] A`.  `MvPolynomial.algHom_ext` on a generator `x`, rewritten to its graph
representative (`stablePhi4ResolvedRep_gen`), and Step 3-LEFT. -/
theorem phi4CharacterConvolution_left_unit (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution phi4StableConvolutionUnit f = f := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [stablePhi4ResolvedRep_gen x]
  exact phi4CharacterConvolution_unit_left_of_graph f _ _ _

/-- **body-659b (Step 4, HEADLINE) — the RIGHT convolution-unit law** `f ⋆ η = f` as algebra homs
`StableResolvedPhi4HopfH →ₐ[ℚ] A`.  Mirror of the LEFT law via Step 3-RIGHT. -/
theorem phi4CharacterConvolution_right_unit (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution f phi4StableConvolutionUnit = f := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [stablePhi4ResolvedRep_gen x]
  exact phi4CharacterConvolution_unit_right_of_graph f _ _ _

/-! ## Step 5 — the associative-unital VERDICT (BARE THEOREMS — NO instance) -/

/-- **body-659b (Step 5, VERDICT) — character convolution is ASSOCIATIVE** (re-export of 658).  A BARE theorem
— NO `Std.Associative` / `Semigroup` / `Monoid` instance is created. -/
theorem phi4CharacterConvolution_isAssociative
    (f g h : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution (phi4CharacterConvolution f g) h
      = phi4CharacterConvolution f (phi4CharacterConvolution g h) :=
  phi4CharacterConvolution_assoc f g h

/-- **body-659b (Step 5, VERDICT) — `η` is a LEFT identity for character convolution.**  A BARE theorem — NO
`One` / `Monoid` instance is created. -/
theorem phi4StableConvolutionUnit_isLeftIdentity (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution phi4StableConvolutionUnit f = f :=
  phi4CharacterConvolution_left_unit f

/-- **body-659b (Step 5, VERDICT) — `η` is a RIGHT identity for character convolution.**  A BARE theorem — NO
`One` / `Monoid` instance is created.  Together with `phi4CharacterConvolution_isAssociative` and
`phi4StableConvolutionUnit_isLeftIdentity`, these three facts ARE the associative-unital verdict: character
convolution is an ASSOCIATIVE UNITAL operation with two-sided unit `η`.  (The Hopf frontier remains OPEN — the
antipode is NOT built here; that + Rota–Baxter subtraction is 660+.) -/
theorem phi4StableConvolutionUnit_isRightIdentity (f : StableResolvedPhi4HopfH →ₐ[ℚ] A) :
    phi4CharacterConvolution f phi4StableConvolutionUnit = f :=
  phi4CharacterConvolution_right_unit f

end GaugeGeometry.QFT.Combinatorial
