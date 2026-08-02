import GaugeGeometry.QFT.HopfAlgebra.Phi4CharacterConvolutionAssociativity

/-!
# QFT-R2-body-659a — the STABLE resolved φ⁴ COUNIT and its two tensor counit laws

Body-658 recorded the CANDIDATE counit `phi4StableCounitCandidate := MvPolynomial.aeval (fun _ => (0 : ℚ))
: StableResolvedPhi4HopfH →ₐ[ℚ] ℚ` — a plain `def` with NO law attached.  **659a promotes 658's candidate `ε`
to a genuine stable COUNIT**: the two tensor counit laws

* `(ε ⊗ id) ∘ Δᵣˢ = Algebra.TensorProduct.includeRight`  (`phi4StableCounit_left_law`), and
* `(id ⊗ ε) ∘ Δᵣˢ = Algebra.TensorProduct.includeLeft`   (`phi4StableCounit_right_law`),

by **aeval-zero annihilation** of the W‴ forest sum + the two primitive terms, lifted from a graph generator to
the whole algebra by body-651's representative recovery + `MvPolynomial.algHom_ext`.  651's representative
machinery and 629's `_of_graph` computation rule are consumed as BLACK BOXES — **NO geometry / ambient
transport / forest-index / W‴-membership re-proof** beyond calling `mem_phi4WTriplePrimeIndex` +
`isNonempty_of_isProperForest` to extract one component from a carrier member.

## Construction

* **Step 1 — the counit + basic rules.**  `phi4StableCounit := phi4StableCounitCandidate`, with
  `phi4StableCounit_X` (`ε (X g) = 0` via `aeval_X`), `phi4StableCounit_one`, `phi4StableCounit_mul`.
* **Step 2 — aeval-zero forest annihilation.**  `aevalZero_stableLeftAggregate_eq_zero` (a nonempty
  `stableLeftAggregate` — a PRODUCT of `X`'s — is killed by `aeval (fun _ => 0)`, `Finset.prod_eq_zero` on any
  component) and `aevalZero_stableForestRightTerm_eq_zero` (the single-`X` right term) are stated GENERICALLY
  over an arbitrary target `[CommSemiring B] [Algebra ℚ B]` — so body-659b can reuse them for the A-valued
  convolution unit.  Their counit corollaries + the tensor `map ε id` / `map id ε` summand and forest-SUM
  vanishings follow.
* **Step 3 — generator counit laws.**  `phi4StableCounit_left_of_graph` / `_right_of_graph`: one `_of_graph`
  unfolding + the Step-2 forest vanishing collapse `(ε ⊗ id)(Δᵣˢ (X x)) = 1 ⊗ X x` and `(id ⊗ ε)(Δᵣˢ (X x)) =
  X x ⊗ 1`.
* **Step 4 — HEADLINE.**  `phi4StableCounit_left_law` / `_right_law`: `MvPolynomial.algHom_ext` on a generator
  `x`, rewritten to its graph representative by `stablePhi4ResolvedRep_gen`, Step 3, and `includeRight_apply` /
  `includeLeft_apply`.

## HALT / red lines

651 representative recovery + 629 `_of_graph` + 658 candidate are consumed as BLACK BOXES (never reproved); NO
forest geometry / ambient transport / W‴ index machinery beyond `mem_phi4WTriplePrimeIndex` +
`isNonempty_of_isProperForest`.  This file is COUNIT + its two tensor laws ONLY — the A-valued convolution unit
`f ⋆ ε = f` and the `Function.Associative` / `Function.Identity` verdict are body-659b.  NO antipode, NO
counterterm, NO Rota–Baxter, NO convolution associativity / unit restatement; NO reuse of the old
`Counit` / `WithConv` / `Coalgebra` terms.  NO `Coalgebra` / `Bialgebra` / `Semigroup` / `Monoid` / `One` /
`Mul` instance; ZERO `cast` / `HEq` / graph-data `▸`; ZERO forbidden divergence class in any declaration TYPE;
ZERO `sorry` / `admit` / `native_decide`.  Every declaration is a `def` / `abbrev` / `theorem` (a file-scoped
`local instance` re-exposing the EXISTING divergence family is allowed, matching the pre-existing pattern).
Bodies ≤658 UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).

## Roadmap

659a (stable counit `ε` + its two tensor counit laws) → 659b (A-valued convolution unit `f ⋆ ε = f` +
`Function.Associative` / identity verdict) → 660 (Rota–Baxter subtraction) → 661+ (Bogoliubov / counterterm
recursion).  HALT.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct BigOperators

set_option linter.unusedVariables false

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global instance —
scoped to this file exactly as in `Phi4RegularizedCharacterConvolution` / `Phi4StableResolvedHopfCoproduct`),
so the W‴ carrier types in the forest-sum statements elaborate. -/
local instance instPhi4DivergenceMeasureFamily659a : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the counit + basic rules -/

/-- **body-659a (Step 1) — the stable resolved φ⁴ COUNIT** `ε := MvPolynomial.aeval (fun _ => (0 : ℚ))`,
promoting body-658's `phi4StableCounitCandidate` (now armed with its counit laws below). -/
noncomputable abbrev phi4StableCounit : StableResolvedPhi4HopfH →ₐ[ℚ] ℚ :=
  phi4StableCounitCandidate

/-- **body-659a (Step 1) — the counit annihilates every generator.** -/
@[simp] theorem phi4StableCounit_X (g : StableResolvedPhi4HopfGen) :
    phi4StableCounit (MvPolynomial.X g) = 0 := by
  simp only [phi4StableCounit, phi4StableCounitCandidate, MvPolynomial.aeval_X]

/-- **body-659a (Step 1) — the counit preserves the unit.** -/
@[simp] theorem phi4StableCounit_one : phi4StableCounit (1 : StableResolvedPhi4HopfH) = 1 :=
  map_one _

/-- **body-659a (Step 1) — the counit is multiplicative.** -/
theorem phi4StableCounit_mul (p q : StableResolvedPhi4HopfH) :
    phi4StableCounit (p * q) = phi4StableCounit p * phi4StableCounit q :=
  map_mul _ _ _

/-! ## Step 2 — aeval-zero forest annihilation (GENERIC over the target `B`) -/

/-- **body-659a (Step 2, GENERIC) — aeval-zero kills a nonempty stable left aggregate.**  `stableLeftAggregate`
is a PRODUCT of `X`'s over `A.elements.attach`; each factor `aeval (fun _ => 0) (X _) = 0` (`aeval_X`), so any
one component sends the whole product to `0` (`Finset.prod_eq_zero`).  Stated over an arbitrary target so
body-659b can reuse it for the A-valued convolution unit. -/
theorem aevalZero_stableLeftAggregate_eq_zero {B : Type*} [CommSemiring B] [Algebra ℚ B]
    {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G} (hne : A.elements.Nonempty) :
    (MvPolynomial.aeval (fun _ => (0 : B))) (stableLeftAggregate A hSt) = 0 := by
  obtain ⟨γ, hγ⟩ := Finset.attach_nonempty_iff.mpr hne
  simp only [stableLeftAggregate]
  rw [map_prod]
  refine Finset.prod_eq_zero (Finset.mem_attach _ γ) ?_
  simp only [MvPolynomial.aeval_X]

/-- **body-659a (Step 2, GENERIC) — aeval-zero kills the stable right (contraction) term.**  A SINGLE `X`, so
`aeval_X` closes it directly.  Stated over an arbitrary target for body-659b reuse. -/
theorem aevalZero_stableForestRightTerm_eq_zero {B : Type*} [CommSemiring B] [Algebra ℚ B]
    {G : ResolvedFeynmanGraph} (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A.contractWithStars starOf).toResolvedClass)
    (hSt : StableResolvedBoundaryIds (A.contractWithStars starOf)) :
    (MvPolynomial.aeval (fun _ => (0 : B))) (stableForestRightTerm A starOf hCD hSt) = 0 := by
  simp only [stableForestRightTerm, MvPolynomial.aeval_X]

/-- **body-659a (Step 2) — the counit kills a live W‴ carrier member's left aggregate.**  The forest is a
proper forest (`isNonempty_of_isProperForest` on the fifth membership conjunct, `.carrier` defeq
`phi4WTriplePrimeIndex G` feeding `mem_phi4WTriplePrimeIndex`), hence has a component. -/
theorem phi4StableCounit_stableLeftAggregate_eq_zero {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    phi4StableCounit (stableLeftAggregate A.1 hSt) = 0 := by
  have hne : (A.1.elements).Nonempty :=
    ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest
      ((mem_phi4WTriplePrimeIndex G A.1).mp A.2).2.2.2.2.1
  exact aevalZero_stableLeftAggregate_eq_zero hSt hne

/-- **body-659a (Step 2) — the counit kills a right (contraction) term.** -/
theorem phi4StableCounit_stableForestRightTerm_eq_zero {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A.contractWithStars starOf).toResolvedClass)
    (hSt : StableResolvedBoundaryIds (A.contractWithStars starOf)) :
    phi4StableCounit (stableForestRightTerm A starOf hCD hSt) = 0 :=
  aevalZero_stableForestRightTerm_eq_zero A starOf hCD hSt

/-- **body-659a (Step 2) — `(ε ⊗ id)` kills one forest summand** (its LEFT factor vanishes). -/
theorem phi4StableCounit_map_left_stableForestSummand_eq_zero {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    Algebra.TensorProduct.map phi4StableCounit (AlgHom.id ℚ StableResolvedPhi4HopfH)
        (stableForestSummand hSt A) = 0 := by
  unfold stableForestSummand
  rw [Algebra.TensorProduct.map_tmul, phi4StableCounit_stableLeftAggregate_eq_zero hSt A,
    TensorProduct.zero_tmul]

/-- **body-659a (Step 2) — `(id ⊗ ε)` kills one forest summand** (its RIGHT factor vanishes). -/
theorem phi4StableCounit_map_right_stableForestSummand_eq_zero {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH) phi4StableCounit
        (stableForestSummand hSt A) = 0 := by
  unfold stableForestSummand
  rw [Algebra.TensorProduct.map_tmul, phi4StableCounit_stableForestRightTerm_eq_zero,
    TensorProduct.tmul_zero]

/-- **body-659a (Step 2) — `(ε ⊗ id)` kills the whole W‴ forest sum.** -/
theorem phi4StableCounit_map_left_stableForestSum_eq_zero (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) :
    Algebra.TensorProduct.map phi4StableCounit (AlgHom.id ℚ StableResolvedPhi4HopfH)
        (stableForestSum G hSt) = 0 := by
  unfold stableForestSum
  rw [map_sum]
  exact Finset.sum_eq_zero (fun A _ => phi4StableCounit_map_left_stableForestSummand_eq_zero hSt A)

/-- **body-659a (Step 2) — `(id ⊗ ε)` kills the whole W‴ forest sum.** -/
theorem phi4StableCounit_map_right_stableForestSum_eq_zero (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) :
    Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH) phi4StableCounit
        (stableForestSum G hSt) = 0 := by
  unfold stableForestSum
  rw [map_sum]
  exact Finset.sum_eq_zero (fun A _ => phi4StableCounit_map_right_stableForestSummand_eq_zero hSt A)

/-! ## Step 3 — generator counit laws (one `_of_graph` unfolding) -/

/-- **body-659a (Step 3, LEFT) — the LEFT counit law on a graph generator.**  `(ε ⊗ id)(Δᵣˢ (X x)) = 1 ⊗ X x`.
Unfold `Δᵣˢ` by 629's `_of_graph`, distribute `map (ε ⊗ id)` over the sum and the two primitive tensors, and
kill the forest sum + the `ε (X x)` factor. -/
theorem phi4StableCounit_left_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    Algebra.TensorProduct.map phi4StableCounit (AlgHom.id ℚ StableResolvedPhi4HopfH)
        (coproduct_resolved_stable_phi4 (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt)))
      = (1 : ℚ) ⊗ₜ[ℚ] MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt) := by
  rw [coproduct_resolved_stable_phi4_of_graph G hCD hSt, map_add, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    phi4StableCounit_map_left_stableForestSum_eq_zero]
  simp only [phi4StableCounit_X, phi4StableCounit_one, AlgHom.id_apply,
    TensorProduct.zero_tmul, zero_add, add_zero]

/-- **body-659a (Step 3, RIGHT) — the RIGHT counit law on a graph generator.**  `(id ⊗ ε)(Δᵣˢ (X x)) = X x ⊗ 1`.
Mirror of the LEFT law: the forest sum + the `ε (X x)` right factor vanish. -/
theorem phi4StableCounit_right_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH) phi4StableCounit
        (coproduct_resolved_stable_phi4 (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt)))
      = MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt) ⊗ₜ[ℚ] (1 : ℚ) := by
  rw [coproduct_resolved_stable_phi4_of_graph G hCD hSt, map_add, map_add,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
    phi4StableCounit_map_right_stableForestSum_eq_zero]
  simp only [phi4StableCounit_X, phi4StableCounit_one, AlgHom.id_apply,
    TensorProduct.tmul_zero, add_zero]

/-! ## Step 4 — HEADLINE: the two whole-algebra counit laws -/

/-- **body-659a (Step 4, HEADLINE) — the LEFT counit law.**  `(ε ⊗ id) ∘ Δᵣˢ = includeRight` as algebra homs
`StableResolvedPhi4HopfH →ₐ[ℚ] ℚ ⊗[ℚ] StableResolvedPhi4HopfH`.  `MvPolynomial.algHom_ext` on a generator `x`,
rewritten to its graph representative (`stablePhi4ResolvedRep_gen`), Step 3-LEFT, and `includeRight_apply`. -/
theorem phi4StableCounit_left_law :
    (Algebra.TensorProduct.map phi4StableCounit (AlgHom.id ℚ StableResolvedPhi4HopfH)).comp
        coproduct_resolved_stable_phi4
      = Algebra.TensorProduct.includeRight := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [stablePhi4ResolvedRep_gen x, AlgHom.comp_apply, phi4StableCounit_left_of_graph,
    Algebra.TensorProduct.includeRight_apply]

/-- **body-659a (Step 4, HEADLINE) — the RIGHT counit law.**  `(id ⊗ ε) ∘ Δᵣˢ = includeLeft` as algebra homs
`StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH ⊗[ℚ] ℚ`.  Mirror of the LEFT law via Step 3-RIGHT and
`includeLeft_apply`. -/
theorem phi4StableCounit_right_law :
    (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH) phi4StableCounit).comp
        coproduct_resolved_stable_phi4
      = Algebra.TensorProduct.includeLeft := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [stablePhi4ResolvedRep_gen x, AlgHom.comp_apply, phi4StableCounit_right_of_graph,
    Algebra.TensorProduct.includeLeft_apply]

end GaugeGeometry.QFT.Combinatorial
