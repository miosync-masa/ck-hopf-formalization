import GaugeGeometry.QFT.HopfAlgebra.Phi4BubbleWitnessTopology
import GaugeGeometry.QFT.HopfAlgebra.Phi4RegularizedCharacterConvolution

/-!
# QFT-R2-body-665c — the payoff: the bubble forest lives in W‴ ⇒ the stable φ⁴₄ coproduct is NON-PRIMITIVE

The payoff: the one-loop four-point bubble forest lives in W‴ (`phi4BubbleForest_mem_wTriplePrime` — it
PASSES the fifth axis, the exact inverse of Figure 1), so W‴ is nonempty, and via the all-1 character
`c = MvPolynomial.aeval (fun _ => 1)` through the tensor evaluator the forest sum evaluates to `|W‴| > 0` —
cancellation-free — hence `stableForestSum ≠ 0` and the stable φ⁴₄ coproduct is genuinely NON-PRIMITIVE on
the bubble generator: `Δᵣˢ(X_G) ≠ X_G ⊗ 1 + 1 ⊗ X_G`.  Positive counterpart to Figure 1's dropped-sector
counterexample: the coproduct actually computes real forest combinatorics.  Part 3/3.

## The four victory theorems

1. `phi4BubbleForest_mem_wTriplePrime` — the singleton admissible forest `{δ}` on the bubble subgraph lands
   in W‴.  All seven axes pass; crucially the FIFTH (forest-internal-edge completeness) PASSES here — the
   exact inverse of Figure 1's `phi4CarrierGapOuterForest_not_mem_wTriplePrime`, whose hidden root edge
   `h03` breaks edge-completeness.
2. `phi4BubbleWTriplePrimeIndex_nonempty` — W‴ is therefore inhabited on `phi4BubbleAmbient`.
3. `phi4Bubble_stableForestSum_ne_zero` — the stable W‴ forest sum is nonzero.  Route: the all-1 character
   `c := MvPolynomial.aeval (fun _ => (1 : ℚ))` sends every generator to `1`, so each summand
   `c(leftAggregate) · c(rightTerm) = (∏ 1) · 1 = 1` (cancellation-free — no sign collapses the sum), and
   through the tensor evaluator `phi4CharacterTensorMul c c` the forest sum evaluates to `|W‴|`, which is
   `> 0` by (2).  A NONZERO image forces a nonzero preimage.
4. `coproduct_resolved_stable_phi4_bubble_not_primitive` (the CROWN) — expanding `Δᵣˢ(X_G)` via
   `coproduct_resolved_stable_phi4_of_graph` gives `(X_G ⊗ 1 + 1 ⊗ X_G) + stableForestSum`; were it
   primitive, the forest sum would vanish (`add_right_eq_self`), contradicting (3).

## The pairing with Figure 1

* **Figure 1** (`phi4CarrierGapOuterForest_not_mem_wTriplePrime`) = the necessary COUNTEREXAMPLE dropped by
  the fifth axis: an outer forest whose hidden root edge `h03` is doubly-inside but not internal, so
  vertex-induced edge-completeness FAILS and the forest is correctly excluded from W‴.
* **The bubble** (this file) = the positive EXAMPLE passing the fifth axis: the ambient edges with both
  endpoints inside `{0,1}` are EXACTLY the two bubble edges, so edge-completeness holds and the forest
  enters W‴ — generating a genuine non-primitive coproduct term.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
ZERO forbidden divergence classes in ANY declaration type.  No constructed symmetry factor / Feynman
integral / numerical amplitude; `stableForestSum ≠ 0` is PROVED via the character trick, never weakened to
"W‴ nonempty".  No `HEq` / `cast` / graph-data `▸`.  ZERO new `structure` / `class` / global `instance`
(`phi4BubbleForest` / `phi4BubbleStableGen` / `phi4BubbleAllOne` are `def`s; one file-local `local instance`
re-exposes the existing φ⁴ divergence family).  Bodies ≤665b UNEDITED.

**IMPORT NOTE.**  The 665b topology import does NOT transitively reach the stable coproduct (629) / tensor
evaluator (657); the W‴/Hopf machinery therefore enters through the additional
`Phi4RegularizedCharacterConvolution` (657) import (which brings 629 / 656 / the W‴ carrier + owner).  Both
imports are needed; no existing file is edited.  **HALT (665c — full payoff delivered).**
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped BigOperators
open scoped Classical
open scoped TensorProduct

set_option linter.unusedVariables false

/-- **body-665c — file-local φ⁴ divergence-measure family instance** (same value as 665a / 665b). -/
local instance instPhi4DivergenceMeasureFamily665c :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 1 — the bubble stable generator (mirror of body-656) -/

/-- **body-665c (Step 1) — the bubble ambient OWNS the stable boundary-ID certificate.**  Edge/leg id
uniqueness are 665a's; the boundary-disjointness field is VACUOUS because `phi4BubbleAmbient` has NO external
legs (`externalLegs = 0`).  Mirrors `phi4CarrierGapAmbient_stableBoundaryIds`. -/
theorem phi4BubbleAmbient_stableBoundaryIds :
    StableResolvedBoundaryIds phi4BubbleAmbient := by
  refine ⟨phi4BubbleAmbient_edgeIdsUnique, phi4BubbleAmbient_legIdsUnique, ?_⟩
  intro ℓ hℓ e he
  rw [show phi4BubbleAmbient.externalLegs = 0 from rfl] at hℓ
  exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-665c (Step 1) — the bubble ambient's self-CD existential** for the STABLE carrier constructor.
Recovered from the body-665b CLASS-level family CD via the `.mp` direction of the resolved-class anchor.
Mirrors `phi4CarrierGapAmbient_stableCD`. -/
theorem phi4BubbleAmbient_stableCD :
    ∃ hWF : phi4BubbleAmbient.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent phi4BubbleAmbient.forget
        (phi4DivergenceMeasureFamily phi4BubbleAmbient.forget)
        (FeynmanSubgraph.self phi4BubbleAmbient.forget hWF) :=
  (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    phi4BubbleAmbient).mp phi4BubbleAmbient_isConnectedDivergentFor

/-- **body-665c (Step 1) — the bubble ambient as a genuine STABLE resolved φ⁴ Hopf GENERATOR.**  Carries both
its family CD (665b) and the stable boundary-ID certificate.  Mirrors `phi4CarrierGapStableGen`. -/
noncomputable def phi4BubbleStableGen : StableResolvedPhi4HopfGen :=
  phi4BubbleAmbient.toStableResolvedPhi4HopfGen
    phi4BubbleAmbient_stableCD phi4BubbleAmbient_stableBoundaryIds

/-! ## Step 2 — the bubble forest is in W‴ (HEADLINE 1) -/

/-- **body-665c (Step 2) — the one-loop four-point bubble as a singleton admissible forest** `{δ}` on the
ambient.  CD from 665b.  Mirrors `phi4CarrierGapOuterForest`. -/
noncomputable def phi4BubbleForest :
    ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4BubbleAmbient :=
  singletonResolvedAdmissibleSubgraph phi4BubbleInner phi4BubbleInner_forget_isConnectedDivergent

/-- Bubble forest aggregate internal edges = the single component's internal edges. -/
theorem phi4BubbleForest_internalEdges :
    phi4BubbleForest.internalEdges = phi4BubbleInner.internalEdges := by
  show (singletonResolvedAdmissibleSubgraph phi4BubbleInner
    phi4BubbleInner_forget_isConnectedDivergent).internalEdges = _
  exact singletonResolvedAdmissibleSubgraph_internalEdges _ _

/-- **body-665c — the bubble forest complement is exactly the six cograph edges** (`6 > 0`). -/
theorem phi4BubbleForest_complementEdges :
    phi4BubbleForest.complementEdges = phi4BubbleCrossEdges := by
  show phi4BubbleAmbient.internalEdges - phi4BubbleForest.internalEdges = phi4BubbleCrossEdges
  rw [phi4BubbleForest_internalEdges]
  exact phi4BubbleInner_complementEdges_eq

/-- **body-665c (Step 2) — the bubble singleton forest is a proper forest.**  Nonempty, one nonempty
component (`{0,1}`, card `2 > 0`), `2 > 0` total & component internal edges, complement six edges `> 0`. -/
theorem phi4BubbleForest_isProperForest :
    phi4BubbleForest.IsProperForest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- IsNonempty
    exact Finset.singleton_nonempty _
  · -- HasNonemptyComponents
    intro γ hγ
    have hγ' : γ ∈ ({phi4BubbleInner} : Finset (ResolvedFeynmanSubgraph phi4BubbleAmbient)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    show 0 < phi4BubbleInner.vertices.card
    decide
  · -- total internal edges
    rw [phi4BubbleForest_internalEdges]; decide
  · -- HasPositiveInternalEdgesComponents
    intro γ hγ
    have hγ' : γ ∈ ({phi4BubbleInner} : Finset (ResolvedFeynmanSubgraph phi4BubbleAmbient)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    decide
  · -- complement edges card
    rw [phi4BubbleForest_complementEdges]; decide

/-- **body-665c (Step 2) — the bubble forest is external-leg saturated** (its single component is; trivial —
the vacuum ambient has no external legs). -/
theorem phi4BubbleForest_saturated :
    ResolvedForestExternalLegSaturated phi4BubbleForest := by
  intro γ hγ
  have hγ' : γ ∈ ({phi4BubbleInner} : Finset (ResolvedFeynmanSubgraph phi4BubbleAmbient)) := hγ
  rw [Finset.mem_singleton] at hγ'
  subst hγ'
  exact phi4BubbleInner_saturated

/-- **body-665c (Step 2, THE FIFTH AXIS PASSES) — the bubble forest is forest-internal-edge complete.**  Its
only component `phi4BubbleInner` is edge-complete (665a) — the ambient edges with both endpoints inside
`{0,1}` are EXACTLY the two bubble edges.  This is the EXACT INVERSE of Figure 1's
`phi4CarrierGapOuterForest_not_internalEdgeComplete`, which fails at the hidden root edge `h03`. -/
theorem phi4BubbleForest_internalEdgeComplete :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily phi4BubbleForest := by
  intro γ hγ
  have hγ' : γ ∈ ({phi4BubbleInner} : Finset (ResolvedFeynmanSubgraph phi4BubbleAmbient)) := hγ
  rw [Finset.mem_singleton] at hγ'
  subst hγ'
  exact phi4BubbleInner_internalEdgeComplete

/-- **body-665c (HEADLINE 1) — the bubble forest lives in W‴.**  All seven axes pass — support (665a), CD
(665b), edge/leg id-uniqueness (665a), properness, external-leg saturation, and — the load-bearing FIFTH
axis — forest-internal-edge completeness.  The exact inverse of Figure 1's
`phi4CarrierGapOuterForest_not_mem_wTriplePrime`. -/
theorem phi4BubbleForest_mem_wTriplePrime :
    phi4BubbleForest ∈ phi4WTriplePrimeIndex phi4BubbleAmbient :=
  (mem_phi4WTriplePrimeIndex phi4BubbleAmbient phi4BubbleForest).mpr
    ⟨phi4BubbleAmbient_ambientSupported,
     phi4BubbleAmbient_isConnectedDivergentFor,
     phi4BubbleAmbient_edgeIdsUnique,
     phi4BubbleAmbient_legIdsUnique,
     phi4BubbleForest_isProperForest,
     phi4BubbleForest_saturated,
     phi4BubbleForest_internalEdgeComplete⟩

/-! ## Step 3 — W‴ nonempty (HEADLINE 2) -/

/-- **body-665c (HEADLINE 2) — W‴ is nonempty on the bubble ambient.**  Witnessed by the bubble forest. -/
theorem phi4BubbleWTriplePrimeIndex_nonempty :
    (phi4WTriplePrimeIndex phi4BubbleAmbient).Nonempty :=
  ⟨phi4BubbleForest, phi4BubbleForest_mem_wTriplePrime⟩

/-! ## Step 4 — the forest sum is nonzero via the all-1 character (HEADLINE 3, cancellation-free) -/

/-- **body-665c (Step 4) — the all-1 character** `c := aeval (fun _ => 1)`: the ℚ-algebra map sending EVERY
stable resolved φ⁴ generator to `1`.  The character trick that makes the forest sum cancellation-free. -/
noncomputable def phi4BubbleAllOne : StableResolvedPhi4HopfH →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval (fun _ => (1 : ℚ))

/-- **body-665c (Step 4) — the all-1 character reads `1` off every generator.** -/
theorem phi4BubbleAllOne_X (g : StableResolvedPhi4HopfGen) :
    phi4BubbleAllOne (MvPolynomial.X g) = 1 := by
  simp only [phi4BubbleAllOne, MvPolynomial.aeval_X]

/-- **body-665c (Step 4) — the all-1 character sends every left aggregate to `1`** (a product of generators,
each `↦ 1`). -/
theorem phi4BubbleAllOne_stableLeftAggregate
    {G : ResolvedFeynmanGraph} (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hSt : StableResolvedBoundaryIds G) :
    phi4BubbleAllOne (stableLeftAggregate A hSt) = 1 := by
  unfold stableLeftAggregate
  rw [map_prod]
  apply Finset.prod_eq_one
  intro γ _
  exact phi4BubbleAllOne_X _

/-- **body-665c (Step 4) — the all-1 character sends every right (contraction) term to `1`** (a single
generator `↦ 1`). -/
theorem phi4BubbleAllOne_stableForestRightTerm
    {G : ResolvedFeynmanGraph} (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A.contractWithStars starOf).toResolvedClass)
    (hSt : StableResolvedBoundaryIds (A.contractWithStars starOf)) :
    phi4BubbleAllOne (stableForestRightTerm A starOf hCD hSt) = 1 := by
  unfold stableForestRightTerm
  exact phi4BubbleAllOne_X _

/-- **body-665c (Step 4, cancellation-free) — the tensor-evaluation of the bubble forest sum is `|W‴|`.**
Through `phi4CharacterTensorMul c c`, each W‴ summand collapses to `c(leftAggregate) · c(rightTerm) = 1·1 = 1`
(no sign, no cancellation), so the sum counts the carrier: `∑ 1 = |W‴|`. -/
theorem phi4Bubble_charTensorMul_stableForestSum :
    phi4CharacterTensorMul phi4BubbleAllOne phi4BubbleAllOne
        (stableForestSum phi4BubbleAmbient phi4BubbleAmbient_stableBoundaryIds)
      = ((phi4WTriplePrimeIndex phi4BubbleAmbient).card : ℚ) := by
  rw [phi4CharacterTensorMul_stableForestSum]
  have hterm : ∀ A ∈ (phi4WTriplePrimeCanonicalSupply.index phi4BubbleAmbient).carrier.attach,
      phi4BubbleAllOne (stableLeftAggregate A.1 phi4BubbleAmbient_stableBoundaryIds)
        * phi4BubbleAllOne (stableForestRightTerm A.1
            (phi4WTriplePrimeCanonicalSupply.starOf phi4BubbleAmbient A.1)
            (phi4WTriplePrimeCanonicalSupply.hCD phi4BubbleAmbient A.1 A.2)
            (stableResolvedBoundaryIds_contractWithStars A.1
              (phi4WTriplePrimeCanonicalSupply.starOf phi4BubbleAmbient A.1)
              phi4BubbleAmbient_stableBoundaryIds)) = 1 := by
    intro A _
    rw [phi4BubbleAllOne_stableLeftAggregate, phi4BubbleAllOne_stableForestRightTerm, mul_one]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, mul_one]
  rfl

/-- **body-665c (HEADLINE 3) — the stable W‴ forest sum is NONZERO.**  A nonzero image under
`phi4CharacterTensorMul c c` (namely `|W‴| > 0` by Step 4 + nonemptiness) forces a nonzero preimage.  This is
the cancellation-free heart: NOT weakened to "W‴ nonempty". -/
theorem phi4Bubble_stableForestSum_ne_zero :
    stableForestSum phi4BubbleAmbient phi4BubbleAmbient_stableBoundaryIds ≠ 0 := by
  intro h0
  have hc := congrArg (phi4CharacterTensorMul phi4BubbleAllOne phi4BubbleAllOne) h0
  rw [phi4Bubble_charTensorMul_stableForestSum, map_zero] at hc
  have hpos : 0 < (phi4WTriplePrimeIndex phi4BubbleAmbient).card :=
    Finset.card_pos.mpr phi4BubbleWTriplePrimeIndex_nonempty
  exact (Nat.cast_ne_zero.mpr hpos.ne') hc

/-! ## Step 5 — the stable coproduct is NON-PRIMITIVE on the bubble generator (HEADLINE 4, the CROWN) -/

/-- **body-665c (HEADLINE 4, the CROWN) — the stable φ⁴₄ coproduct is genuinely NON-PRIMITIVE on the bubble
generator.**  `Δᵣˢ(X_G) ≠ X_G ⊗ 1 + 1 ⊗ X_G`: expanding via `coproduct_resolved_stable_phi4_of_graph` yields
`(X_G ⊗ 1 + 1 ⊗ X_G) + stableForestSum`; primitivity would force `stableForestSum = 0`
(`add_right_eq_self`), contradicting `phi4Bubble_stableForestSum_ne_zero`.  The positive counterpart to
Figure 1: the coproduct actually computes real forest combinatorics. -/
theorem coproduct_resolved_stable_phi4_bubble_not_primitive :
    coproduct_resolved_stable_phi4 (MvPolynomial.X phi4BubbleStableGen)
      ≠ MvPolynomial.X phi4BubbleStableGen ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH)
        + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X phi4BubbleStableGen := by
  intro hprim
  unfold phi4BubbleStableGen at hprim
  rw [coproduct_resolved_stable_phi4_of_graph phi4BubbleAmbient phi4BubbleAmbient_stableCD
    phi4BubbleAmbient_stableBoundaryIds] at hprim
  set p := MvPolynomial.X (phi4BubbleAmbient.toStableResolvedPhi4HopfGen
      phi4BubbleAmbient_stableCD phi4BubbleAmbient_stableBoundaryIds) ⊗ₜ[ℚ]
        (1 : StableResolvedPhi4HopfH)
      + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X
        (phi4BubbleAmbient.toStableResolvedPhi4HopfGen
          phi4BubbleAmbient_stableCD phi4BubbleAmbient_stableBoundaryIds) with hp
  -- hprim : p + stableForestSum … = p
  have h2 : p + stableForestSum phi4BubbleAmbient phi4BubbleAmbient_stableBoundaryIds = p + 0 := by
    rw [add_zero]; exact hprim
  exact phi4Bubble_stableForestSum_ne_zero (add_left_cancel h2)

end GaugeGeometry.QFT.Combinatorial
