import GaugeGeometry.QFT.HopfAlgebra.BoundaryResolvedCounterexamples
import GaugeGeometry.QFT.HopfAlgebra.Phi4NestedBoundaryIdCoherenceAudit
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBoundaryIdempotence
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableGenuineForestBlockEquiv
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableFiniteSumReindex
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoproductCoassociativityLaw
import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBogoliubovFactorization
import GaugeGeometry.QFT.HopfAlgebra.Phi4CarrierGapBogoliubovDroppedSector
import GaugeGeometry.QFT.HopfAlgebra.Phi4BubbleNestedObstruction

/-!
# Paper main theorems — a compact façade over the φ⁴₄ development

**One import point for the paper's headline results.** The development is ~150k lines of Lean;
a reader should be able to inspect the *main results* without entering the construction site.
This module re-exports the headline theorems under **paper-facing names** (`paper_thm1 … paper_thm7`)
with **no new mathematics** — each is a single `exact`/`:=` of an already-proved, axiom-clean term.
Import `GaugeGeometry.QFT.HopfAlgebra.PaperMainTheorems` and read the five (resp. seven) statements.

Axiom footprint of every export is verified in the companion ledger
`Phi4StableChainLedgerAudit.lean` (`#print axioms` = `[propext, Classical.choice, Quot.sound]`,
`paper_thm1`/`paper_thm2` need only `[propext, Quot.sound]`).

## The coassociativity paper — five main theorems

| Paper | Statement | Evidence (bodies) | Internal name |
|---|---|---|---|
| **Thm 1** | Early-quotient obstruction: flat quotienting does **not** retain the identity data needed for coherent contraction/reconstruction. | four flat counterexamples | `flat{Edge,Leg}Retarget_not_injective` |
| **Thm 2** | Naive boundary-completion obstruction: the naive boundary-completed presentation is **not** stable under nested forest contraction. | 625/596 | `nested_direct_singletonProfile_ne` |
| **Thm 2′** | The obstruction is **inhabited**: a concrete φ⁴ configuration (the bubble witness) on which the naive nested completion provably differs from the root-relative one — the ∃-form of Thm 2. | 665d | `exists_nested_completion_obstruction` |
| **Thm 3** | Stable normalization: root-relative stable completion is **idempotent** under nested contraction. | 627–630 (esp. 628) | `stableBoundaryIterate_idempotent` |
| **Thm 4** | Multiplicity-preserving forest correspondence: mixed split choices and iterated quotient forests are in **genuine bijection**, preserving summand weights (no dedup of forest occurrences). | 640, 648, 649 | `stablePhi4ForestBlockEquiv` + `stableForestBlock_finiteSum_reindex` |
| **Thm 5** | Concrete φ⁴₄ coassociativity: the stable resolved φ⁴₄ coproduct is **coassociative** on the full polynomial algebra. | 650b, 651 | `coproduct_resolved_stable_phi4_coassociativity_law` |

## Renormalization extension (QFT-R2) — two further main theorems

| Paper | Statement | Evidence | Internal name |
|---|---|---|---|
| **Thm 6** | Connes–Kreimer Birkhoff factorization: `φ₋ ⋆ φ = φ₊`. | 656–663 | `phi4Bogoliubov_birkhoff_factorization` |
| **Thm 7** | Carrier-support renormalization discrepancy: the forest-support change propagates **exactly** to the renormalized amplitude (dropped-sector counterterm-times-quotient sum). | 664 | `phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector` |

Thm 2 (the no-go) and Thm 3 (the repair) are the **paired mathematical novelty**: the naive
completion is provably not relabeling-stable, and the root-relative completion provably is —
which is *why* the coassociativity proof lives on the stable carrier.
-/

namespace GaugeGeometry.QFT.Paper

open GaugeGeometry.QFT.Combinatorial
open GaugeGeometry.QFT.HopfAlgebra
open scoped BigOperators
open scoped Classical

/-- File-scoped re-exposure of the φ⁴ divergence-measure family instance (NOT a permanent/global
instance — scoped exactly as in the audited source files), so the W″ / W‴ carrier types in
Theorem 7 elaborate. -/
local instance instPhi4DivergenceMeasureFamilyPaper : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Theorem 1 — early-quotient obstruction (flat quotienting loses identity data) -/

/-- **Paper Theorem 1 — early-quotient obstruction.**  Flat quotienting does not retain the
identity data required for coherent contraction and reconstruction: the flat edge- and
leg-retarget maps are **not injective** (distinct edges/legs collapse under a vertex
identification). This is the `mechanism`-level counterexample that motivates the whole
boundary-resolved carrier. -/
theorem paper_thm1_early_quotient_obstruction :
    (∃ (f : VertexId → VertexId) (e₁ e₂ : FeynmanEdge),
        e₁ ≠ e₂ ∧ flatEdgeRetarget f e₁ = flatEdgeRetarget f e₂)
      ∧ (∃ (f : VertexId → VertexId) (ℓ₁ ℓ₂ : ExternalLeg),
          ℓ₁ ≠ ℓ₂ ∧ flatLegRetarget f ℓ₁ = flatLegRetarget f ℓ₂) :=
  ⟨flatEdgeRetarget_not_injective, flatLegRetarget_not_injective⟩

/-! ## Theorem 2 — naive boundary-completion obstruction (the no-go) -/

/-- **Paper Theorem 2 — naive boundary-completion obstruction.**  The naive
(nested/second-order) boundary-completed presentation is **not** stable under nested forest
contraction: the nested route re-encodes an inherited boundary leg with an EVEN id
(`existingLegId ∘ boundaryExternalLeg`) while the direct route uses an ODD id
(`boundaryLegId`), and the `mapPerm`-invariant singleton leg-id profiles differ — so no
vertex relabeling can bridge a naive-nested completion to the direct one. Forcing the naive
round-trip raw would break coassociativity. -/
theorem paper_thm2_naive_completion_obstruction {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    ({ResolvedFeynmanSubgraph.existingLegId (γ.boundaryExternalLeg e)} : Multiset ResolvedLegId)
      ≠ {ResolvedFeynmanSubgraph.boundaryLegId e} :=
  nested_direct_singletonProfile_ne γ e

/-- **Paper Theorem 2′ — the obstruction is inhabited (the ∃-form of Theorem 2).**  There EXISTS a
concrete φ⁴ configuration — an ambient graph with unique edge ids, a subgraph `γ`, a nested subgraph
`δ` of `γ`'s boundary completion, and an inherited outer boundary edge `e` — on which the naive
nested boundary completion PROVABLY differs (as a resolved class) from the root-relative one.
Witnessed by the one-loop bubble (`phi4BubbleAmbient`/`phi4BubbleInner`/`phi4BubbleNested`, edge
`e2 (0–2)`); notably Figure 1 canNOT witness this (its `inheritedOuter` is proved empty), so the
witness is a genuinely separate configuration. Theorem 2 states the obstruction; Theorem 2′ shows it
occurs on a real φ⁴ graph. -/
theorem paper_thm2'_obstruction_inhabited :
    ∃ (G : ResolvedFeynmanGraph) (γ : ResolvedFeynmanSubgraph G)
      (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
      (e : ResolvedFeynmanEdge),
      G.EdgeIdsUnique ∧ e ∈ inheritedOuter γ δ ∧
      δ.boundaryCompletedResolvedGraph.toResolvedClass
        ≠ (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass :=
  exists_nested_completion_obstruction

/-! ## Theorem 3 — stable normalization (idempotent root-relative completion) -/

/-- **Paper Theorem 3 — stable normalization.**  The root-relative stable boundary completion is
**idempotent** under the nested contraction operation: iterating it on a saturated subforest `δ`
of a normalized `γ` returns the normal form of the root-relative inner completion,
`stableBoundaryIterate γ δ = stableBoundaryNormalForm (rootRelativeInner γ δ)`. This is the
repair paired with Theorem 2 — completing in one step or two steps agrees judgmentally, which is
what makes every forest-block round-trip a genuine raw equality. -/
theorem paper_thm3_stable_normalization {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ) :
    stableBoundaryIterate γ δ = stableBoundaryNormalForm (rootRelativeInner γ δ) :=
  stableBoundaryIterate_idempotent γ δ hγsat hδsat

/-! ## Theorem 4 — multiplicity-preserving forest correspondence -/

/-- **Paper Theorem 4a — the forest correspondence is a genuine bijection.**  Mixed split
choices and iterated quotient forests are in bijection (an `Equiv`), on the *raw* carriers —
so no ID-distinct forest occurrence is collapsed. -/
noncomputable def paperForestBlockEquiv {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G) :
    StablePhi4MixedSplitChoice G hSt ≃ Phi4WTriplePrimeInverseCodomain G :=
  stablePhi4ForestBlockEquiv hSt

/-- **Paper Theorem 4b — the correspondence preserves summand weights.**  Under the bijection of
Theorem 4a, the two residual finite sums coincide **term for term** — the mixed-split-choice sum
equals the iterated-quotient-forest sum, with exact component multiplicity and no dedup of forest
occurrences. -/
theorem paper_thm4_multiplicity_preserving_correspondence {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G) :
    stableMixedSplitChoiceFiniteSum hSt = stableInverseCodomainTripleSum hSt :=
  stableForestBlock_finiteSum_reindex hSt

/-! ## Theorem 5 — concrete φ⁴₄ coassociativity (the coassociativity paper's headline) -/

/-- **Paper Theorem 5 — concrete φ⁴₄ coassociativity.**  The stable resolved φ⁴₄ coproduct
`Δᵣˢ := coproduct_resolved_stable_phi4` is **coassociative** on the whole polynomial algebra:
the standard coassociativity square `assoc ∘ (Δᵣˢ ⊗ id) ∘ Δᵣˢ = (id ⊗ Δᵣˢ) ∘ Δᵣˢ`. Unconditional
— no divergence-law hypotheses, no typeclass-instance arguments. -/
theorem paper_thm5_phi4_coassociativity :
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ
        StableResolvedPhi4HopfH StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom.comp
      (Algebra.TensorProduct.map coproduct_resolved_stable_phi4
        (AlgHom.id ℚ StableResolvedPhi4HopfH))).comp
      coproduct_resolved_stable_phi4
      = (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
          coproduct_resolved_stable_phi4).comp
        coproduct_resolved_stable_phi4 :=
  coproduct_resolved_stable_phi4_coassociativity_law

/-! ## Theorem 6 — Connes–Kreimer Birkhoff factorization (renormalization extension, QFT-R2) -/

/-- **Paper Theorem 6 — the CK Birkhoff factorization** `φ₋ ⋆ φ = φ₊` on the whole algebra, for any
Rota–Baxter subtraction scheme `S` and character `φ` into a target commutative ℚ-algebra `B`. -/
theorem paper_thm6_birkhoff_factorization {B : Type*} [CommRing B] [Algebra ℚ B]
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ
      = phi4BogoliubovRenormalizedCharacter S φ :=
  phi4Bogoliubov_birkhoff_factorization S φ

/-! ## Theorem 7 — carrier-support renormalization discrepancy (renormalization extension, QFT-R2) -/

/-- **Paper Theorem 7 — carrier-support renormalization discrepancy.**  For the concrete Figure-1
φ⁴ graph, the change in admissible-forest support (`W‴ ⊊ W″`) propagates **exactly** to the
renormalized amplitude: the difference between the broader-support comparison value and the genuine
renormalized character is the sum of genuine counterterm-times-quotient weights `φ₋(L_F)·φ(R_F)`
over the dropped forest sector `W″ ∖ W‴`. -/
theorem paper_thm7_carrier_support_discrepancy {B : Type*} [CommRing B] [Algebra ℚ B]
    (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B) :
    phi4CarrierGapWDoublePrimeComparisonValue S φ
        - phi4BogoliubovRenormalizedCharacter S φ (MvPolynomial.X phi4CarrierGapStableGen)
      = ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
          phi4CarrierGapBogoliubovForestWeight S φ A :=
  phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector S φ

end GaugeGeometry.QFT.Paper
