# Appendix B — the raw `#print axioms` audit output

*Verbatim kernel output for every paper-facing theorem, captured from the committed audit
modules at tag `v2.1.0` (Lean `v4.29.0`, Mathlib `v4.29.0`). `propext`, `Classical.choice`,
and `Quot.sound` are the three standard axioms of Lean's classical core; no `sorryAx`
(no `sorry`/`admit`), no `Lean.ofReduceBool` (no `native_decide`), and no project-level axiom
appears anywhere.*

**Reproduction.** From the repository root:

```
lake exe cache get
lake env lean GaugeGeometry/QFT/HopfAlgebra/Phi4StableChainLedgerAudit.lean
```

and for the paper façade names, `#print axioms` any of the `GaugeGeometry.QFT.Paper.*`
theorems after `import GaugeGeometry.QFT.HopfAlgebra.PaperMainTheorems`.

---

## B.1 The paper façade (`PaperMainTheorems.lean`, namespace `GaugeGeometry.QFT.Paper`)

```
'GaugeGeometry.QFT.Paper.paper_thm1_early_quotient_obstruction' does not depend on any axioms
'GaugeGeometry.QFT.Paper.paper_thm2_naive_completion_obstruction' depends on axioms: [propext, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm2'_obstruction_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm3_stable_normalization' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paperForestBlockEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm4_multiplicity_preserving_correspondence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm5_phi4_coassociativity' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm5'_coproduct_non_primitive' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm6_birkhoff_factorization' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Paper.paper_thm7_carrier_support_discrepancy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.phi4StableCK_renormalization_settlement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

*(Note: `paper_thm1_early_quotient_obstruction` depends on NO axioms at all — the flat
counterexamples are closed by pure kernel computation.)*

## B.2 The internal theorem ledger (`Phi4StableChainLedgerAudit.lean` — full output: pinned `#check` types followed by the axiom footprints)

```
@nested_direct_singletonProfile_ne : ∀ {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
  (e : ResolvedFeynmanEdge),
  {ResolvedFeynmanSubgraph.existingLegId (γ.boundaryExternalLeg e)} ≠ {ResolvedFeynmanSubgraph.boundaryLegId e}
@stableBoundaryIterate_idempotent : ∀ {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
  (δ : ResolvedFeynmanSubgraph (stableBoundaryNormalForm γ)),
  ResolvedExternalLegSaturated G γ →
    ResolvedExternalLegSaturated (stableBoundaryNormalForm γ) δ →
      stableBoundaryIterate γ δ = stableBoundaryNormalForm (rootRelativeInner γ δ)
@stablePhi4ForestBlockEquiv : {G : ResolvedFeynmanGraph} →
  (hSt : StableResolvedBoundaryIds G) → StablePhi4MixedSplitChoice G hSt ≃ Phi4WTriplePrimeInverseCodomain G
@stableForestBlock_finiteSum_reindex : ∀ {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G),
  stableMixedSplitChoiceFiniteSum hSt = stableInverseCodomainTripleSum hSt
coproduct_resolved_stable_phi4_coassociative : stableCoassocLeft = stableCoassocRight
@phi4Bogoliubov_birkhoff_factorization : ∀ {B : Type u_1} [inst : CommRing B] [inst_1 : Algebra ℚ B]
  (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B),
  phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ = phi4BogoliubovRenormalizedCharacter S φ
@phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector : ∀ {B : Type u_1} [inst : CommRing B]
  [inst_1 : Algebra ℚ B] (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B),
  phi4CarrierGapWDoublePrimeComparisonValue S φ -
      (phi4BogoliubovRenormalizedCharacter S φ) (MvPolynomial.X phi4CarrierGapStableGen) =
    ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
      phi4CarrierGapBogoliubovForestWeight S φ A
@phi4StableCK_renormalization_settlement : ∀ {B : Type u_1} [inst : CommRing B] [inst_1 : Algebra ℚ B]
  (S : Phi4RotaBaxterSubtractionScheme B) (φ : StableResolvedPhi4HopfH →ₐ[ℚ] B),
  phi4CharacterConvolution (phi4BogoliubovCountertermCharacter S φ) φ = phi4BogoliubovRenormalizedCharacter S φ ∧
    phi4CarrierGapWDoublePrimeComparisonValue S φ -
        (phi4BogoliubovRenormalizedCharacter S φ) (MvPolynomial.X phi4CarrierGapStableGen) =
      ∑ A ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient \ phi4WTriplePrimeIndex phi4CarrierGapAmbient,
        phi4CarrierGapBogoliubovForestWeight S φ A
'GaugeGeometry.QFT.Combinatorial.nested_direct_singletonProfile_ne' depends on axioms: [propext, Quot.sound]
'GaugeGeometry.QFT.Combinatorial.stableBoundaryIterate_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.stablePhi4ForestBlockEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'GaugeGeometry.QFT.Combinatorial.stableForestBlock_finiteSum_reindex' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.coproduct_resolved_stable_phi4_coassociative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.phi4Bogoliubov_birkhoff_factorization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'GaugeGeometry.QFT.Combinatorial.phi4StableCK_renormalization_settlement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
