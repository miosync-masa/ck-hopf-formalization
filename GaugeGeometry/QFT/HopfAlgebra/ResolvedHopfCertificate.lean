import GaugeGeometry.QFT.HopfAlgebra.ResolvedPayloadModel

/-!
# Resolved Hopf structure certificate (Track R-4-full, Phase 7)

Rather than register the resolved coproduct as a competing `Coalgebra`/`Bialgebra`
instance on the flat carrier `HopfH` (which would clash with the existing instance),
we record a **certificate**: the coproduct assembled from a resolved payload family
(`ResolvedHopfPayloadFamily.resolvedCoproduct`) satisfies all the Hopf-structure
laws.  Every law transfers for free, because that coproduct *equals* the flat
strict-forest coproduct as an algebra/linear map (Phase 4c,
`resolvedCoproduct_eq_flat` / `…_toLinearMap_eq_flat`).

Combined with `resolvedHopfPayloadFamily_exists` (Phase 6c), this gives an explicit,
provably-existent resolved-payload coproduct that obeys coassociativity, the counit
laws, and both antipode axioms — without packaging a duplicate typeclass instance.
-/

set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- The Hopf-structure laws for a resolved-payload coproduct, as a `Prop` bundle
(a certificate, not a competing typeclass instance). -/
structure ResolvedHopfStructureCertificate (PF : ResolvedHopfPayloadFamily)
    [CoassocStrictForestH58Ready] [AntipodeStrictForestRightReady] : Prop where
  /-- Coassociativity (Phase 5). -/
  coassoc :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ HopfH HopfH HopfH).toLinearMap ∘ₗ
        PF.resolvedCoproduct.toLinearMap.rTensor HopfH ∘ₗ PF.resolvedCoproduct.toLinearMap
      =
    PF.resolvedCoproduct.toLinearMap.lTensor HopfH ∘ₗ PF.resolvedCoproduct.toLinearMap
  /-- Right counit law (`(ε ⊗ id) ∘ Δ = includeRight`). -/
  rTensor_counit :
    (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)).comp PF.resolvedCoproduct
      = Algebra.TensorProduct.includeRight
  /-- Left counit law (`(id ⊗ ε) ∘ Δ = includeLeft`). -/
  lTensor_counit :
    (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit).comp PF.resolvedCoproduct
      = Algebra.TensorProduct.includeLeft
  /-- Left antipode axiom (`mul ∘ (S ⊗ id) ∘ Δ = η ∘ ε`). -/
  antipode_left :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.rTensor HopfH).comp PF.resolvedCoproduct.toLinearMap)
      = (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap
  /-- Right antipode axiom (`mul ∘ (id ⊗ S) ∘ Δ = η ∘ ε`). -/
  antipode_right :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.lTensor HopfH).comp PF.resolvedCoproduct.toLinearMap)
      = (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap

/-- **The resolved-payload coproduct satisfies the Hopf-structure laws.**  Every
field transfers from the flat strict-forest coproduct via the Phase 4c equalities;
the resolved structure introduces no new obligation. -/
theorem resolvedHopfStructureCertificate_holds (PF : ResolvedHopfPayloadFamily)
    [CoassocStrictForestH58Ready] [AntipodeStrictForestRightReady] :
    ResolvedHopfStructureCertificate PF where
  coassoc := PF.resolvedCoproduct_coassoc
  rTensor_counit := by
    rw [PF.resolvedCoproduct_eq_flat]; exact rTensor_counit_comp_coproduct_strict_forest_algHom
  lTensor_counit := by
    rw [PF.resolvedCoproduct_eq_flat]; exact lTensor_counit_comp_coproduct_strict_forest_algHom
  antipode_left := by
    rw [PF.resolvedCoproduct_toLinearMap_eq_flat]
    exact mul_antipode_rTensor_coproduct_strict_forest
  antipode_right := by
    rw [PF.resolvedCoproduct_toLinearMap_eq_flat]
    exact AntipodeStrictForestRightReady.mul_antipode_lTensor_coproduct_strict_forest

/-- **Phase 7 headline.**  There exists a resolved payload family whose coproduct
satisfies all the Hopf-structure laws — the canonical constant-id lift family of
Phase 6c.  (Non-vacuity + the full law bundle, without a duplicate typeclass
instance on the flat carrier.) -/
theorem exists_resolvedHopfStructureCertificate
    [CoassocStrictForestH58Ready] [AntipodeStrictForestRightReady] :
    ∃ PF : ResolvedHopfPayloadFamily, ResolvedHopfStructureCertificate PF :=
  ⟨canonicalResolvedHopfPayloadFamily,
    resolvedHopfStructureCertificate_holds canonicalResolvedHopfPayloadFamily⟩

end GaugeGeometry.QFT.Combinatorial
