import GaugeGeometry.QFT.HopfAlgebra.Bialgebra
import GaugeGeometry.QFT.HopfAlgebra.Antipode
import GaugeGeometry.QFT.HopfAlgebra.AntipodeConvolution
import Mathlib.RingTheory.HopfAlgebra.Basic

/-!
# `HopfAlgebra ℚ HopfH` instance  [Sprint E H6.8]

This file assembles the Mathlib `HopfAlgebra ℚ HopfH` instance for the
forest strict coproduct artifact, completing Sprint E's pipeline.

## Conditional facades

The instance currently depends on **two** facade typeclasses, both of
which must be discharged before the final axiom audit:

* `[CoassocStrictForestH58Ready]` — Sprint D facade carrying the
  LinearMap-form coassociativity for `coproduct_strict_forest` (already
  discharged-modulo-canonical-classifier wiring; see Bialgebra.lean
  header for the canonical-discharge plan).
* `[AntipodeStrictForestRightReady]` — Sprint E facade for the right
  antipode axiom (`mul_antipode_lTensor_comul`). The left axiom
  (`mul_antipode_rTensor_comul`) is unconditionally proven in
  `Antipode.lean` as `mul_antipode_rTensor_coproduct_strict_forest`; the
  right axiom requires a forest-summation identity analogous to (but
  mathematically distinct from) H5.8 and is isolated as a payload.

## Sprint E pipeline status

* **H6.1–H6.5** — `antipodeGen_forest` (well-founded recursion),
  `antipode_forest : HopfH →ₗ[ℚ] HopfH`, `antipode_forest_one`,
  `antipode_forest_X`, `antipode_forest_mul` ✓
* **H6.6a** — Generator-level left axiom
  `mul_antipode_rTensor_coproduct_strict_forest_X` ✓
* **H6.6b** — LinearMap-form left axiom
  `mul_antipode_rTensor_coproduct_strict_forest` ✓
* **H6.7** — Right axiom isolated as facade
  `AntipodeStrictForestRightReady`
* **H6.8** — `HopfAlgebra ℚ HopfH` conditional instance (this file)

## Final-audit discharge tasks (open)

Before the unconditional `HopfAlgebra ℚ HopfH` instance and final axiom
audit `[propext, Classical.choice, Quot.sound]`, the following must be
proved:

1. `CoassocStrictForestH58Ready` discharge from canonical
   `forestComponentSplitPhiIndexedBranchClassifier` constructor.
2. `AntipodeStrictForestRightReady` discharge by proving the right
   forest-summation cancellation identity (CK 1998 §3 style).
-/

namespace GaugeGeometry.QFT.Combinatorial

section StrictForestHopfInstance

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
         [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- `HopfAlgebraStruct ℚ HopfH` carrying the forest antipode
`antipode_forest`. Extends the Sprint E Bialgebra instance.

The `[CoassocStrictForestH58Ready]` hypothesis is inherited from the
underlying Bialgebra instance. -/
noncomputable instance instHopfAlgebraStructHopfHStrictForest
    [CoassocStrictForestH58Ready] :
    HopfAlgebraStruct ℚ HopfH where
  antipode := antipode_forest

/-- **Sprint E H6.8 — conditional `HopfAlgebra ℚ HopfH` instance** for
the forest strict coproduct artifact.

Both Sprint D's `CoassocStrictForestH58Ready` and Sprint E's
`AntipodeStrictForestRightReady` facades must be in scope. The left
antipode axiom is supplied unconditionally by H6.6b
(`mul_antipode_rTensor_coproduct_strict_forest`); the right axiom is
read off the facade. -/
noncomputable instance instHopfAlgebraHopfHStrictForest
    [CoassocStrictForestH58Ready]
    [AntipodeStrictForestRightReady] :
    HopfAlgebra ℚ HopfH where
  mul_antipode_rTensor_comul :=
    mul_antipode_rTensor_coproduct_strict_forest
  mul_antipode_lTensor_comul :=
    AntipodeStrictForestRightReady.mul_antipode_lTensor_coproduct_strict_forest

/-- **Cross-file JAR certificate (coassociativity boundary).**  The H5.8
coassociativity facade `CoassocStrictForestH58Ready` — hence the entire
coalgebra/coassociativity layer of `HopfH` — is **synthesized** from exactly the
two boundary-semantics facades (`ForestGraphInsertionUniquenessModel`,
`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`) plus the
reverse forest-contraction power-counting reflection
(`IsDivergenceReflectedByAdmissibleForestContract`) in the ambient
`DivergenceMeasure` environment.  The former `CoassocStrictForestH58CoverData`
obligation is auto-derived (`CoassocStrictForestH58CoverData_ofReflection`): no
residual cover-data hypothesis.  This compiles cross-file, certifying that the
coassociativity side is closed modulo the two boundary-semantics interfaces. -/
theorem coassocStrictForestH58Ready_ofBoundaryFacadesAndReflection
    [ForestGraphInsertionUniquenessModel]
    [ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel]
    [IsDivergenceReflectedByAdmissibleForestContract] :
    CoassocStrictForestH58Ready :=
  inferInstance

/-- Cross-file certificate with the right antipode supplied as a hypothesis
(`AntipodeStrictForestRightReady`).  Superseded by the convolution version below,
which discharges it; kept as the explicit-hypothesis form. -/
theorem hopfAlgebraHopfH_ofBoundaryFacadesAndReflection
    [ForestGraphInsertionUniquenessModel]
    [ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel]
    [IsDivergenceReflectedByAdmissibleForestContract]
    [AntipodeStrictForestRightReady] :
    Nonempty (HopfAlgebra ℚ HopfH) :=
  ⟨inferInstance⟩

/-- **Cross-file JAR certificate — full `HopfAlgebra ℚ HopfH` on exactly two
boundary-semantics facades.**  Both the coassociativity facade
(`CoassocStrictForestH58Ready`) *and* the right antipode facade
(`AntipodeStrictForestRightReady`, via `AntipodeStrictForestRightReady_ofConvolution`)
are synthesized — the latter by the convolution / local-nilpotency route
(`AntipodeConvolution.lean`), **without** the CK §3 kernel
`AntipodeForestRightCoreIdentity`.  So the conditional Hopf structure is gated on
**precisely** the two boundary-semantics interfaces
(`ForestGraphInsertionUniquenessModel`,
`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` — both
false on the flat carrier, theorems on the boundary-resolved carrier) plus the
ambient power-counting environment (including the reverse forest-contraction
reflection).  The right antipode axiom is no longer a separate cancellation
kernel: it follows from the left antipode identity, coassociativity, and local
nilpotency of the reduced convolution operator.  This compiles, certifying the
final dependency boundary. -/
theorem hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution
    [ForestGraphInsertionUniquenessModel]
    [ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel]
    [IsDivergenceReflectedByAdmissibleForestContract] :
    Nonempty (HopfAlgebra ℚ HopfH) :=
  ⟨inferInstance⟩

end StrictForestHopfInstance

end GaugeGeometry.QFT.Combinatorial
