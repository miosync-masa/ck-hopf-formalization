/-
# SIGMA paper axiom audit

This file is the single executable audit surface for every Lean declaration
currently cited by the frozen B1/A5/B2 claim hierarchy.

Run from the root of `miosync-masa/ck-hopf-formalization` after copying this
file there:

```text
lake env lean SIGMAAxiomAudit.lean
```

The emitted `#print axioms` blocks must be copied verbatim into B3 of
`SIGMA_CK_HOPF_MASTER_LEDGER.md`.  Do not replace declaration-specific output
with the repository-wide upper bound
`[propext, Classical.choice, Quot.sound]`: small `rfl` and `by decide`
declarations may have a strictly smaller footprint.
-/

import GaugeGeometry.QFT.HopfAlgebra.BoundarySemanticCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedCarrier
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentOnePI
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemainderDelta
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentReflectionAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentDischarged
import GaugeGeometry.QFT.HopfAlgebra.AntipodeConvolution
import GaugeGeometry.QFT.HopfAlgebra.HopfAlgebra

open GaugeGeometry.QFT.Combinatorial
open GaugeGeometry.QFT.HopfAlgebra

/-! ## B2.1 — flat mechanism failures -/

#print axioms flatEdgeRetarget_not_injective
#print axioms flatLegRetarget_not_injective
#print axioms flatEdgeRetarget_multiset_collapse
#print axioms flatLegRetarget_multiset_collapse

/-! ## B2.2–B2.3 — resolved repair and correspondence -/

#print axioms resolved_insertion_internalEdges_unique
#print axioms resolved_promotedExternalLegs_unique
#print axioms forget_retarget_edge
#print axioms forget_retarget_leg
#print axioms boundaryResolvedSemanticModel
#print axioms boundarySemanticCorrespondence_holds

/-! ## B2.4 — facade-free H5.8 reindex -/

#print axioms h58_resolved_carrier_double_sum_reindex

/-! ## B2.5 — saturated carrier and absorbed leg supply -/

#print axioms canonicalLegSaturatedCarrierProperSupply
#print axioms mem_canonicalLegSaturatedCarrier_full_iff
#print axioms canonicalLegSaturatedExternalLegSaturationSupply

/-! ## B2.6–B2.9 — Parent topology, traceability, and divergence -/

#print axioms canonicalLegSaturated_parent_isOnePI
#print axioms canonicalLegSaturated_quotientRemainder_toFeynmanGraph_eq_delta
#print axioms admissibleSubgraphQuotientRemainder_divergent_reflect
#print axioms canonicalLegSaturated_parent_isDivergent
#print axioms canonicalLegSaturated_parent_isConnectedDivergent
#print axioms canonicalLegSaturatedDecontractionCDSupply

/-! ## B2.10 — unique Main Theorem -/

#print axioms coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged

/-! ## B2.11 — convolution antipode -/

#print axioms reducedConv_pow_gen_eq_zero
#print axioms AntipodeStrictForestRightReady_ofConvolution

/-! ## B2.12 — conditional flat Hopf comparison -/

#print axioms hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution
