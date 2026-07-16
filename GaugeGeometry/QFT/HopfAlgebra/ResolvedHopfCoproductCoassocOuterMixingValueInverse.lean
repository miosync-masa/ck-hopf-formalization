import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainOrphanCoverAudit

/-!
# R-6c-body-308 — the outer-mixing value inverse: the raw bijection inverse, inhabited (PROVED)

Three-hundred-and-eighth genuine-body step — the outer-mixing inverse construction, realized.  Following the body-307
verdict (retire the per-component geometry-floor route; re-target the RAW outer-mixing `invFun` directly), the scout found
the raw inverse is **already built and its round-trips already proved**: it is `recoveredPreimageValue` (body-282), with
`forward_roundtrip_value` / `backward_roundtrip_value` PROVED (body-285) and branch membership PROVED (body-283).  This body
DEFINES the user's target `ResolvedOuterMixingValueInverseSupply (F) (V)` — the four raw-bijection fields
(`invFun` / `invFun_mem` / `forward` / `backward`) — and INHABITS it outright from a single
`ResolvedRecoveredPreimageValueRoundTripLeafSupply F V`.  No `componentToForest`, no per-component parent membership, no
region-core geometry floor, no `FilteredForestBlockCod` migration, no codomain filter.

## The build-path (body-308 scout verdict: (II) RAW-CONSTRUCT, already assembled; sole residual = carrier closure)

* **(I) LIFT-READY is FALSE.**  There is no completed flat forest-block `Finset.sum_bij'`
  (`grep Finset.sum_bij' Coassoc.lean` → empty); the flat `forestComponentSplitPhiInverseConstruction`
  (Coassoc.lean:27993) is itself an un-inhabited data structure, and the resolved-lift forget lemmas
  (`forget_complete` / `forget_injective`, ResolvedCoproduct.lean:246/253) are facade fields that provably cannot lift
  equality for a fresh `A'` (CanonicalMembershipRewriteScout.lean:29-47 — forget is not globally injective).  So there is
  nothing to lift.

* **(II) RAW-CONSTRUCT is the route and the pieces exist.**  `invFun := recoveredPreimageValue z =
  ⟨unionOuterValue z, recoverChoiceValue z⟩` (OuterUnionRegionTagValue.lean:140) is the direct inverse of
  `selectedOuterRawOf` (`leftOf ∪ promotedOf`, Promote.lean:61) / `quotientForestRaw` (`survivor ∪ remnant`,
  ConcreteSummandValue.lean:76); `forward` = `forward_roundtrip_value` (RecoveredPreimageValueRoundTrip.lean:122, from the
  proved `forward_outer_value` ForwardOuterValue.lean:175 + the round-trip leaf `forward_quotient_value`); `backward` =
  `backward_roundtrip_value` (:116, from `backward_outer_value` body-280 + the proved `backward_choice_value` :105);
  `invFun_mem` = a `by_cases` over `resolvedIsForestImage` dispatching `forestPreimage_mem` / `mixedPreimage_mem`
  (RecoveredPreimageValueMem.lean:86/92).  `summand_agree` is `invFun`-free (ForestBlockBijection.lean:114 /
  SummandAgreeValue.lean:70) — untouched by the inverse swap.

* **(III) The SOLE genuine residual is the carrier closure** `recovered_raw_mem` / `selectedOuter_mem`
  (ParametricCarrierClosure.lean:111, "recovered `A' ∈ D.carrier G`"), a model primitive for abstract `D` exactly as
  before — and it is now buried inside the round-trip leaf's `Data` (body-283 membership supply), NOT a per-`z` geometry
  obligation.  The canonical carrier (`ResolvedProperForestFiniteCover`, complete divergent-subgraph enumeration)
  discharges it; the geometry-floor route ultimately required the SAME closure, only after an extra false leaf (297/298).

## Consequence

The genuine phase-1b critical object — the raw outer-mixing inverse of the forest-block forward map — is fully reduced to
ONE named input, the round-trip leaf supply `ResolvedRecoveredPreimageValueRoundTripLeafSupply F V` (body-285), whose
remaining honest leaves are `forward_quotient_value` (HEq), the mixed classifier leaves `mixed_ne_pR` / `mixed_ne_pL`,
`forest_value_eq`, and — inside `Data` — the carrier closure `recovered_raw_mem`.  The over-typed geometry-floor
(297/298, body-299) is bypassed entirely: it was a valid conditional theorem but a dead concrete route.

Per the HALT: this body constructs `ResolvedOuterMixingValueInverseSupply` and its inhabitant from the round-trip supply;
it does NOT inhabit the round-trip supply's remaining leaves, nor the carrier closure (both named as the next fronts); no
`FilteredForestBlockCod`, no codomain filter, no `componentToForest`; no facade, no flat term, no `forgetHopf`.  The
imports keep the pin honest against body-285/307.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-308 — the outer-mixing value inverse supply.**  The four raw-bijection fields of the forest-block
forward map's inverse: `invFun` (codomain → domain), its domain-carrier membership, and the two round-trips.  This is the
live phase-1b target that replaces the retired per-component geometry-floor route (body-307). -/
structure ResolvedOuterMixingValueInverseSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The raw outer-mixing inverse `(A, B) ↦ (A', p)` (`A'` the recovered sub-outer; `A ⊋ A'` absorbed). -/
  invFun : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ForestBlockDomType D G
  /-- The inverse lands in the domain carrier. -/
  invFun_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    z ∈ forestBlockCodFinset G → invFun z ∈ forestBlockDomFinset G
  /-- Forward round-trip: `fwd ∘ invFun = id` on the codomain. -/
  forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G),
    fwdMapFilteredValue F V ⟨invFun z, invFun_mem z hz⟩ = z
  /-- Backward round-trip: `invFun ∘ fwd = id` on the (filtered) domain. -/
  backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    invFun (fwdMapFilteredValue F V q) = q.1

namespace ResolvedRecoveredPreimageValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-308 — total domain-carrier membership of the recovered preimage.**  A `by_cases` over
`resolvedIsForestImage` dispatching the two branch memberships (body-283); independent of any codomain membership. -/
theorem recoveredPreimageValue_mem (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    R.Data.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G := by
  by_cases h : resolvedIsForestImage z.1 z.2
  · exact R.Data.forestPreimage_mem z h
  · exact R.Data.mixedPreimage_mem z h

/-- **R-6c-body-308 — the outer-mixing value inverse, inhabited from the round-trip supply.**  All four raw-bijection
fields come from body-285's proved round-trips + body-283's branch membership; no geometry floor, no `componentToForest`. -/
noncomputable def toOuterMixingInverse (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedOuterMixingValueInverseSupply F V where
  invFun := fun {_G} z => R.Data.Tags.recoveredPreimageValue z
  invFun_mem := fun {_G} z _hz => R.recoveredPreimageValue_mem z
  forward := fun {_G} z _hz => R.forward_roundtrip_value z (R.recoveredPreimageValue_mem z)
  backward := fun {_G} q => R.backward_roundtrip_value q

end ResolvedRecoveredPreimageValueRoundTripLeafSupply

end GaugeGeometry.QFT.Combinatorial
