import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRoundTripLeaf

/-!
# R-6c-body-480 — the alpha-native outer-mixing inverse + witnessSplit cover (PROVED)

Four-hundred-and-eightieth genuine-body step — the value-root re-key of the outer-mixing inverse (body-308) and the
witnessSplit cover (body-253) onto the alpha recovered side, but with the design STRENGTHENED by the body-479 dividend:
the inverse is a FILTERED value BY CONSTRUCTION, so there is no longer a reason to split the raw value from a separate
membership field.  Both the inverse-membership field and the forward codomain-membership hypothesis are ELIMINATED — the
round-trips are unconditional.

* `ResolvedOuterMixingAlphaValueInverseSupply` — three fields (`invFun : cod → FilteredForestBlockDom`, `forward`,
  `backward`), no `invFun_mem`, no `hz`;
* `ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply.toOuterMixingAlphaValueInverse` — the canonical inhabitant from
  body-479 (`invFun := recoveredFilteredPreimageAlphaValue`, `forward := forward_roundtrip_alpha_value`, `backward :=
  Subtype.ext ∘ backward_roundtrip_alpha_value`);
* `ResolvedWitnessSplitFilteredAlphaValueCoverSupply` — the matching three-field cover; `.toCover` is projection-only from
  the inverse; `ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply.toCover` issues it via the inverse (no per-branch
  concrete data — the raw recovered choice is already branch-agnostic, fixed through body-479);
* the projection anchors (`invFun` / `witnessSplit` value is `recoveredPreimageAlphaValue`, `rfl`);
* the legacy compatibility path: an old round-trip supply issues the alpha inverse / cover ONLY after `.toAlpha` (body-479);
  there is deliberately NO adapter from the old `ResolvedOuterMixingValueInverseSupply` — its `forward` is `hz`-dependent,
  a genuine capability gap recorded honestly.

Per the HALT/guards: the alpha bijection side / coassoc theorem are NOT connected; no branch-specific concrete data is
duplicated; the codomain-membership hypothesis is NOT reinstated; the old cover / inverse are NOT edited; the 71-file
downstream migration is NOT started; NO `quot_eq`, NO `W'` membership, NO new geometry; strict `StarProm` / `InnerStarRaw`
NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **R-6c-body-480 — the normalized alpha outer-mixing inverse supply.**  The inverse is a FILTERED value directly; the
membership field and the forward codomain hypothesis are gone. -/
structure ResolvedOuterMixingAlphaValueInverseSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The filtered outer-mixing inverse `(A, B) ↦ ⟨(A', p), mem⟩`. -/
  invFun : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → FilteredForestBlockDom D G
  /-- Forward round-trip: `fwd ∘ invFun = id` on the codomain (unconditional). -/
  forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    fwdMapFilteredAlphaValue F V (invFun z) = z
  /-- Backward round-trip: `invFun ∘ fwd = id` on the filtered domain. -/
  backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    invFun (fwdMapFilteredAlphaValue F V q) = q

namespace ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-480 — the canonical alpha inverse from the round-trip supply.**  All three fields come from body-479's
membership-free round-trips; no geometry floor, no per-component data. -/
noncomputable def toOuterMixingAlphaValueInverse
    (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V) :
    ResolvedOuterMixingAlphaValueInverseSupply F V where
  invFun := fun {_G} z => R.Data.recoveredFilteredPreimageAlphaValue z
  forward := fun {_G} z => R.forward_roundtrip_alpha_value z
  backward := fun {_G} q => Subtype.ext (R.backward_roundtrip_alpha_value q)

/-- **R-6c-body-480 — the inverse's value is the recovered preimage** (`rfl`). -/
@[simp] theorem toOuterMixingAlphaValueInverse_invFun_val
    (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (R.toOuterMixingAlphaValueInverse.invFun z).1 = R.Data.Tags.recoveredPreimageAlphaValue z :=
  rfl

end ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

/-- **R-6c-body-480 — the normalized alpha witnessSplit cover.**  The three-field cover with a filtered `witnessSplit`
and unconditional round-trips. -/
structure ResolvedWitnessSplitFilteredAlphaValueCoverSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The backward map, total on the codomain, landing in the filtered domain by construction. -/
  witnessSplit : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → FilteredForestBlockDom D G
  /-- Forward round-trip on the filtered domain (unconditional). -/
  forward_witness : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    fwdMapFilteredAlphaValue F V (witnessSplit z) = z
  /-- Backward round-trip on the filtered domain. -/
  backward_witness : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    witnessSplit (fwdMapFilteredAlphaValue F V q) = q

/-- **R-6c-body-480 — the cover from the inverse** (projection-only). -/
def ResolvedOuterMixingAlphaValueInverseSupply.toCover
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (I : ResolvedOuterMixingAlphaValueInverseSupply F V) :
    ResolvedWitnessSplitFilteredAlphaValueCoverSupply F V where
  witnessSplit := I.invFun
  forward_witness := I.forward
  backward_witness := I.backward

namespace ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-480 — the canonical alpha cover, issued via the inverse.**  No per-branch concrete data: the raw recovered
choice is branch-agnostic (fixed through body-479). -/
noncomputable def toCover (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V) :
    ResolvedWitnessSplitFilteredAlphaValueCoverSupply F V :=
  R.toOuterMixingAlphaValueInverse.toCover

/-- **R-6c-body-480 — the cover's witness is the same recovered preimage** (`rfl`). -/
@[simp] theorem toCover_witnessSplit_val
    (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (R.toCover.witnessSplit z).1 = R.Data.Tags.recoveredPreimageAlphaValue z :=
  rfl

end ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

/-! ## Legacy compatibility (via `.toAlpha`; NO adapter from the old `hz`-dependent inverse) -/

namespace ResolvedRecoveredPreimageValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-480 — the legacy round-trip supply issues the alpha inverse over `V.toFiltered`.**  It goes through the
body-479 `.toAlpha`; there is deliberately no adapter from the old `ResolvedOuterMixingValueInverseSupply`, whose `forward`
is `hz`-dependent — a genuine capability gap. -/
noncomputable def toAlphaOuterMixingInverse (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedOuterMixingAlphaValueInverseSupply F V.toFiltered :=
  R.toAlpha.toOuterMixingAlphaValueInverse

/-- **R-6c-body-480 — the legacy round-trip supply issues the alpha cover over `V.toFiltered`.** -/
noncomputable def toAlphaCover (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedWitnessSplitFilteredAlphaValueCoverSupply F V.toFiltered :=
  R.toAlpha.toCover

/-- **R-6c-body-480 — the legacy alpha inverse value is the legacy raw recovered choice** (`rfl`). -/
theorem toAlphaOuterMixingInverse_invFun_val
    (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (R.toAlphaOuterMixingInverse.invFun z).1 = R.Data.Tags.recoveredPreimageValue z :=
  rfl

end ResolvedRecoveredPreimageValueRoundTripLeafSupply

end GaugeGeometry.QFT.Combinatorial
