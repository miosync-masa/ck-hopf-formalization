import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForwardGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueRoundTrip

/-!
# R-6c-body-479 — the alpha round-trip completion node (PROVED)

Four-hundred-and-seventy-ninth genuine-body step — the value-root re-key of body-285 onto the alpha recovered side: the
alpha backward-outer, the backward-choice HEq, and the two whole round-trips for `fwdMapFilteredAlphaValue F V`.  The
design invariant: the round-trip leaf supply owns `Data` ONCE, and BOTH forward fields read the same filtered witness
`qz := Data.recoveredFilteredPreimageAlphaValue z` — so the forward round-trip needs NO membership hypothesis (the
filtered witness is issued from `Data`, not supplied as an external certificate).

* `ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply.{left,right,forest}Recovered_forward_alpha_membership` +
  `recovered_region_membership_alpha_value` — the six-bridge membership assembly (body-280 shape) over the alpha map;
* `ResolvedRegionAlphaValueClosureSupply.backward_outer_alpha_value` — `unionOuterAlphaValue (fwd q) = q.1.1` (body-284
  shape, no new geometry);
* `ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply` — `Data` + the two forward fields + the honest `forest_value_eq`
  leaf; `ResolvedForwardQuotientAlphaValueGeometrySupply.toRoundTripLeafSupply` builds it from the body-478 theorems;
* `choice_component_eq_alpha_value` / `backward_choice_alpha_value` / `backward_roundtrip_alpha_value` — the backward
  choice assembly (body-285 shape);
* `forward_roundtrip_alpha_value` — `fwd (Data.recoveredFilteredPreimageAlphaValue z) = z`, MEMBERSHIP-FREE;
* `ResolvedRecoveredPreimageValueRoundTripLeafSupply.toAlpha` — the legacy adapter over `V.toFiltered`.

Per the HALT/guards: the outer-mixing inverse / cover are NOT entered; `forest_value_eq` is NOT derived (honest leaf); the
canonical geometry inhabitants are NOT re-proved; no downstream structure is migrated in place; the filtered witness is NOT
re-wrapped under a different proof; NO `quot_eq`, NO `W'` membership, NO new geometry; strict `StarProm` / `InnerStarRaw`
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

namespace ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-479 — the alpha right region membership bridge** (body-278 shape, from the six bridges). -/
theorem rightRecovered_forward_alpha_membership
    (A : ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (A.Region.rightRecovered (fwdMapFilteredAlphaValue F V q)).elements
      ↔ rightPrimSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.rightRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact A.right_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := A.right_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-479 — the alpha forest region membership bridge** (body-278 shape, from the six bridges). -/
theorem forestRecovered_forward_alpha_membership
    (A : ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (A.Region.forestRecovered (fwdMapFilteredAlphaValue F V q)).elements
      ↔ forestChoiceSelected q.1 γ := by
  rw [ResolvedRegionConstructionFromSectorValueSupply.forestRecovered_elements_eq]
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact A.forest_sound_value q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := A.forest_complete_value q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-479 — the alpha left region membership bridge** (body-279 shape, from the six bridges). -/
theorem leftResidual_forward_alpha_membership
    (A : ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (A.Left.leftResidual (fwdMapFilteredAlphaValue F V q)).elements
      ↔ ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ :=
  ⟨A.left_complete_value q γ, A.left_sound_value q γ⟩

/-- **R-6c-body-479 — the alpha recovered-region membership** (body-280 shape).  On the alpha forward image, a component
is in the three regions iff it is a component of the domain outer. -/
theorem recovered_region_membership_alpha_value
    (A : ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ (A.Left.leftResidual (fwdMapFilteredAlphaValue F V q)).elements
        ∨ γ ∈ (A.Region.rightRecovered (fwdMapFilteredAlphaValue F V q)).elements
        ∨ γ ∈ (A.Region.forestRecovered (fwdMapFilteredAlphaValue F V q)).elements)
      ↔ γ ∈ q.1.1.1.elements := by
  rw [A.leftResidual_forward_alpha_membership q γ, A.rightRecovered_forward_alpha_membership q γ,
    A.forestRecovered_forward_alpha_membership q γ]
  exact choice_tag_trichotomy q.1 γ

end ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply

/-- **R-6c-body-479 — the alpha backward outer round-trip** (body-284 shape, no leaf).  The reconstruction's outer of an
alpha forward image is the original domain outer, from the six bridges. -/
theorem ResolvedRegionAlphaValueClosureSupply.backward_outer_alpha_value
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (C : ResolvedRegionAlphaValueClosureSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    C.unionOuterAlphaValue (fwdMapFilteredAlphaValue F V q) = q.1.1 := by
  apply Subtype.ext
  apply ResolvedAdmissibleSubgraph.ext_elements
  apply Finset.ext
  intro γ
  rw [C.mem_unionOuterAlphaValue_iff]
  exact C.Assembly.recovered_region_membership_alpha_value q γ

/-- **R-6c-body-479 — the alpha round-trip leaf supply.**  `Data` is owned ONCE; both forward fields read the same
filtered witness `Data.recoveredFilteredPreimageAlphaValue z`. -/
structure ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply
    (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The alpha membership supply (body-477). -/
  Data : ResolvedRecoveredPreimageAlphaValueMemSupply F V
  /-- Forward outer: the reconstruction's re-promoted outer is the original outer (body-478). -/
  forward_outer_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (Data.recoveredFilteredPreimageAlphaValue z).1 = z.1.1
  /-- Forward quotient: the reconstruction's quotient forest is the original `B`, on the FILTERED witness (body-478). -/
  forward_quotient_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (V.quotientForestRaw (Data.recoveredFilteredPreimageAlphaValue z)) z.2
  /-- The forest-component exact-value match (the honest body-285 leaf, re-keyed to the alpha forward map). -/
  forest_value_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterAlphaValue (fwdMapFilteredAlphaValue F V q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
    γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered
        (fwdMapFilteredAlphaValue F V q)).elements →
    q.1.2 γ (Finset.mem_attach _ _) = Sum.inr B →
    Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue F V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = Sum.inr B

/-- **R-6c-body-479 — the canonical constructor from the body-478 forward geometry.**  `Data` and the two forward fields
are the body-478 theorems; only `forest_value_eq` is supplied as the honest leaf. -/
def ResolvedForwardQuotientAlphaValueGeometrySupply.toRoundTripLeafSupply
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (R : ResolvedForwardQuotientAlphaValueGeometrySupply F V)
    (forest_value_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
      (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
      (hu : γ.1 ∈ (R.Geom.Data.Tags.Closure.unionOuterAlphaValue
          (fwdMapFilteredAlphaValue F V q)).1.elements)
      (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
      γ.1 ∈ (R.Geom.Data.Tags.Closure.Assembly.Region.forestRecovered
          (fwdMapFilteredAlphaValue F V q)).elements →
      q.1.2 γ (Finset.mem_attach _ _) = Sum.inr B →
      R.Geom.Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue F V q) ⟨γ.1, hu⟩
          (Finset.mem_attach _ _) = Sum.inr B) :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V where
  Data := R.Geom.Data
  forward_outer_value := R.Geom.forward_outer_alpha_value
  forward_quotient_value := R.forward_quotient_alpha_value
  forest_value_eq := forest_value_eq

namespace ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-479 — the componentwise choice agreement** (body-285 shape, alpha root). -/
theorem choice_component_eq_alpha_value (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (R.Data.Tags.Closure.unionOuterAlphaValue (fwdMapFilteredAlphaValue F V q)).1.elements) :
    R.Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue F V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = q.1.2 γ (Finset.mem_attach _ _) := by
  rcases hc : q.1.2 γ (Finset.mem_attach _ _) with (b | B)
  · cases b
    · have hr : rightPrimSelected q.1 γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Region.rightRecovered
          (fwdMapFilteredAlphaValue F V q)).elements :=
        (R.Data.Tags.Closure.Assembly.rightRecovered_forward_alpha_membership q γ.1).mpr hr
      exact R.Data.Tags.right_tag_alpha (fwdMapFilteredAlphaValue F V q) ⟨γ.1, hu⟩ hmem
    · have hl : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Left.leftResidual
          (fwdMapFilteredAlphaValue F V q)).elements :=
        (R.Data.Tags.Closure.Assembly.leftResidual_forward_alpha_membership q γ.1).mpr hl
      exact R.Data.Tags.left_tag_alpha (fwdMapFilteredAlphaValue F V q) ⟨γ.1, hu⟩ hmem
  · have hf : forestChoiceSelected q.1 γ.1 := ⟨γ.2, B, hc⟩
    have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered
        (fwdMapFilteredAlphaValue F V q)).elements :=
      (R.Data.Tags.Closure.Assembly.forestRecovered_forward_alpha_membership q γ.1).mpr hf
    exact R.forest_value_eq q γ hu B hmem hc

/-- **R-6c-body-479 — the backward choice HEq** (body-193's transport, alpha root). -/
theorem backward_choice_alpha_value (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    HEq (R.Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue F V q)) q.1.2 := by
  have he : (R.Data.Tags.Closure.unionOuterAlphaValue (fwdMapFilteredAlphaValue F V q)).1.elements
      = q.1.1.1.elements := by
    rw [R.Data.Tags.Closure.backward_outer_alpha_value q]
  exact heq_of_index_eq (T := fun x => Bool ⊕ (D.supply (x.toResolvedFeynmanGraph)).ForestIdx)
    (f := R.Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue F V q)) (g := q.1.2) he
    (fun x ha hb => R.choice_component_eq_alpha_value q ⟨x, hb⟩ ha)

/-- **R-6c-body-479 — the whole backward round-trip** (`Sigma.ext` of outer + choice). -/
theorem backward_roundtrip_alpha_value (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    R.Data.Tags.recoveredPreimageAlphaValue (fwdMapFilteredAlphaValue F V q) = q.1 :=
  Sigma.ext (R.Data.Tags.Closure.backward_outer_alpha_value q) (R.backward_choice_alpha_value q)

/-- **R-6c-body-479 ∎ — the whole forward round-trip, MEMBERSHIP-FREE.**  The filtered witness is issued from `Data`, so
no external membership certificate is threaded (contrast body-285's `hmem` argument). -/
theorem forward_roundtrip_alpha_value (R : ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    fwdMapFilteredAlphaValue F V (R.Data.recoveredFilteredPreimageAlphaValue z) = z :=
  Sigma.ext (Subtype.ext (R.forward_outer_value z)) (R.forward_quotient_value z)

end ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply

/-! ## Legacy adapter (over `V.toFiltered`, DEFEQ via the body-471/476/478 `rfl` anchors) -/

/-- **R-6c-body-479 — the legacy round-trip leaf adapter into the alpha supply over `V.toFiltered`.**  `Data` is the
body-478 adapter; both forward fields transport by DEFEQ (the filtered witness's `.1` is the legacy raw choice, `rfl`;
`V.toFiltered.quotientForestRaw` is defeq); the forest leaf is verbatim. -/
def ResolvedRecoveredPreimageValueRoundTripLeafSupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V) :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply F V.toFiltered where
  Data := R.Data.toAlpha
  forward_outer_value := R.forward_outer_value
  forward_quotient_value := R.forward_quotient_value
  forest_value_eq := R.forest_value_eq

/-- **R-6c-body-479 — the legacy backward compatibility anchor** (`rfl`). -/
theorem ResolvedRecoveredPreimageValueRoundTripLeafSupply.toAlpha_backward_roundtrip
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    R.toAlpha.Data.Tags.recoveredPreimageAlphaValue (fwdMapFilteredAlphaValue F V.toFiltered q)
      = R.Data.Tags.recoveredPreimageValue (fwdMapFilteredValue F V q) :=
  rfl

end GaugeGeometry.QFT.Combinatorial
