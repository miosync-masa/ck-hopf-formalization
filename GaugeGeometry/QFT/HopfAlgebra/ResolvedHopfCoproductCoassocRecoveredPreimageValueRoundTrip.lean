import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBackwardOuterValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBackwardChoiceHEqAssembly

/-!
# R-6c-body-285 — the two whole value round-trips from the three leaves (PROVED)

Two-hundred-and-eighty-fifth genuine-body step — the dependent-equality assembly.  It takes the three genuine leaves
(`forward_outer_value`, `forward_quotient_value`, `forest_value_eq`) and PROVES the two classifier-free whole
round-trips for `fwdMapFilteredValue F V`:

* backward: `recoveredPreimageValue (fwdMapFilteredValue F V q) = q.1`;
* forward:  `fwdMapFilteredValue F V ⟨recoveredPreimageValue z, hmem⟩ = z`.

Everything except the three leaves is proved by reusing body-193's generic `heq_of_index_eq`, body-284's
`backward_outer_value`, the value tags (body-282), and the value region bridges (bodies 278/280) — mirroring the
total-root bodies 193/194 exactly, with `fwdMap S` → `fwdMapFilteredValue F V` and no `S`-keyed geometry (body-200's
occurrence machinery is NOT used; its content is the honest `forest_value_eq` leaf).

## Componentwise choice agreement (body-194, value)

`choice_component_eq_value` cases on the original choice `q.1.2 γ`:
`inl false` → right bridge + `right_tag`; `inl true` → left bridge + `left_tag`; `inr B` → forest bridge +
`forest_value_eq` (leaf).

## The whole round-trips

`backward_choice_value` = `heq_of_index_eq` with index equality `backward_outer_value` (body-284) and the componentwise
agreement.  `backward_roundtrip_value` / `forward_roundtrip_value` are the two `Sigma.ext`s; the forward one is
independent of the membership proof `hmem` (`fwdMapFilteredValue` reads the raw `.1` only, proof-irrelevant `.2`).

Per the HALT: only the three leaves remain; everything else is proved; body-193's generic transport is reused; no
`S`-keyed occurrence geometry; the four branch specs / `.toCover` are body-286.  No `S` / `Forward` / legacy in any
declaration type.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-285 — the three round-trip leaves.**  The two forward-reconstruction facts + the forest-component
exact-value match; everything else is proved from these. -/
structure ResolvedRecoveredPreimageValueRoundTripLeafSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283): tags + forest-nonempty + the two mixed inequalities. -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- Leaf 1 — forward outer: the reconstruction's re-promoted outer is the original outer. -/
  forward_outer_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (Data.Tags.recoveredPreimageValue z) = z.1.1
  /-- Leaf 2 — forward quotient: the reconstruction's quotient forest is the original `B` (heterogeneous). -/
  forward_quotient_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (V.quotientForestRaw (Data.Tags.recoveredPreimageValue z)) z.2
  /-- Leaf 3 — the forest-component exact-value match (value analog of body-194's `forest_value_eq`). -/
  forest_value_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
    γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements →
    q.1.2 γ (Finset.mem_attach _ _) = Sum.inr B →
    Data.Tags.recoverChoiceValue (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _) = Sum.inr B

namespace ResolvedRecoveredPreimageValueRoundTripLeafSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-285 — the componentwise choice agreement** (body-194, value root). -/
theorem choice_component_eq_value (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (R.Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements) :
    R.Data.Tags.recoverChoiceValue (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = q.1.2 γ (Finset.mem_attach _ _) := by
  rcases hc : q.1.2 γ (Finset.mem_attach _ _) with (b | B)
  · cases b
    · have hr : rightPrimSelected q.1 γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Region.rightRecovered
          (fwdMapFilteredValue F V q)).elements :=
        (R.Data.Tags.Closure.Assembly.toRightBridgeSupply.rightRecovered_forward_value_membership
          q γ.1).mpr hr
      exact R.Data.Tags.right_tag (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem
    · have hl : ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Left.leftResidual
          (fwdMapFilteredValue F V q)).elements :=
        (R.Data.Tags.Closure.Assembly.toLeftBridgeSupply.leftResidual_forward_value_membership
          q γ.1).mpr hl
      exact R.Data.Tags.left_tag (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem
  · have hf : forestChoiceSelected q.1 γ.1 := ⟨γ.2, B, hc⟩
    have hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered
        (fwdMapFilteredValue F V q)).elements :=
      (R.Data.Tags.Closure.Assembly.toForestBridgeSupply.forestRecovered_forward_value_membership
        q γ.1).mpr hf
    exact R.forest_value_eq q γ hu B hmem hc

/-- **R-6c-body-285 — the backward choice HEq** (body-193's transport, value root). -/
theorem backward_choice_value (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    HEq (R.Data.Tags.recoverChoiceValue (fwdMapFilteredValue F V q)) q.1.2 := by
  have he : (R.Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements
      = q.1.1.1.elements := by
    rw [R.Data.Tags.Closure.backward_outer_value q]
  exact heq_of_index_eq (T := fun x => Bool ⊕ (D.supply (x.toResolvedFeynmanGraph)).ForestIdx)
    (f := R.Data.Tags.recoverChoiceValue (fwdMapFilteredValue F V q)) (g := q.1.2) he
    (fun x ha hb => R.choice_component_eq_value q ⟨x, hb⟩ ha)

/-- **R-6c-body-285 — the whole backward round-trip** (`Sigma.ext` of outer + choice). -/
theorem backward_roundtrip_value (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    R.Data.Tags.recoveredPreimageValue (fwdMapFilteredValue F V q) = q.1 :=
  Sigma.ext (R.Data.Tags.Closure.backward_outer_value q) (R.backward_choice_value q)

/-- **R-6c-body-285 — the whole forward round-trip** (`Sigma.ext` of outer + quotient; independent of `hmem`). -/
theorem forward_roundtrip_value (R : ResolvedRecoveredPreimageValueRoundTripLeafSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hmem : R.Data.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G) :
    fwdMapFilteredValue F V ⟨R.Data.Tags.recoveredPreimageValue z, hmem⟩ = z :=
  Sigma.ext (Subtype.ext (R.forward_outer_value z)) (R.forward_quotient_value z)

end ResolvedRecoveredPreimageValueRoundTripLeafSupply

end GaugeGeometry.QFT.Combinatorial
