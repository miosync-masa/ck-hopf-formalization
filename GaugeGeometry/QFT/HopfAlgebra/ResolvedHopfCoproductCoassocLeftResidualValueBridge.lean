import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualConstruction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-body-279 — S-free left-residual construction + left value bridge (PROVED)

Two-hundred-and-seventy-ninth genuine-body step — the left region, value-root canonical.  Unlike the right/forest
sides (sector images, bodies 275/276/278), the left residual is a **filter** of the target outer `A = z.1`, so its
S-free core and its value bridge are handled in one body.  The scout (body-273) confirmed body-157 never reads `S`; here
the single representation-predicate field is re-declared `S`-free, `leftResidual` / `leftResidual_elements_eq` (rfl) are
re-derived, and the membership bridge is proved from a value-root sound/complete pair.

## The S-free core

`ResolvedLeftResidualConstructionValueSupply D` fields `representedInQuotient z γ` (body-157) with `S` gone.
`leftResidual z = z.1.1.filterElements (fun γ => ¬ representedInQuotient z γ)`; `leftResidual_elements_eq` is `rfl`.

## The left value bridge

`ResolvedLeftResidualValueCoreBridgeSupply F V` carries the S-free core plus the value-root
`left_sound_value` / `left_complete_value` (honest construction leaves — `leftSelectedConcrete` is `choiceAt = inl true`,
the `X γ ⊗ 1` primitive).  `leftResidual_forward_value_membership` is then just `⟨complete, sound⟩`, over
`fwdMapFilteredValue F V q` alone.

If downstream geometry ever supplies `representedInQuotient ↔ rightPrimSelected ∨ forestChoiceSelected`, the
sound/complete pair can be derived from it; absent that, they stay honest construction leaves (the definitional meaning
of "not represented ⇔ left-selected", the `inl true` complement of the `inl false` / `inr` sector components).

Per the HALT: only the left S-free core + its value bridge are defined/proved; `.toValueCore` is a migration check
(not canonical); the right/forest bridges are NOT mixed into the left proof; the recovered-membership assembly (body-280)
is NOT entered.  No selected-outer carrier membership, no `Forward`, no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-279 — the S-free left-residual construction core.**  Body-157's representation predicate with `S`
removed from the declaration type. -/
structure ResolvedLeftResidualConstructionValueSupply (D : ResolvedCoproductProperForestData) where
  /-- A component of the target outer `A` is represented by the quotient `B` (a survivor or remnant image). -/
  representedInQuotient : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop

namespace ResolvedLeftResidualConstructionValueSupply

/-- **R-6c-body-279 — the recovered left region** (S-free; the filter of `A`'s unrepresented components). -/
noncomputable def leftResidual (L : ResolvedLeftResidualConstructionValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements (fun γ => ¬ L.representedInQuotient z γ)

/-- **R-6c-body-279 — the left region's element shape** (`rfl`; success criterion). -/
@[simp] theorem leftResidual_elements_eq (L : ResolvedLeftResidualConstructionValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (L.leftResidual z).elements = z.1.1.elements.filter (fun γ => ¬ L.representedInQuotient z γ) :=
  rfl

end ResolvedLeftResidualConstructionValueSupply

/-- **R-6c-body-279 — the S-free reduct of the old S-indexed left-residual supply** (migration check, `rfl`).  Not on
the canonical path. -/
def ResolvedLeftResidualConstructionSupply.toValueCore
    {S : ResolvedConcreteSummandBundleSupply D} (L : ResolvedLeftResidualConstructionSupply D S) :
    ResolvedLeftResidualConstructionValueSupply D where
  representedInQuotient := L.representedInQuotient

/-- **R-6c-body-279 — the value-root left region bridge supply.**  The S-free core plus the value-root left
sound/complete round-trip (honest construction leaves). -/
structure ResolvedLeftResidualValueCoreBridgeSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The S-free left-residual construction core (this body). -/
  Construction : ResolvedLeftResidualConstructionValueSupply D
  /-- Value-root left soundness: a left-selected component is unrepresented (lies in `leftResidual`). -/
  left_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ (Construction.leftResidual (fwdMapFilteredValue F V q)).elements
  /-- Value-root left completeness: an unrepresented component of `A` is left-selected. -/
  left_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Construction.leftResidual (fwdMapFilteredValue F V q)).elements →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ

/-- **R-6c-body-279 — the value-root left region membership bridge.**  `leftResidual (fwdMapFilteredValue F V q)`'s
components are exactly `q`'s left-selected (`inl true`) components — just `⟨complete, sound⟩`. -/
theorem ResolvedLeftResidualValueCoreBridgeSupply.leftResidual_forward_value_membership
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (B : ResolvedLeftResidualValueCoreBridgeSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (B.Construction.leftResidual (fwdMapFilteredValue F V q)).elements
      ↔ ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ :=
  ⟨B.left_complete_value q γ, B.left_sound_value q γ⟩

end GaugeGeometry.QFT.Combinatorial
