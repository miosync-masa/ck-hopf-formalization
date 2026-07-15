import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionValueCoreBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualValueBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionMembershipAssembly

/-!
# R-6c-body-280 — recovered-region membership, value-root version (PROVED)

Two-hundred-and-eightieth genuine-body step — the three value-root region bridges (left/right/forest, bodies 278/279)
assembled with the choice-tag trichotomy (body-173, S-free) into the value-root `recovered_region_membership`: on the
value forward image, a component lies in `leftResidual ∪ rightRecovered ∪ forestRecovered` iff it is a component of the
domain outer `q.1.1.1`.  Over `fwdMapFilteredValue F V q` alone — no `S`, no `Forward`, no legacy.

## One shared `Region` by construction

The assembly is a **flat record**: it carries a single S-free region core `Region` (body-277) and a single left core
`Left` (body-279), and all six sound/complete laws reference `Region.componentToRight` / `Region.componentToForest` /
`Left.leftResidual` directly — so right and forest **cannot** carry different region maps (the mistake a
three-independent-bridge bundle would allow).  The converters `toRightBridgeSupply` / `toForestBridgeSupply` /
`toLeftBridgeSupply` rebuild bodies 278/279's records to reuse their membership iffs.

## The assembly theorem

`recovered_region_membership_value` rewrites the three membership iffs and closes with `choice_tag_trichotomy` — the
exact shape of body-173's `recovered_region_membership`, re-keyed to the value root.

Per the HALT: only the membership theorem is proved; the carrier membership, `unionOuter`, and the raw union are NOT
entered (body-281 combines this shared `Region`/`Left` with body-269's closure for the preimage / branch data / cover).
No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-280 — the value-root recovered-region bridge assembly.**  A flat record with ONE shared region core
`Region` (right + forest) and ONE left core `Left`, plus the six value-root sound/complete construction leaves. -/
structure ResolvedRecoveredRegionValueBridgeAssemblySupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The shared S-free region construction core (body-277). -/
  Region : ResolvedRegionConstructionFromSectorValueSupply D
  /-- The S-free left-residual construction core (body-279). -/
  Left : ResolvedLeftResidualConstructionValueSupply D
  /-- Right soundness. -/
  right_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ rightDomain (fwdMapFilteredValue F V q)}),
    rightPrimSelected q.1 (Region.componentToRight (fwdMapFilteredValue F V q) δ)
  /-- Right completeness. -/
  right_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    rightPrimSelected q.1 γ →
    ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredValue F V q)},
      Region.componentToRight (fwdMapFilteredValue F V q) δ = γ
  /-- Forest soundness. -/
  forest_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue F V q)}),
    forestChoiceSelected q.1 (Region.componentToForest (fwdMapFilteredValue F V q) δ)
  /-- Forest completeness. -/
  forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    forestChoiceSelected q.1 γ →
    ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredValue F V q)},
      Region.componentToForest (fwdMapFilteredValue F V q) δ = γ
  /-- Left soundness. -/
  left_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ (Left.leftResidual (fwdMapFilteredValue F V q)).elements
  /-- Left completeness. -/
  left_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Left.leftResidual (fwdMapFilteredValue F V q)).elements →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ

namespace ResolvedRecoveredRegionValueBridgeAssemblySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-280 — the right bridge over the shared region** (body-278). -/
def toRightBridgeSupply (A : ResolvedRecoveredRegionValueBridgeAssemblySupply F V) :
    ResolvedRightRegionValueCoreBridgeSupply F V where
  Construction := A.Region
  right_sound_value := A.right_sound_value
  right_complete_value := A.right_complete_value

/-- **R-6c-body-280 — the forest bridge over the shared region** (body-278). -/
def toForestBridgeSupply (A : ResolvedRecoveredRegionValueBridgeAssemblySupply F V) :
    ResolvedForestRegionValueCoreBridgeSupply F V where
  Construction := A.Region
  forest_sound_value := A.forest_sound_value
  forest_complete_value := A.forest_complete_value

/-- **R-6c-body-280 — the left bridge over the shared left core** (body-279). -/
def toLeftBridgeSupply (A : ResolvedRecoveredRegionValueBridgeAssemblySupply F V) :
    ResolvedLeftResidualValueCoreBridgeSupply F V where
  Construction := A.Left
  left_sound_value := A.left_sound_value
  left_complete_value := A.left_complete_value

/-- **R-6c-body-280 — the value-root recovered-region membership.**  On the value forward image, a component is in the
three regions iff it is a component of the domain outer — body-173's proof, re-keyed to the value root. -/
theorem recovered_region_membership_value (A : ResolvedRecoveredRegionValueBridgeAssemblySupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ (A.Left.leftResidual (fwdMapFilteredValue F V q)).elements
        ∨ γ ∈ (A.Region.rightRecovered (fwdMapFilteredValue F V q)).elements
        ∨ γ ∈ (A.Region.forestRecovered (fwdMapFilteredValue F V q)).elements)
      ↔ γ ∈ q.1.1.1.elements := by
  have hL : γ ∈ (A.Left.leftResidual (fwdMapFilteredValue F V q)).elements
      ↔ ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ :=
    A.toLeftBridgeSupply.leftResidual_forward_value_membership q γ
  have hR : γ ∈ (A.Region.rightRecovered (fwdMapFilteredValue F V q)).elements
      ↔ rightPrimSelected q.1 γ :=
    A.toRightBridgeSupply.rightRecovered_forward_value_membership q γ
  have hF : γ ∈ (A.Region.forestRecovered (fwdMapFilteredValue F V q)).elements
      ↔ forestChoiceSelected q.1 γ :=
    A.toForestBridgeSupply.forestRecovered_forward_value_membership q γ
  rw [hL, hR, hF]
  exact choice_tag_trichotomy q.1 γ

end ResolvedRecoveredRegionValueBridgeAssemblySupply

end GaugeGeometry.QFT.Combinatorial
