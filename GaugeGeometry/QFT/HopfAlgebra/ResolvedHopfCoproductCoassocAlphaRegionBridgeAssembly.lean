import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionValueAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaNativeFilteredValue

/-!
# R-6c-body-475 — the alpha recovered-region bridge assembly (stage 1 of the tag-chain mirror) (PARALLEL)

Four-hundred-and-seventy-fifth genuine-body step — the FIRST of three staged mirrors (`assembly → closure →
tags/membership`) of the recovered-region tag chain over the alpha value root.  This body mirrors ONLY the 8-field bridge
assembly (body-280): the shared `Region` / `Left` cores (V-independent) plus the six sound/complete bridges, with every
forward image retyped from `fwdMapFilteredValue` to `fwdMapFilteredAlphaValue F V q` — `q` stays FILTERED (never weakened
to a raw split choice).

* `ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply` — the 8-field alpha assembly;
* `ResolvedRecoveredRegionValueBridgeAssemblySupply.toAlpha` — the legacy adapter into the assembly over `V.toFiltered`;
  every bridge field is the legacy field verbatim (the body-471 `fwdMapFilteredAlphaValue F V.toFiltered = fwdMapFiltered
  Value F V` is `rfl`, so the types are DEFEQ), and `Region` / `Left` project across by `rfl`.

Per the HALT/guards: NO closure / disjointness / `recovered_raw_mem`; NO tag functions / exclusivity; the
`recoveredFilteredPreimageValue` is NOT consumed; the canonical six-bridge geometry is NOT re-proved; old structures are
NOT edited in place; NO `quot_eq`, NO `W'` membership, NO new geometry; strict `StarProm` / `InnerStarRaw` NOT restored;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no
rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-475 — the alpha recovered-region bridge assembly.**  The body-280 8-field assembly with every forward
image over `fwdMapFilteredAlphaValue`; `Region` / `Left` are the shared V-independent cores. -/
structure ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply
    (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The shared S-free region construction core (body-277). -/
  Region : ResolvedRegionConstructionFromSectorValueSupply D
  /-- The S-free left-residual construction core (body-279). -/
  Left : ResolvedLeftResidualConstructionValueSupply D
  /-- Right soundness. -/
  right_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue F V q)}),
    rightPrimSelected q.1 (Region.componentToRight (fwdMapFilteredAlphaValue F V q) δ)
  /-- Right completeness. -/
  right_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    rightPrimSelected q.1 γ →
    ∃ δ : {x // x ∈ rightDomain (fwdMapFilteredAlphaValue F V q)},
      Region.componentToRight (fwdMapFilteredAlphaValue F V q) δ = γ
  /-- Forest soundness. -/
  forest_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue F V q)}),
    forestChoiceSelected q.1 (Region.componentToForest (fwdMapFilteredAlphaValue F V q) δ)
  /-- Forest completeness. -/
  forest_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    forestChoiceSelected q.1 γ →
    ∃ δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue F V q)},
      Region.componentToForest (fwdMapFilteredAlphaValue F V q) δ = γ
  /-- Left soundness. -/
  left_sound_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ →
      γ ∈ (Left.leftResidual (fwdMapFilteredAlphaValue F V q)).elements
  /-- Left completeness. -/
  left_complete_value : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Left.leftResidual (fwdMapFilteredAlphaValue F V q)).elements →
      ResolvedCoassocSplitChoice.leftSelectedConcrete q.1 γ

/-- **R-6c-body-475 ∎ — the legacy adapter into the alpha assembly over `V.toFiltered`.**  Every field is the legacy field
verbatim (the body-471 forward-map agreement is `rfl`, so the types are definitionally equal). -/
def ResolvedRecoveredRegionValueBridgeAssemblySupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (A : ResolvedRecoveredRegionValueBridgeAssemblySupply F V) :
    ResolvedRecoveredRegionAlphaValueBridgeAssemblySupply F V.toFiltered where
  Region := A.Region
  Left := A.Left
  right_sound_value := A.right_sound_value
  right_complete_value := A.right_complete_value
  forest_sound_value := A.forest_sound_value
  forest_complete_value := A.forest_complete_value
  left_sound_value := A.left_sound_value
  left_complete_value := A.left_complete_value

end GaugeGeometry.QFT.Combinatorial
