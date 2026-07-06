import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagForwardScout

/-!
# R-6c-body-199 — backward-choice final leaf: the whole chain down to `forest_choiceAt_eq`

Hundred-and-ninety-ninth genuine-body step, wiring the entire backward-choice round-trip down to its single fresh
leaf `forest_choiceAt_eq` (body-198).  After bodies 192–198 dismantled the `HEq`, this body assembles the chain

```text
backward_choice_heq  (body-164)
  ⇐ heq_of_index_eq + outer_partition            (body-193)
  ⇐ choice_component_eq                          (body-194)   [inl tags via sector bridges]
  ⇐ forest_value_eq                              (body-196)   [+ body-188 tag pinning]
  ⇐ forestTag_forward_eq                         (body-198)   [Sum.inr.inj]
  ⇐ forest_choiceAt_eq                           (body-198)   THE single fresh leaf
```

into one supply, and produces body-164's `ResolvedRecoveredChoiceRoundTripSupply`.

## The one fresh leaf, and the reused machinery

`ResolvedBackwardChoiceFinalLeafSupply D S Region` fields the single genuinely fresh fact `forest_choiceAt_eq` (the
forward round-trip parent recovery — the reconstructed forest tag is `q`'s own choice value) alongside the reused
already-proved / reusable inputs:

* `forestTag_fwd` — the forward image's forest tag (body-198);
* `forest_choiceAt_eq` — **the fresh leaf**;
* `recoverChoice_forest_pin` — the body-188 tag pinning (`recoverChoice (fwdMap q) = inr forestTag_fwd`);
* `outer_partition` — body-160's `recoveredOuter_partition` (the proved index transport);
* `Left` / `Right` / `Forest` — the three sector bridges (bodies 172/170/171).

`.toRecoveredChoiceRoundTripSupply` runs the chain 198 → 196 → 194 → 193 → 164, so body-164's `backward_choice_heq`
is supplied entirely by `forest_choiceAt_eq` plus the reused tags / bridges / transport.

## Consequence — backward-choice closed to a homogeneous forest-choice parent recovery

The backward-choice round-trip residual is now exactly the single homogeneous `Bool ⊕ ForestIdx` equality
`forest_choiceAt_eq`, whose only content is the forward round-trip parent recovery (`occ.γ = γ`).  Everything else on
the backward-choice side — the `HEq` transport, the `inl` tag cases, the `Sum.inr.inj` value step — is proved.  The
next body (body-200) opens the occurrence concretization: `forestTag_fwd := occurrence.B`, `toOccurrence` `hchoice`,
`parent_recovered`, `Sum.inr.inj`.

Per the HALT: `forest_choiceAt_eq`'s body (the occurrence / parent recovery) is not entered; the tag pinning /
bridges / transport are reused; this body is the chain wiring only.

Landed:

* `ResolvedBackwardChoiceFinalLeafSupply D S Region` — the single fresh leaf + the reused inputs;
* `.toForestValueEqDecompositionSupply` / `.toChoiceComponentCasesSupply` / `.toBackwardChoiceHEqAssemblySupply` —
  bodies 196 / 194 / 193;
* `.toRecoveredChoiceRoundTripSupply` — body-164 (the backward-choice round-trip closed on `forest_choiceAt_eq`).

Toolkit body (like body-181).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-199 — the backward-choice final leaf supply.**  The single fresh `forest_choiceAt_eq` (the forward
round-trip parent recovery) together with the reused machinery: the forward forest tag, the body-188 tag pinning,
the body-160 index transport, and the three sector bridges. -/
structure ResolvedBackwardChoiceFinalLeafSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The forward image's reconstructed forest tag (body-198). -/
  forestTag_fwd : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements}),
    γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements →
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- **The single fresh leaf**: the reconstructed forest tag is `q`'s own choice value at `γ`. -/
  forest_choiceAt_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
    q.2 γ (Finset.mem_attach _ _) = Sum.inr (forestTag_fwd q γ hmem)
  /-- Body-188 tag pinning (reused). -/
  recoverChoice_forest_pin : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements)
    (hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements),
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = Sum.inr (forestTag_fwd q γ hmem)
  /-- Body-160 index transport (reused, proved). -/
  outer_partition : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements
  /-- Body-172 left residual sector bridge (reused). -/
  Left : ResolvedLeftResidualSectorBridgeSupply D S Region
  /-- Body-170 right region sector bridge (reused). -/
  Right : ResolvedRightRegionSectorBridgeSupply D S Region
  /-- Body-171 forest region sector bridge (reused). -/
  Forest : ResolvedForestRegionSectorBridgeSupply D S Region

namespace ResolvedBackwardChoiceFinalLeafSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-199 — body-198's forest tag forward decomposition supply.** -/
def toForestTagForwardDecompositionSupply (F : ResolvedBackwardChoiceFinalLeafSupply D S Region) :
    ResolvedForestTagForwardDecompositionSupply D S Region where
  forestTag_fwd := fun {G} q γ hmem => F.forestTag_fwd q γ hmem
  forest_choiceAt_eq := fun {G} q γ hmem => F.forest_choiceAt_eq q γ hmem

/-- **R-6c-body-199 — body-196's forest value-equality supply.** -/
def toForestValueEqDecompositionSupply (F : ResolvedBackwardChoiceFinalLeafSupply D S Region) :
    ResolvedForestValueEqDecompositionSupply D S Region :=
  F.toForestTagForwardDecompositionSupply.toForestValueEqDecompositionSupply
    (fun {G} q γ hu hmem => F.recoverChoice_forest_pin q γ hu hmem)

/-- **R-6c-body-199 — body-194's choice component cases supply.** -/
def toChoiceComponentCasesSupply (F : ResolvedBackwardChoiceFinalLeafSupply D S Region) :
    ResolvedChoiceComponentCasesSupply D S Region :=
  F.toForestValueEqDecompositionSupply.toChoiceComponentCasesSupply F.Left F.Right F.Forest

/-- **R-6c-body-199 — body-193's backward-choice HEq assembly supply.** -/
def toBackwardChoiceHEqAssemblySupply (F : ResolvedBackwardChoiceFinalLeafSupply D S Region) :
    ResolvedBackwardChoiceHEqAssemblySupply D S Region :=
  F.toChoiceComponentCasesSupply.toBackwardChoiceHEqAssemblySupply
    (fun {G} q => F.outer_partition q)

/-- **R-6c-body-199 — body-164's recovered-choice round-trip supply (backward-choice closed on the fresh leaf).** -/
def toRecoveredChoiceRoundTripSupply (F : ResolvedBackwardChoiceFinalLeafSupply D S Region) :
    ResolvedRecoveredChoiceRoundTripSupply D S Region :=
  F.toBackwardChoiceHEqAssemblySupply.toRecoveredChoiceRoundTripSupply

end ResolvedBackwardChoiceFinalLeafSupply

end GaugeGeometry.QFT.Combinatorial
