import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBackwardChoiceHEqAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge

/-!
# R-6c-body-194 — choice component cases: `choice_component_eq` split into three tag cases

Hundred-and-ninety-fourth genuine-body step, splitting body-192's componentwise choice agreement into its three
`Sum`-tag cases.  With the three sector bridges (bodies 170/171/172) and the region tags (body-146), the two `inl`
cases are **proved** outright; only the `inr` value match (`forest_value_eq`) remains as the single fresh leaf.

## The three cases (PROVED except the `inr` value)

For a component `γ` of `q`, case on `q.2 γ` (= the original choice `choiceAt q γ`):

* **`inl false`** — `γ` is right-primitive (`rightPrimSelected q γ`, `⟨γ.2, hc⟩`); bridge (body-170)
  `rightRecovered_forward_membership` places `γ ∈ rightRecovered (fwdMap q)`; the region tag (body-146)
  `right_tag` gives `recoverChoice (fwdMap q) ⟨γ,_⟩ = inl false`.  ✓
* **`inl true`** — `γ` is left-selected (`leftSelectedConcrete q γ`); bridge (body-172) → `γ ∈ leftResidual
  (fwdMap q)`; `left_tag` → `inl true`.  ✓
* **`inr B`** — `γ` is a forest choice (`forestChoiceSelected q γ`, `⟨γ.2, B, hc⟩`); bridge (body-171) → `γ ∈
  forestRecovered (fwdMap q)`.  The region tag `forest_tag` only gives `∃ B', recoverChoice = inr B'`; the **value
  match** `B' = B` is the single fresh fact, fielded as `forest_value_eq`.

So `choice_component_eq` is **proved** by these three cases: the `inl` halves from the tags + bridges, the `inr`
half from `forest_value_eq`.

## The supply

`ResolvedChoiceComponentCasesSupply D S Region` fields the three sector bridges and the fresh `forest_value_eq`:

```text
forest_value_eq : γ ∈ forestRecovered (fwdMap q) → q.2 γ = inr B →
                    recoverChoice (fwdMap q) ⟨γ,_⟩ = inr B
```

`.choice_component_eq` is proved, and `.toBackwardChoiceHEqAssemblySupply` (given the index transport
`outer_partition`, body-160) produces body-193's assembly supply — so the backward-choice `HEq` reduces, through
bodies 193/192, to `forest_value_eq` alone.

## Consequence

The backward-choice round-trip residual is now the single `inr` value fact `forest_value_eq` (the choice-value
de-contraction: the recovered forest tag on a forward image equals the original forest index) plus the reused tag /
bridge machinery and the index transport.  `forward_quotient_heq` is untouched.

Per the HALT: `forest_value_eq`'s body (the forest-index de-contraction) is not entered; the region tags / sector
bridges are reused; the two `inl` cases are proved; the `HEq` assembly is body-193's.

Landed:

* `ResolvedChoiceComponentCasesSupply D S Region` — the three bridges + the fresh `forest_value_eq`;
* `.choice_component_eq` — body-192's componentwise `Eq` (PROVED from the tags/bridges + `forest_value_eq`);
* `.toBackwardChoiceHEqAssemblySupply` — body-193's assembly supply.

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

/-- **R-6c-body-194 — the choice component cases supply.**  The three sector bridges (left / right / forest,
bodies 172/170/171) and the fresh `inr` value match `forest_value_eq`. -/
structure ResolvedChoiceComponentCasesSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-172: the left residual sector bridge. -/
  Left : ResolvedLeftResidualSectorBridgeSupply D S Region
  /-- Body-170: the right region sector bridge. -/
  Right : ResolvedRightRegionSectorBridgeSupply D S Region
  /-- Body-171: the forest region sector bridge. -/
  Forest : ResolvedForestRegionSectorBridgeSupply D S Region
  /-- The fresh `inr` value match: on a forward-image forest component, the recovered forest tag equals the
  original forest index (the choice-value de-contraction). -/
  forest_value_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
    γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements →
    q.2 γ (Finset.mem_attach _ _) = Sum.inr B →
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _) = Sum.inr B

namespace ResolvedChoiceComponentCasesSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-194 — body-192's componentwise choice agreement from the three tag cases.** -/
theorem choice_component_eq (C : ResolvedChoiceComponentCasesSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements) :
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = q.2 γ (Finset.mem_attach _ _) := by
  rcases hc : q.2 γ (Finset.mem_attach _ _) with (b | B)
  · cases b
    · have hr : rightPrimSelected q γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (Region.Union.rightRecovered (fwdMap S q)).elements :=
        (C.Right.rightRecovered_forward_membership q γ.1).mpr hr
      exact Region.right_tag (fwdMap S q) ⟨γ.1, hu⟩ hmem
    · have hl : ResolvedCoassocSplitChoice.leftSelectedConcrete q γ.1 := ⟨γ.2, hc⟩
      have hmem : γ.1 ∈ (Region.Union.leftResidual (fwdMap S q)).elements :=
        (C.Left.leftResidual_forward_membership q γ.1).mpr hl
      exact Region.left_tag (fwdMap S q) ⟨γ.1, hu⟩ hmem
  · have hf : forestChoiceSelected q γ.1 := ⟨γ.2, B, hc⟩
    have hmem : γ.1 ∈ (Region.Union.forestRecovered (fwdMap S q)).elements :=
      (C.Forest.forestRecovered_forward_membership q γ.1).mpr hf
    exact C.forest_value_eq q γ hu B hmem hc

/-- **R-6c-body-194 — body-193's backward-choice assembly supply from the cases** (given the index transport). -/
def toBackwardChoiceHEqAssemblySupply (C : ResolvedChoiceComponentCasesSupply D S Region)
    (outer_partition : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements) :
    ResolvedBackwardChoiceHEqAssemblySupply D S Region where
  outer_partition := fun {G} q => outer_partition q
  choice_component_eq := fun {G} q γ hu => C.choice_component_eq q γ hu

end ResolvedChoiceComponentCasesSupply

end GaugeGeometry.QFT.Combinatorial
