import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestChoiceOccurrenceRecovery

/-!
# R-6c-body-288 — forest exact-B reduced to the occurrence-compatibility leaf (PROVED)

Two-hundred-and-eighty-eighth genuine-body step — the value-root re-key of body-200/202's forest occurrence recovery.
It reduces body-285's leaf 3 (`forest_value_eq`, the forest exact-value match) to a SINGLE minimal
occurrence-compatibility leaf `forestTag_agrees`, proving everything else.

## The anti-cycle: the occurrence's `B` comes from `choiceAt`, NOT `forestTag`

At a forest component `γ.1 ∈ forestRecovered (fwdMapFilteredValue F V q)`, body-278's proved forest bridge
`forestRecovered_forward_value_membership |>.mp` gives `forestChoiceSelected q.1 γ.1 = ∃ hγ ∃ B, choiceAt q.1 ⟨γ.1,hγ⟩ =
inr B` — the `B` is `q.1`'s OWN choice, independent of `forestTag`.  So the occurrence `occurrenceValue q γ hmem` is
built from `q.1`'s choice witness, and `parent_recovered_value := rfl` (the parent is `γ` by construction, exactly the
total-root body-202 move).  Then `forest_choiceAt_eq_value : q.1.2 γ = inr (forestTag_fwd_value …)` follows from body-200's
generic `heq_transport_choice`.

## The single minimal leaf + the reduction

The recovered index `forestTag_fwd_value` (`= occurrence.B`) equals the original `B` by `Sum.inr.inj`
(`forest_choiceAt_eq_value` vs the hypothesis).  The ONLY residual is that the model's opaque `forestTag` (body-282)
agrees with it:

```text
forestTag_agrees : forestTag (fwd q) ⟨γ.1, hu⟩ hmem = forestTag_fwd_value q γ hmem
```

Given it, `forest_value_eq` (body-285's leaf shape) is proved by the free forest-branch unfold of `recoverChoiceValue`
(body-282 exclusivities) + `Sum.inr.inj` — pure logic.  No `S`, no `Forward`, no total-root occurrence machinery
(body-200's supply is S-keyed; its content is reused as the generic `heq_transport_choice` + the value forest bridge).

Per the HALT: leaf 3 is reduced to `forestTag_agrees`; the occurrence is built from the value forest bridge with
`parent_recovered := rfl`; the two forward leaves (bodies 289/290) are untouched.  No facade, no flat term, no
`forgetHopf`.
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

namespace ResolvedRecoveredPreimageValueMemSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-288 — the recovered forest occurrence** (value root; built from body-278's forest bridge, so its `B`
comes from `q.1`'s own `choiceAt`, breaking the cycle). -/
noncomputable def occurrenceValue (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements) :
    ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1 :=
  let hsel := (R.Tags.Closure.Assembly.toForestBridgeSupply.forestRecovered_forward_value_membership
    q γ.1).mp hmem
  ⟨⟨γ.1, hsel.choose⟩, hsel.choose_spec.choose, hsel.choose_spec.choose_spec⟩

/-- **R-6c-body-288 — the parent recovery** (`rfl`; the occurrence's parent is `γ` by construction, body-202). -/
theorem parent_recovered_value (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements) :
    (R.occurrenceValue q γ hmem).γ = γ :=
  rfl

/-- **R-6c-body-288 — the recovered forest tag** (the occurrence's `B`, transported to `γ`). -/
noncomputable def forestTag_fwd_value (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements) :
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  (R.parent_recovered_value q γ hmem) ▸ (R.occurrenceValue q γ hmem).B

/-- **R-6c-body-288 — the forest-component choice value** (body-200's `forest_choiceAt_eq`, value root). -/
theorem forest_choiceAt_eq_value (R : ResolvedRecoveredPreimageValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements) :
    q.1.2 γ (Finset.mem_attach _ _) = Sum.inr (R.forestTag_fwd_value q γ hmem) :=
  heq_transport_choice (R.occurrenceValue q γ hmem) γ (R.parent_recovered_value q γ hmem)

end ResolvedRecoveredPreimageValueMemSupply

/-- **R-6c-body-288 — the forest exact-B supply.**  Body-283's data + the single occurrence-compatibility leaf: the
opaque `forestTag` agrees with the occurrence-recovered index. -/
structure ResolvedForestValueEqValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- The single minimal leaf: the model's `forestTag` agrees with the occurrence-recovered index. -/
  forestTag_agrees : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements),
    Data.Tags.forestTag (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem = Data.forestTag_fwd_value q γ hmem

namespace ResolvedForestValueEqValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-288 — body-285's leaf 3 from the compatibility leaf** (pure logic: forest-branch unfold + `Sum.inr.inj`). -/
theorem forest_value_eq (R : ResolvedForestValueEqValueSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (R.Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue F V q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
    (hmem : γ.1 ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredValue F V q)).elements)
    (hqB : q.1.2 γ (Finset.mem_attach _ _) = Sum.inr B) :
    R.Data.Tags.recoverChoiceValue (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = Sum.inr B := by
  rw [ResolvedRegionTagValueSupply.recoverChoiceValue,
    if_neg (R.Data.Tags.forest_notMem_left (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem),
    if_neg (R.Data.Tags.forest_notMem_right (fwdMapFilteredValue F V q) ⟨γ.1, hu⟩ hmem),
    dif_pos hmem, R.forestTag_agrees q γ hu hmem]
  exact congrArg Sum.inr
    (Sum.inr.inj ((R.Data.forest_choiceAt_eq_value q γ hmem).symm.trans hqB))

end ResolvedForestValueEqValueSupply

end GaugeGeometry.QFT.Combinatorial
