import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBackwardOuterValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem

/-!
# R-6c-body-289 — forward outer round-trip reduced to three geometry leaves (PROVED)

Two-hundred-and-eighty-ninth genuine-body step — the value-root re-key of the total-root forward-outer geometry
(bodies 174/189/177/190).  It reduces body-285's leaf 1 (`forward_outer_value`,
`selectedOuterRawOf (recoveredPreimageValue z) = z.1.1`) to THREE honest local geometry leaves, proving everything else
(the tag layer, the biUnion `inl→∅` collapse, and the coverage logic).

## The decomposition (all value-root)

`selectedOuterRawOf s = leftOf s ∪ promotedOf s` (body-heart-4).  For `s = recoveredPreimageValue z`:

* `leftOf(recovered) = leftResidual z` — PURE TAG (body-174 shape): the `inl true` filter of `unionOuterValue z` is
  exactly `leftResidual z`, by body-282's `left_tag` / `right_tag` / `forest_tag` + `mem_unionOuterValue_iff` (body-284).
  No leaf.
* `promotedOf(recovered) = forestRecovered z` — the biUnion collapse (body-189 shape): the `inl` regions contribute
  `∅` (tags), and each forest parent contributes its own singleton via `promotedComponentElements_inr` (the `dif_pos`
  branch of `recoverChoiceValue`) + `promote_collapse` (LEAF 1).
* `leftResidual z ∪ forestRecovered z = z.1.1` — the coverage (body-177 shape): `leftResidual_mem` is
  `filterElements` membership; the two directions need `forestComponentMem` (LEAF 2) and `represented_cases` (LEAF 3).

## The three leaves

```text
promote_collapse    (promote γ (forestTag z γ h).1).elements = {γ.1}         -- de-contraction geometry
forestComponentMem  γ ∈ forestRecovered z → γ ∈ z.1.1.elements               -- forest parent is an A-component
represented_cases   γ ∈ z.1.1 → representedInQuotient z γ → γ ∈ forestRecovered z
```

Per the HALT: `forward_outer_value` is reduced to these three leaves; the tag layer, the biUnion collapse, and the
coverage logic are proved; `forestTag` is body-282 data, not a leaf; `forestTag_agrees` (body-288) and the forward
quotient (body-290) are NOT mixed in; the proof is over generic `z`, never `fwdMap`.  No facade, no flat term, no
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

/-- **R-6c-body-289 — the forward outer geometry supply.**  Body-283's data + the three honest local geometry leaves. -/
structure ResolvedForwardOuterValueGeometrySupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The membership supply (body-283). -/
  Data : ResolvedRecoveredPreimageValueMemSupply F V
  /-- LEAF 1 — the de-contracted forest of a recovered parent is the parent singleton. -/
  promote_collapse : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterValue z).1.elements})
    (h : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements),
    (ResolvedAdmissibleSubgraph.promote γ.1 (Data.Tags.forestTag z γ h).1).elements = {γ.1}
  /-- LEAF 2 — a forest-recovered parent is a component of the target outer `A`. -/
  forestComponentMem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements → γ ∈ z.1.1.elements
  /-- LEAF 3 — a represented `A`-component is a forest-recovered parent. -/
  represented_cases : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → Data.Tags.Closure.Assembly.Left.representedInQuotient z γ →
      γ ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements

namespace ResolvedForwardOuterValueGeometrySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-289 — the choice-at-the-reconstruction bridge** (`rfl`). -/
theorem choiceAt_recovered_eq (R : ResolvedForwardOuterValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (R.Data.Tags.Closure.unionOuterValue z).1.elements}) :
    ResolvedCoassocSplitChoice.choiceAt (R.Data.Tags.recoveredPreimageValue z) γ
      = R.Data.Tags.recoverChoiceValue z γ (Finset.mem_attach _ _) :=
  rfl

/-- **R-6c-body-289 — `leftOf(recovered) = leftResidual`** (pure tag, body-174 shape). -/
theorem leftOf_recovered_eq (R : ResolvedForwardOuterValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((resolvedConcreteForestPromoteSupply D G).leftOf (R.Data.Tags.recoveredPreimageValue z)).elements
      = (R.Data.Tags.Closure.Assembly.Left.leftResidual z).elements := by
  have hLe : ((resolvedConcreteForestPromoteSupply D G).leftOf
        (R.Data.Tags.recoveredPreimageValue z)).elements
      = (R.Data.Tags.Closure.unionOuterValue z).1.elements.filter
          (ResolvedCoassocSplitChoice.leftSelectedConcrete (R.Data.Tags.recoveredPreimageValue z)) := rfl
  rw [hLe]
  ext γ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmemU, hγmem, htag⟩
    rcases (R.Data.Tags.Closure.mem_unionOuterValue_iff z γ).mp hmemU with hl | hr | hf
    · exact hl
    · exact absurd (Sum.inl.inj ((R.Data.Tags.right_tag z ⟨γ, hmemU⟩ hr).symm.trans
        ((R.choiceAt_recovered_eq z ⟨γ, hmemU⟩).symm.trans htag))) (by decide)
    · obtain ⟨B, hB⟩ := R.Data.Tags.forest_tag z ⟨γ, hmemU⟩ hf
      exact absurd (hB.symm.trans ((R.choiceAt_recovered_eq z ⟨γ, hmemU⟩).symm.trans htag)) (by simp)
  · intro hl
    have hmemU : γ ∈ (R.Data.Tags.Closure.unionOuterValue z).1.elements :=
      (R.Data.Tags.Closure.mem_unionOuterValue_iff z γ).mpr (Or.inl hl)
    exact ⟨hmemU, hmemU,
      (R.choiceAt_recovered_eq z ⟨γ, hmemU⟩).trans (R.Data.Tags.left_tag z ⟨γ, hmemU⟩ hl)⟩

/-- **R-6c-body-289 — `promotedOf(recovered) = forestRecovered`** (biUnion collapse, body-189 shape). -/
theorem promotedOf_recovered_eq (R : ResolvedForwardOuterValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((resolvedConcreteForestPromoteSupply D G).promotedOf (R.Data.Tags.recoveredPreimageValue z)).elements
      = (R.Data.Tags.Closure.Assembly.Region.forestRecovered z).elements := by
  have hpe : ((resolvedConcreteForestPromoteSupply D G).promotedOf
        (R.Data.Tags.recoveredPreimageValue z)).elements
      = (R.Data.Tags.Closure.unionOuterValue z).1.elements.attach.biUnion
        (ResolvedCoassocSplitChoice.promotedComponentElements
          (R.Data.Tags.recoveredPreimageValue z)) := rfl
  rw [hpe]
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨γ, -, hx⟩
    rcases (R.Data.Tags.Closure.mem_unionOuterValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (R.Data.Tags.recoveredPreimageValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(R.choiceAt_recovered_eq z γ).trans (R.Data.Tags.left_tag z γ hl)]] at hx
      simp at hx
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (R.Data.Tags.recoveredPreimageValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(R.choiceAt_recovered_eq z γ).trans (R.Data.Tags.right_tag z γ hr)]] at hx
      simp at hx
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
          ((R.choiceAt_recovered_eq z γ).trans (by
            rw [ResolvedRegionTagValueSupply.recoverChoiceValue,
              if_neg (R.Data.Tags.forest_notMem_left z γ hf),
              if_neg (R.Data.Tags.forest_notMem_right z γ hf), dif_pos hf])),
        R.promote_collapse z γ hf, Finset.mem_singleton] at hx
      subst hx
      exact hf
  · intro hx
    have hxu : x ∈ (R.Data.Tags.Closure.unionOuterValue z).1.elements :=
      (R.Data.Tags.Closure.mem_unionOuterValue_iff z x).mpr (Or.inr (Or.inr hx))
    refine ⟨⟨x, hxu⟩, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
        ((R.choiceAt_recovered_eq z ⟨x, hxu⟩).trans (by
          rw [ResolvedRegionTagValueSupply.recoverChoiceValue,
            if_neg (R.Data.Tags.forest_notMem_left z ⟨x, hxu⟩ hx),
            if_neg (R.Data.Tags.forest_notMem_right z ⟨x, hxu⟩ hx), dif_pos hx])),
      R.promote_collapse z ⟨x, hxu⟩ hx]
    exact Finset.mem_singleton_self x

/-- **R-6c-body-289 — the target-outer coverage** (`leftResidual ∪ forestRecovered = A`, body-177 shape). -/
theorem coverage_value (R : ResolvedForwardOuterValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ (R.Data.Tags.Closure.Assembly.Left.leftResidual z).elements
        ∨ γ ∈ (R.Data.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      ↔ γ ∈ z.1.1.elements := by
  constructor
  · rintro (hl | hf)
    · exact (Finset.mem_filter.mp hl).1
    · exact R.forestComponentMem z γ hf
  · intro hmem
    by_cases hrep : R.Data.Tags.Closure.Assembly.Left.representedInQuotient z γ
    · exact Or.inr (R.represented_cases z γ hmem hrep)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hmem, hrep⟩)

/-- **R-6c-body-289 — body-285's leaf 1 from the three geometry leaves.** -/
theorem forward_outer_value (R : ResolvedForwardOuterValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (R.Data.Tags.recoveredPreimageValue z)
      = z.1.1 := by
  apply ResolvedAdmissibleSubgraph.ext_elements
  ext γ
  rw [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements]
  constructor
  · intro hγ
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp hγ with hl | hp
    · rw [R.leftOf_recovered_eq z] at hl
      exact (R.coverage_value z γ).mp (Or.inl hl)
    · rw [R.promotedOf_recovered_eq z] at hp
      exact (R.coverage_value z γ).mp (Or.inr hp)
  · intro hmem
    rcases (R.coverage_value z γ).mpr hmem with hl | hf
    · refine (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl ?_)
      rw [R.leftOf_recovered_eq z]; exact hl
    · refine (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr ?_)
      rw [R.promotedOf_recovered_eq z]; exact hf

end ResolvedForwardOuterValueGeometrySupply

end GaugeGeometry.QFT.Combinatorial
