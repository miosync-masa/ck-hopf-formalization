import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionTags

/-!
# R-6c-body-478 — the alpha forward-outer + forward-quotient geometry (282–290 migration, PROVED)

Four-hundred-and-seventy-eighth genuine-body step — the value-root re-key of bodies 289/290 onto the alpha recovered side,
finishing the 282–290 migration.  The key discipline: **one filtered witness `qz := Data.recoveredFilteredPreimageAlpha
Value z` is shared by every forward reconstruction**; a raw split choice is only ever `qz.1` (never a re-wrapped filtered
subtype with a different membership proof).  This eliminates the raw quotient application entirely — the forward quotient
value is `V.quotientForestRaw qz` on the FILTERED witness.

* `ResolvedRegionAlphaValueClosureSupply.mem_unionOuterAlphaValue_iff` — the outer-union membership trichotomy helper
  (body-284 shape);
* `ResolvedForwardOuterAlphaValueGeometrySupply` — body-477 data + the three honest local geometry leaves
  (`promote_collapse` / `forestComponentMem` / `represented_cases`), mirroring body-289; the theorems
  `choiceAt_recovered_eq_alpha` / `leftOf_recovered_eq_alpha` / `promotedOf_recovered_eq_alpha` / `coverage_alpha_value`
  reduce to `forward_outer_alpha_value : selectedOuterRawOf qz.1 = z.1.1`;
* `ResolvedForwardQuotientAlphaValueGeometrySupply` — the outer geometry + the two survivor/remnant element membership
  bridges (indexed by `qz.1`), mirroring body-290; `quotient_elements_heq_alpha_value` + `forward_quotient_alpha_value :
  HEq (V.quotientForestRaw qz) z.2`;
* the legacy adapters `ResolvedRegionTagValueSupply.toAlpha` / `ResolvedRecoveredPreimageValueMemSupply.toAlpha` /
  `ResolvedForwardOuterValueGeometrySupply.toAlpha` / `ResolvedForwardQuotientValueGeometrySupply.toAlpha` (field-by-field
  over `V.toFiltered`, DEFEQ via the body-471/476 `rfl` anchors).

Per the HALT/guards: the full recovered round-trip supply is NOT assembled (body-479); no backward choice / outer is
entered; the three geometry leaves are NOT claimed canonically proved (they stay honest fields); no raw recovered choice is
handed to `V.quotientForestRaw` (only the filtered `qz`); the filtered witness is NOT locally re-wrapped; old structures are
NOT edited in place; NO `quot_eq`, NO `W'` membership, NO new geometry; strict `StarProm` / `InnerStarRaw` NOT restored;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-478 — the alpha outer-union's membership disjunction** (body-284 shape). -/
theorem ResolvedRegionAlphaValueClosureSupply.mem_unionOuterAlphaValue_iff
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (C : ResolvedRegionAlphaValueClosureSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (C.unionOuterAlphaValue z).1.elements ↔
      (γ ∈ (C.Assembly.Left.leftResidual z).elements
        ∨ γ ∈ (C.Assembly.Region.rightRecovered z).elements
        ∨ γ ∈ (C.Assembly.Region.forestRecovered z).elements) := by
  simp only [unionOuterAlphaValue, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements]
  constructor
  · intro h
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp h with h1 | h2
    · rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp h1 with hl | hr
      · exact Or.inl hl
      · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr h2)
  · intro h
    rcases h with hl | hr | hf
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr
        (Or.inl ((@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl hl)))
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr
        (Or.inl ((@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr hr)))
    · exact (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr hf)

/-- **R-6c-body-478 — the alpha forward outer geometry supply.**  Body-477's data + the three honest local geometry
leaves (mirroring body-289). -/
structure ResolvedForwardOuterAlphaValueGeometrySupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The alpha membership supply (body-477). -/
  Data : ResolvedRecoveredPreimageAlphaValueMemSupply F V
  /-- LEAF 1 — the de-contracted forest of a recovered parent is the parent singleton. -/
  promote_collapse : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterAlphaValue z).1.elements})
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

namespace ResolvedForwardOuterAlphaValueGeometrySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-478 — the choice-at-the-reconstruction bridge** (`rfl`). -/
theorem choiceAt_recovered_eq_alpha (R : ResolvedForwardOuterAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (R.Data.Tags.Closure.unionOuterAlphaValue z).1.elements}) :
    ResolvedCoassocSplitChoice.choiceAt (R.Data.Tags.recoveredPreimageAlphaValue z) γ
      = R.Data.Tags.recoverChoiceAlphaValue z γ (Finset.mem_attach _ _) :=
  rfl

/-- **R-6c-body-478 — `leftOf(recovered) = leftResidual`** (pure tag, body-174 shape). -/
theorem leftOf_recovered_eq_alpha (R : ResolvedForwardOuterAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((resolvedConcreteForestPromoteSupply D G).leftOf (R.Data.Tags.recoveredPreimageAlphaValue z)).elements
      = (R.Data.Tags.Closure.Assembly.Left.leftResidual z).elements := by
  have hLe : ((resolvedConcreteForestPromoteSupply D G).leftOf
        (R.Data.Tags.recoveredPreimageAlphaValue z)).elements
      = (R.Data.Tags.Closure.unionOuterAlphaValue z).1.elements.filter
          (ResolvedCoassocSplitChoice.leftSelectedConcrete (R.Data.Tags.recoveredPreimageAlphaValue z)) := rfl
  rw [hLe]
  ext γ
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hmemU, hγmem, htag⟩
    rcases (R.Data.Tags.Closure.mem_unionOuterAlphaValue_iff z γ).mp hmemU with hl | hr | hf
    · exact hl
    · exact absurd (Sum.inl.inj ((R.Data.Tags.right_tag_alpha z ⟨γ, hmemU⟩ hr).symm.trans
        ((R.choiceAt_recovered_eq_alpha z ⟨γ, hmemU⟩).symm.trans htag))) (by decide)
    · obtain ⟨B, hB⟩ := R.Data.Tags.forest_tag_alpha z ⟨γ, hmemU⟩ hf
      exact absurd (hB.symm.trans ((R.choiceAt_recovered_eq_alpha z ⟨γ, hmemU⟩).symm.trans htag)) (by simp)
  · intro hl
    have hmemU : γ ∈ (R.Data.Tags.Closure.unionOuterAlphaValue z).1.elements :=
      (R.Data.Tags.Closure.mem_unionOuterAlphaValue_iff z γ).mpr (Or.inl hl)
    exact ⟨hmemU, hmemU,
      (R.choiceAt_recovered_eq_alpha z ⟨γ, hmemU⟩).trans (R.Data.Tags.left_tag_alpha z ⟨γ, hmemU⟩ hl)⟩

/-- **R-6c-body-478 — `promotedOf(recovered) = forestRecovered`** (biUnion collapse, body-189 shape). -/
theorem promotedOf_recovered_eq_alpha (R : ResolvedForwardOuterAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((resolvedConcreteForestPromoteSupply D G).promotedOf (R.Data.Tags.recoveredPreimageAlphaValue z)).elements
      = (R.Data.Tags.Closure.Assembly.Region.forestRecovered z).elements := by
  have hpe : ((resolvedConcreteForestPromoteSupply D G).promotedOf
        (R.Data.Tags.recoveredPreimageAlphaValue z)).elements
      = (R.Data.Tags.Closure.unionOuterAlphaValue z).1.elements.attach.biUnion
        (ResolvedCoassocSplitChoice.promotedComponentElements
          (R.Data.Tags.recoveredPreimageAlphaValue z)) := rfl
  rw [hpe]
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨γ, -, hx⟩
    rcases (R.Data.Tags.Closure.mem_unionOuterAlphaValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (R.Data.Tags.recoveredPreimageAlphaValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(R.choiceAt_recovered_eq_alpha z γ).trans (R.Data.Tags.left_tag_alpha z γ hl)]] at hx
      simp at hx
    · exfalso
      rw [show ResolvedCoassocSplitChoice.promotedComponentElements
            (R.Data.Tags.recoveredPreimageAlphaValue z) γ = ∅ from by
          unfold ResolvedCoassocSplitChoice.promotedComponentElements
          rw [(R.choiceAt_recovered_eq_alpha z γ).trans (R.Data.Tags.right_tag_alpha z γ hr)]] at hx
      simp at hx
    · rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
          ((R.choiceAt_recovered_eq_alpha z γ).trans (by
            rw [ResolvedRegionTagAlphaValueSupply.recoverChoiceAlphaValue,
              if_neg (R.Data.Tags.forest_notMem_left z γ hf),
              if_neg (R.Data.Tags.forest_notMem_right z γ hf), dif_pos hf])),
        R.promote_collapse z γ hf, Finset.mem_singleton] at hx
      subst hx
      exact hf
  · intro hx
    have hxu : x ∈ (R.Data.Tags.Closure.unionOuterAlphaValue z).1.elements :=
      (R.Data.Tags.Closure.mem_unionOuterAlphaValue_iff z x).mpr (Or.inr (Or.inr hx))
    refine ⟨⟨x, hxu⟩, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr _
        ((R.choiceAt_recovered_eq_alpha z ⟨x, hxu⟩).trans (by
          rw [ResolvedRegionTagAlphaValueSupply.recoverChoiceAlphaValue,
            if_neg (R.Data.Tags.forest_notMem_left z ⟨x, hxu⟩ hx),
            if_neg (R.Data.Tags.forest_notMem_right z ⟨x, hxu⟩ hx), dif_pos hx])),
      R.promote_collapse z ⟨x, hxu⟩ hx]
    exact Finset.mem_singleton_self x

/-- **R-6c-body-478 — the target-outer coverage** (`leftResidual ∪ forestRecovered = A`, body-177 shape). -/
theorem coverage_alpha_value (R : ResolvedForwardOuterAlphaValueGeometrySupply F V)
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

/-- **R-6c-body-478 — the forward outer reconstruction from the three geometry leaves.**  The conclusion is stated over
the shared filtered witness `qz.1` (`= Tags.recoveredPreimageAlphaValue z`, `rfl`). -/
theorem forward_outer_alpha_value (R : ResolvedForwardOuterAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
        (R.Data.recoveredFilteredPreimageAlphaValue z).1 = z.1.1 := by
  rw [ResolvedRecoveredPreimageAlphaValueMemSupply.recoveredFilteredPreimageAlphaValue_fst]
  apply ResolvedAdmissibleSubgraph.ext_elements
  ext γ
  rw [ResolvedForestPromoteSupply.selectedOuterRawOf, ResolvedAdmissibleSubgraph.union_elements]
  constructor
  · intro hγ
    rcases (@Finset.mem_union _ (Classical.decEq _) _ _ _).mp hγ with hl | hp
    · rw [R.leftOf_recovered_eq_alpha z] at hl
      exact (R.coverage_alpha_value z γ).mp (Or.inl hl)
    · rw [R.promotedOf_recovered_eq_alpha z] at hp
      exact (R.coverage_alpha_value z γ).mp (Or.inr hp)
  · intro hmem
    rcases (R.coverage_alpha_value z γ).mpr hmem with hl | hf
    · refine (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inl ?_)
      rw [R.leftOf_recovered_eq_alpha z]; exact hl
    · refine (@Finset.mem_union _ (Classical.decEq _) _ _ _).mpr (Or.inr ?_)
      rw [R.promotedOf_recovered_eq_alpha z]; exact hf

end ResolvedForwardOuterAlphaValueGeometrySupply

/-- **R-6c-body-478 — the alpha forward quotient geometry supply.**  The alpha forward-outer geometry (body-478, for the
graph transport) + the two generic-`z` survivor / remnant element membership bridges, indexed by the shared witness
`qz.1`; the quotient value alone is over the FILTERED `qz`. -/
structure ResolvedForwardQuotientAlphaValueGeometrySupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The alpha forward-outer geometry (body-478): supplies `forward_outer_alpha_value` + the data. -/
  Geom : ResolvedForwardOuterAlphaValueGeometrySupply F V
  /-- The survivor membership bridge (tag-reducible: `inl false` ⟷ star-avoiding), indexed by `qz.1`. -/
  survivor_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Geom.Data.recoveredFilteredPreimageAlphaValue z).1))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Survivor.survivor.rightSurvivorForest
        (Geom.Data.recoveredFilteredPreimageAlphaValue z).1).elements
      ↔ x₂ ∈ rightDomain z)
  /-- The remnant membership bridge (genuine de-contraction geometry), indexed by `qz.1`. -/
  remnant_mem_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (Geom.Data.recoveredFilteredPreimageAlphaValue z).1))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ (V.Remnant.remnant.remnantForest
        (Geom.Data.recoveredFilteredPreimageAlphaValue z).1).elements
      ↔ x₂ ∈ forestDomain z)

namespace ResolvedForwardQuotientAlphaValueGeometrySupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-478 — the quotient element sets are heterogeneously equal** (body-204 shape, alpha value root).  The left
split is `V.union_eq qz` on the FILTERED witness; the ambient graph transport is `forward_outer_alpha_value`. -/
theorem quotient_elements_heq_alpha_value (R : ResolvedForwardQuotientAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (R.Geom.Data.recoveredFilteredPreimageAlphaValue z)).1.elements
      z.2.1.elements := by
  refine heq_of_membership_split (R.Geom.forward_outer_alpha_value z)
    (Q := (V.quotientForestRaw (R.Geom.Data.recoveredFilteredPreimageAlphaValue z)).1.elements)
    (Z := z.2.1.elements)
    (surv := (V.Survivor.survivor.rightSurvivorForest
      (R.Geom.Data.recoveredFilteredPreimageAlphaValue z).1).elements)
    (rem := (V.Remnant.remnant.remnantForest
      (R.Geom.Data.recoveredFilteredPreimageAlphaValue z).1).elements)
    (rightDom := rightDomain z) (forestDom := forestDomain z)
    ?_ ?_
    (heq_finset_of_mem_iff (R.Geom.forward_outer_alpha_value z) (R.survivor_mem_value z))
    (heq_finset_of_mem_iff (R.Geom.forward_outer_alpha_value z) (R.remnant_mem_value z))
  · intro x
    rw [V.union_eq (R.Geom.Data.recoveredFilteredPreimageAlphaValue z),
      ResolvedAdmissibleSubgraph.union_elements]
    convert Finset.mem_union using 2
  · intro x
    simp only [rightDomain, forestDomain, Finset.mem_filter]
    tauto

/-- **R-6c-body-478 ∎ — the forward quotient reconstruction from the two element bridges** (`heq_forestIdx`, body-203).
The application is on the FILTERED witness `qz` — the raw quotient application is ELIMINATED. -/
theorem forward_quotient_alpha_value (R : ResolvedForwardQuotientAlphaValueGeometrySupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (R.Geom.Data.recoveredFilteredPreimageAlphaValue z)) z.2 :=
  heq_forestIdx (V.quotientForestRaw (R.Geom.Data.recoveredFilteredPreimageAlphaValue z)) z.2
    (R.Geom.forward_outer_alpha_value z) (R.quotient_elements_heq_alpha_value z)

end ResolvedForwardQuotientAlphaValueGeometrySupply

/-! ## Legacy adapters (field-by-field over `V.toFiltered`, DEFEQ via the body-471/476 `rfl` anchors) -/

/-- **R-6c-body-478 — the legacy region-tag adapter into the alpha tags over `V.toFiltered`.** -/
def ResolvedRegionTagValueSupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (T : ResolvedRegionTagValueSupply F V) : ResolvedRegionTagAlphaValueSupply F V.toFiltered where
  Closure := T.Closure.toAlpha
  forestTag := T.forestTag
  right_notMem_left := T.right_notMem_left
  forest_notMem_left := T.forest_notMem_left
  forest_notMem_right := T.forest_notMem_right

/-- **R-6c-body-478 — the legacy recovered-membership adapter into the alpha owner over `V.toFiltered`.** -/
def ResolvedRecoveredPreimageValueMemSupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueMemSupply F V) :
    ResolvedRecoveredPreimageAlphaValueMemSupply F V.toFiltered where
  Tags := R.Tags.toAlpha
  forest_nonempty := R.forest_nonempty
  mixed_ne_pR := R.mixed_ne_pR
  mixed_ne_pL := R.mixed_ne_pL

/-- **R-6c-body-478 — the legacy forward-outer geometry adapter into the alpha geometry over `V.toFiltered`.** -/
def ResolvedForwardOuterValueGeometrySupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedForwardOuterValueGeometrySupply F V) :
    ResolvedForwardOuterAlphaValueGeometrySupply F V.toFiltered where
  Data := R.Data.toAlpha
  promote_collapse := R.promote_collapse
  forestComponentMem := R.forestComponentMem
  represented_cases := R.represented_cases

/-- **R-6c-body-478 ∎ — the legacy forward-quotient geometry adapter into the alpha geometry over `V.toFiltered`.** -/
def ResolvedForwardQuotientValueGeometrySupply.toAlpha
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedForwardQuotientValueGeometrySupply F V) :
    ResolvedForwardQuotientAlphaValueGeometrySupply F V.toFiltered where
  Geom := R.Geom.toAlpha
  survivor_mem_value := R.survivor_mem_value
  remnant_mem_value := R.remnant_mem_value

end GaugeGeometry.QFT.Combinatorial
