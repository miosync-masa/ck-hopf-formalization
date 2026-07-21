import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRegionClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredRecoveredChoice

/-!
# R-6c-body-477 — alpha region tags + recovered membership + filtered owner issuance (stage 3 of the tag-chain mirror)

Four-hundred-and-seventy-seventh genuine-body step — the THIRD (near-verbatim) mirror of bodies 282/283: the alpha region
tag supply, its priority reconstruction, the alpha recovered-preimage membership owner, and the body-473 filtered-owner
issuance.  The core is that the raw recovered choice AND its membership read the SAME alpha `Tags` owner.

* `ResolvedRegionTagAlphaValueSupply` — `Closure` (body-476) + `forestTag` + the three region exclusivities;
* `recoverChoiceAlphaValue` (+ `left_tag_alpha` / `right_tag_alpha` / `forest_tag_alpha`) — the priority reconstruction
  (left → `inl true`, right → `inl false`, forest → `inr forestTag`, default → `inl true`);
* `recoveredPreimageAlphaValue T z := ⟨Closure.unionOuterAlphaValue z, recoverChoiceAlphaValue⟩` — outer and choice from
  the SAME owner;
* `ResolvedRecoveredPreimageAlphaValueMemSupply` (`Tags`, `forest_nonempty`, `mixed_ne_pR`, `mixed_ne_pL`) with
  `forestRecovered_mem_unionOuterAlphaValue`, `forest_isForestCarrying_alpha`, `forestPreimage_mem_alpha`,
  `mixedPreimage_mem_alpha`, `recoveredPreimageValue_mem_alpha`;
* `toFilteredRecoveredChoiceSupply` → `recoveredFilteredPreimageAlphaValue` (the body-473 owner + canonical witness), and
  the quotient NORMAL FORM `V.quotientForestRaw (R.recoveredFilteredPreimageAlphaValue z)`.

Per the HALT/guards: forward outer/quotient geometry is NOT entered; NO round-trip; the six bridges / exclusivities are
NOT re-proved; old structures are NOT edited in place; NO `quot_eq`, NO `W'` membership, NO new geometry; strict
`StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-477 — the alpha region tag supply.** -/
structure ResolvedRegionTagAlphaValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The coherent alpha region closure (body-476). -/
  Closure : ResolvedRegionAlphaValueClosureSupply F V
  /-- The quotient sub-forest `Bᵧ` of each forest-recovered component. -/
  forestTag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterAlphaValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- A right-recovered component is not left-residual. -/
  right_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterAlphaValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.rightRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Left.leftResidual z).elements
  /-- A forest-recovered component is not left-residual. -/
  forest_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterAlphaValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Left.leftResidual z).elements
  /-- A forest-recovered component is not right-recovered. -/
  forest_notMem_right : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Closure.unionOuterAlphaValue z).1.elements}),
    γ.1 ∈ (Closure.Assembly.Region.forestRecovered z).elements →
      γ.1 ∉ (Closure.Assembly.Region.rightRecovered z).elements

namespace ResolvedRegionTagAlphaValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-477 — the alpha region-priority tag function.** -/
noncomputable def recoverChoiceAlphaValue (T : ResolvedRegionTagAlphaValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
    (_hγ : γ ∈ (T.Closure.unionOuterAlphaValue z).1.elements.attach) :
    Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  if γ.1 ∈ (T.Closure.Assembly.Left.leftResidual z).elements then Sum.inl true
  else if γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements then Sum.inl false
  else if h : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements then
    Sum.inr (T.forestTag z γ h)
  else Sum.inl true

/-- **R-6c-body-477 — the left tag** (`inl true`). -/
theorem left_tag_alpha (T : ResolvedRegionTagAlphaValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Left.leftResidual z).elements) :
    T.recoverChoiceAlphaValue z γ (Finset.mem_attach _ _) = Sum.inl true := by
  rw [recoverChoiceAlphaValue, if_pos hm]

/-- **R-6c-body-477 — the right tag** (`inl false`). -/
theorem right_tag_alpha (T : ResolvedRegionTagAlphaValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Region.rightRecovered z).elements) :
    T.recoverChoiceAlphaValue z γ (Finset.mem_attach _ _) = Sum.inl false := by
  rw [recoverChoiceAlphaValue, if_neg (T.right_notMem_left z γ hm), if_pos hm]

/-- **R-6c-body-477 — the forest tag** (`inr Bᵧ`). -/
theorem forest_tag_alpha (T : ResolvedRegionTagAlphaValueSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterAlphaValue z).1.elements})
    (hm : γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements) :
    ∃ B, T.recoverChoiceAlphaValue z γ (Finset.mem_attach _ _) = Sum.inr B := by
  rw [recoverChoiceAlphaValue, if_neg (T.forest_notMem_left z γ hm),
    if_neg (T.forest_notMem_right z γ hm), dif_pos hm]
  exact ⟨_, rfl⟩

/-- **R-6c-body-477 — the common raw preimage** (`⟨unionOuterAlphaValue, recoverChoiceAlphaValue⟩`). -/
noncomputable def recoveredPreimageAlphaValue (T : ResolvedRegionTagAlphaValueSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ForestBlockDomType D G :=
  ⟨T.Closure.unionOuterAlphaValue z, fun γ hγ => T.recoverChoiceAlphaValue z γ hγ⟩

end ResolvedRegionTagAlphaValueSupply

/-- **R-6c-body-477 — the alpha recovered-preimage membership owner.** -/
structure ResolvedRecoveredPreimageAlphaValueMemSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- The alpha region tags (body-477). -/
  Tags : ResolvedRegionTagAlphaValueSupply F V
  /-- On a forest image, the forest region is nonempty. -/
  forest_nonempty : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → (Tags.Closure.Assembly.Region.forestRecovered z).elements.Nonempty
  /-- On a mixed image, the reconstructed choice is not the all-right `p_R`. -/
  mixed_ne_pR : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 →
      (Tags.recoveredPreimageAlphaValue z).2 ≠ (fun _ _ => Sum.inl false)
  /-- On a mixed image, the reconstructed choice is not the all-left `p_L`. -/
  mixed_ne_pL : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 →
      (Tags.recoveredPreimageAlphaValue z).2 ≠ (fun _ _ => Sum.inl true)

namespace ResolvedRecoveredPreimageAlphaValueMemSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-477 — a forest component injects into the alpha outer union.** -/
theorem forestRecovered_mem_unionOuterAlphaValue (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ (R.Tags.Closure.Assembly.Region.forestRecovered z).elements) :
    δ ∈ (R.Tags.Closure.unionOuterAlphaValue z).1.elements := by
  simp only [ResolvedRegionAlphaValueClosureSupply.unionOuterAlphaValue, recoveredRawUnion,
    ResolvedAdmissibleSubgraph.union_elements]
  exact @Finset.mem_union_right _ (Classical.decEq _) _ _ _ hδ

/-- **R-6c-body-477 — the forest branch's `isForestCarryingChoice`.** -/
theorem forest_isForestCarrying_alpha (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    isForestCarryingChoice (R.Tags.recoveredPreimageAlphaValue z).1
      (R.Tags.recoveredPreimageAlphaValue z).2 := by
  obtain ⟨δ, hδ⟩ := R.forest_nonempty z h
  have hδu : δ ∈ (R.Tags.Closure.unionOuterAlphaValue z).1.elements :=
    R.forestRecovered_mem_unionOuterAlphaValue z hδ
  obtain ⟨B, hB⟩ := R.Tags.forest_tag_alpha z ⟨δ, hδu⟩ hδ
  exact ⟨⟨δ, hδu⟩, Finset.mem_attach _ _, B, hB⟩

/-- **R-6c-body-477 — forest-branch filtered-domain membership.** -/
theorem forestPreimage_mem_alpha (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    R.Tags.recoveredPreimageAlphaValue z ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_isForestCarrying _ (R.forest_isForestCarrying_alpha z h)

/-- **R-6c-body-477 — mixed-branch filtered-domain membership.** -/
theorem mixedPreimage_mem_alpha (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    R.Tags.recoveredPreimageAlphaValue z ∈ forestBlockDomFinset G :=
  mem_forestBlockDomFinset_of_ne _ (R.mixed_ne_pR z h) (R.mixed_ne_pL z h)

/-- **R-6c-body-477 — the total alpha recovered-preimage domain membership.** -/
theorem recoveredPreimageValue_mem_alpha (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    R.Tags.recoveredPreimageAlphaValue z ∈ forestBlockDomFinset G := by
  by_cases h : resolvedIsForestImage z.1 z.2
  · exact R.forestPreimage_mem_alpha z h
  · exact R.mixedPreimage_mem_alpha z h

/-- **R-6c-body-477 — issue the body-473 filtered recovered-choice owner.** -/
noncomputable def toFilteredRecoveredChoiceSupply
    (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V) :
    ResolvedFilteredRecoveredChoiceSupply D where
  raw := fun {_G} z => R.Tags.recoveredPreimageAlphaValue z
  mem := fun {_G} z => R.recoveredPreimageValue_mem_alpha z

/-- **R-6c-body-477 ∎ — the canonical filtered recovered witness of the alpha side.** -/
noncomputable def recoveredFilteredPreimageAlphaValue
    (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : FilteredForestBlockDom D G :=
  R.toFilteredRecoveredChoiceSupply.filtered z

/-- **R-6c-body-477 — the witness's split choice is the alpha raw choice** (`rfl`). -/
@[simp] theorem recoveredFilteredPreimageAlphaValue_fst
    (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (R.recoveredFilteredPreimageAlphaValue z).1 = R.Tags.recoveredPreimageAlphaValue z :=
  rfl

/-- **R-6c-body-477 — the quotient NORMAL FORM** for the alpha recovered side. -/
theorem alpha_quotient_normal_form
    (R : ResolvedRecoveredPreimageAlphaValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (V.quotientForestRaw (R.recoveredFilteredPreimageAlphaValue z)).1
      ∈ D.carrier (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.recoveredFilteredPreimageAlphaValue z).1) :=
  (V.quotientForestRaw (R.recoveredFilteredPreimageAlphaValue z)).2

end ResolvedRecoveredPreimageAlphaValueMemSupply

end GaugeGeometry.QFT.Combinatorial
