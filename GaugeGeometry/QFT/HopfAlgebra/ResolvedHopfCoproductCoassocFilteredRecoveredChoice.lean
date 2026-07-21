import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredConcreteSummandValue

/-!
# R-6c-body-473 — the filtered recovered-choice owner (the recovered-side circularity guard) (PROVED)

Four-hundred-and-seventy-third genuine-body step — the load-bearing circularity guard: a small `F/V`-INDEPENDENT interface
that owns the raw recovered choice AND its filtered-domain membership together, so no recovered-side consumer ever takes a
bare `ResolvedCoassocSplitChoice` (which cannot feed `V.quotientForestRaw`).

* `ResolvedRecoveredPreimageValueMemSupply.recoveredPreimageValue_mem` — the total domain-carrier membership LOWERED to the
  body-283 owner (a `by_cases` over `resolvedIsForestImage` dispatching `forestPreimage_mem` / `mixedPreimage_mem`); reads
  NO `forward_roundtrip_value`, NO quotient geometry;
* `ResolvedFilteredRecoveredChoiceSupply` — the generic owner: `raw` (choice) + `mem` (membership), `F/V`-free;
* `.filtered` — the honest `FilteredForestBlockDom` witness `⟨raw z, mem z⟩`, with `_val` / proof-irrelevance `rfl` banks;
* `.toFilteredRecoveredChoiceSupply` — issues the generic owner from the legacy data (`raw := Tags.recoveredPreimageValue`,
  `mem := recoveredPreimageValue_mem`);
* `alpha_quotient_of_filtered_recovered` — the canonical-form type-check: `V.quotientForestRaw
  (R.toFilteredRecoveredChoiceSupply.filtered z)` type-checks (the quotient equality itself is NOT a field yet).

Per the HALT/guards: the alpha tag/closure chain is NOT duplicated here; old body-308 is left intact (the lowered theorem
coexists, a later body may alias it); NO fabricated choice / Classical membership; NO new geometry, NO `quot_eq`, NO `W'`
five conditions; strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the
unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
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

/-- **R-6c-body-473 — the recovered-preimage domain membership, LOWERED to the body-283 owner.** -/
theorem ResolvedRecoveredPreimageValueMemSupply.recoveredPreimageValue_mem
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    R.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G := by
  by_cases h : resolvedIsForestImage z.1 z.2
  · exact R.forestPreimage_mem z h
  · exact R.mixedPreimage_mem z h

/-- **R-6c-body-473 — the generic filtered recovered-choice owner** (`F/V`-independent): the raw choice + its membership. -/
structure ResolvedFilteredRecoveredChoiceSupply (D : ResolvedCoproductProperForestData) where
  /-- The raw recovered choice of a codomain point. -/
  raw : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ForestBlockDomType D G
  /-- The raw choice lands in the filtered forest-block domain. -/
  mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G), raw z ∈ forestBlockDomFinset G

/-- **R-6c-body-473 — the honest filtered recovered witness.** -/
def ResolvedFilteredRecoveredChoiceSupply.filtered (R : ResolvedFilteredRecoveredChoiceSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : FilteredForestBlockDom D G :=
  ⟨R.raw z, R.mem z⟩

/-- **R-6c-body-473 — the filtered witness's split choice is the raw choice** (`rfl`). -/
@[simp] theorem ResolvedFilteredRecoveredChoiceSupply.filtered_val
    (R : ResolvedFilteredRecoveredChoiceSupply D) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : (R.filtered z).1 = R.raw z := rfl

/-- **R-6c-body-473 — proof-irrelevance: the filtered witness ignores which membership proof is threaded** (`rfl`). -/
theorem ResolvedFilteredRecoveredChoiceSupply.filtered_ext
    (R : ResolvedFilteredRecoveredChoiceSupply D) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : R.raw z ∈ forestBlockDomFinset G) :
    R.filtered z = ⟨R.raw z, h⟩ :=
  Subtype.ext rfl

/-- **R-6c-body-473 ∎ — issue the generic owner from the legacy recovered-preimage data.** -/
noncomputable def ResolvedRecoveredPreimageValueMemSupply.toFilteredRecoveredChoiceSupply
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueMemSupply F V) : ResolvedFilteredRecoveredChoiceSupply D where
  raw := fun {_G} z => R.Tags.recoveredPreimageValue z
  mem := fun {_G} z => R.recoveredPreimageValue_mem z

/-- **R-6c-body-473 — canonical-form type-check.**  An alpha value root's quotient forest reads the filtered recovered
witness directly (the quotient equality itself is not yet a field). -/
theorem alpha_quotient_of_filtered_recovered
    {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (R : ResolvedRecoveredPreimageValueMemSupply F V)
    (Valpha : ResolvedFilteredConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (Valpha.quotientForestRaw (R.toFilteredRecoveredChoiceSupply.filtered z)).1
      ∈ D.carrier (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (R.toFilteredRecoveredChoiceSupply.filtered z).1) :=
  (Valpha.quotientForestRaw (R.toFilteredRecoveredChoiceSupply.filtered z)).2

end GaugeGeometry.QFT.Combinatorial
