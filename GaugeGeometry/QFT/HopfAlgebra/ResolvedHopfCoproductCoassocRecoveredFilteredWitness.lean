import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredRecoveredChoice
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaNativeFilteredValue

/-!
# R-6c-body-474 — the named recovered filtered witness + quotient normal form (CONSOLIDATION)

Four-hundred-and-seventy-fourth genuine-body step — consolidating the recovered side onto the body-473 circularity-guard
owner: the named canonical filtered witness, its `rfl` banks, the quotient NORMAL FORM every recovered-side consumer must
now use, and the legacy compatibility.

Scope note (honest): the FULL parallel alpha tag/closure/assembly mirror (a ~17-field `RecoveredRegionValueBridgeAssembly`
+ closure + tag supplies + their exclusivity/tag lemmas) is a large multi-structure migration and is left to a later body;
this body pins the canonical *witness/normal-form* boundary through the body-473 owner (which is `F/V`-independent), so the
recovered side already has a single canonical entry point that any alpha consumer reads.

* `recoveredFilteredPreimageValue` — the named canonical `FilteredForestBlockDom` witness of a recovered point
  (`R.toFilteredRecoveredChoiceSupply.filtered z`);
* `recoveredFilteredPreimageValue_fst` — `(…).1 = R.Tags.recoveredPreimageValue z` (`rfl`); the recovered-side raw-choice
  agreement;
* `alpha_quotientForestRaw_recoveredFilteredPreimageValue` — the quotient NORMAL FORM type-check: an alpha value root reads
  the witness directly (`V.quotientForestRaw (recoveredFilteredPreimageValue R z)`), the single canonical form the
  body-475 `ForwardOuter/QuotientValueGeometry` alpha migration routes through.

Per the HALT/guards: forward outer / quotient equality is NOT a field; the round-trip supply is NOT entered; canonical
geometry is NOT re-proved; old structures are NOT edited in place; NO `quot_eq`, NO `W'` membership, NO new geometry;
strict `StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
  {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-474 — the named canonical filtered witness of a recovered point.**  Every recovered-side consumer routes
through this instead of a bare `ResolvedCoassocSplitChoice`. -/
noncomputable def recoveredFilteredPreimageValue
    (R : ResolvedRecoveredPreimageValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : FilteredForestBlockDom D G :=
  R.toFilteredRecoveredChoiceSupply.filtered z

/-- **R-6c-body-474 — the witness's split choice is the raw recovered choice** (`rfl`). -/
@[simp] theorem recoveredFilteredPreimageValue_fst
    (R : ResolvedRecoveredPreimageValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (recoveredFilteredPreimageValue R z).1 = R.Tags.recoveredPreimageValue z :=
  rfl

/-- **R-6c-body-474 — proof-irrelevance: the witness ignores which membership proof is threaded** (`rfl`). -/
theorem recoveredFilteredPreimageValue_ext
    (R : ResolvedRecoveredPreimageValueMemSupply F V) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : R.Tags.recoveredPreimageValue z ∈ forestBlockDomFinset G) :
    recoveredFilteredPreimageValue R z = ⟨R.Tags.recoveredPreimageValue z, h⟩ :=
  Subtype.ext rfl

/-- **R-6c-body-474 ∎ — the quotient NORMAL FORM.**  An alpha value root's quotient forest reads the canonical recovered
witness directly — the single form the body-475 recovered-side geometry alpha migration routes through. -/
theorem alpha_quotientForestRaw_recoveredFilteredPreimageValue
    (R : ResolvedRecoveredPreimageValueMemSupply F V)
    (Valpha : ResolvedFilteredConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) :
    (Valpha.quotientForestRaw (recoveredFilteredPreimageValue R z)).1
      ∈ D.carrier (ResolvedCoassocSplitChoice.selectedOuterContractGraph
        (recoveredFilteredPreimageValue R z).1) :=
  (Valpha.quotientForestRaw (recoveredFilteredPreimageValue R z)).2

end GaugeGeometry.QFT.Combinatorial
