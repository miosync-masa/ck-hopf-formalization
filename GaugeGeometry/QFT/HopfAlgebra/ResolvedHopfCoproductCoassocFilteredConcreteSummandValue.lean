import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredQuotientValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue

/-!
# R-6c-body-470 — the filtered concrete summand value root + filtered forward map (IMPLEMENTATION)

Four-hundred-and-seventieth genuine-body step — landing the new filtered `V` root (all quotient-owned fields over a
FILTERED `q`, per the body-468 no-go) and the filtered forward map.  This is a structural landing body; the 71-file
downstream migration is deferred to a later body, and the `W'` five-condition / `quot_eq` geometry stays honest ownership.

* `ResolvedFilteredConcreteSummandValueSupply` — `Measure / Survivor / Remnant` total, quotient-owned fields
  (`quotientForestRaw / hcross / union_eq / hRdisj / quot_eq`) ALL over `q : FilteredForestBlockDom D G`;
* `fwdMapFilteredAlphaValue` — the filtered forward map (outer `selectedOuterRawOf q.1`, inner `V.quotientForestRaw q`);
* `fwdMapFilteredAlphaValue_outer_fst` / `_quotient` — the outer / quotient projections (`rfl` / `HEq.rfl`), the
  regression anchors for the downstream migration.

Per the HALT/guards: NO `W'` five-condition proof; NO `quot_eq` contract-twice geometry; strict `StarProm` /
`InnerStarRaw` NOT restored; the OLD total `ResolvedConcreteSummandValueSupply` is NOT claimed canonically inhabited;
body-445 stays a valid conditional; the corrected-remnant transport supply, the minimal alpha-native constructor +
converter, and the legacy adapter are the next body.  NOT the unconditional theorem.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-470 — the filtered concrete summand value root.**  Every quotient-owned field is over a filtered `q`
(leaving one raw would reinstate the body-468 defect); `Measure / Survivor / Remnant` stay total. -/
structure ResolvedFilteredConcreteSummandValueSupply (D : ResolvedCoproductProperForestData) where
  /-- The measure-leaf supply (total). -/
  Measure : ResolvedMeasureLeafSupply D
  /-- The right-survivor transport supply (total). -/
  Survivor : ResolvedRightSurvivorTransportSupply D
  /-- The remnant transport supply (total). -/
  Remnant : ResolvedRemnantTransportSupply D
  /-- The quotient forest index — over a FILTERED `q`. -/
  quotientForestRaw : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (D.supply (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).contractWithStars
      (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)))).ForestIdx
  /-- Survivor/remnant cross-disjointness — over a FILTERED `q`. -/
  hcross : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ∀ γ ∈ (Survivor.survivor.rightSurvivorForest q.1).elements,
    ∀ δ ∈ (Remnant.remnant.remnantForest q.1).elements, γ ≠ δ → γ.Disjoint δ
  /-- The quotient forest is survivor ∪ remnant — over a FILTERED `q`. -/
  union_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (quotientForestRaw q).1
      = (Survivor.survivor.rightSurvivorForest q.1).union (Remnant.remnant.remnantForest q.1) (hcross q)
  /-- Survivor and remnant are element-disjoint — over a FILTERED `q`. -/
  hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    Disjoint (Survivor.survivor.rightSurvivorForest q.1).elements
      (Remnant.remnant.remnantForest q.1).elements
  /-- The right-term agreement — over a FILTERED `q`. -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (D.supply G).rightTerm q.1.1
      = (D.supply (((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).contractWithStars
          (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)))).rightTerm
            (quotientForestRaw q)

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-470 — the filtered forward map over the alpha-native value root.** -/
noncomputable def fwdMapFilteredAlphaValue (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) : ForestBlockCodType D G :=
  ⟨⟨(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1,
      F.mem_of_mem_forestBlockDomFinset q.1 q.2⟩,
    V.quotientForestRaw q⟩

/-- **R-6c-body-470 — the forward map's outer forest is the raw selected outer** (`rfl`, regression anchor). -/
theorem fwdMapFilteredAlphaValue_outer_fst (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    (fwdMapFilteredAlphaValue F V q).1.1
      = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1 :=
  rfl

/-- **R-6c-body-470 ∎ — the forward map's quotient forest is the value bundle's** (`rfl`, regression anchor). -/
theorem fwdMapFilteredAlphaValue_quotient (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    (fwdMapFilteredAlphaValue F V q).2 = V.quotientForestRaw q :=
  rfl

end GaugeGeometry.QFT.Combinatorial
