import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFilteredConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorTransport

/-!
# R-6c-body-471 — the alpha-native filtered value constructor + converters (OWNERSHIP ASSEMBLY)

Four-hundred-and-seventy-first genuine-body step — pure ownership assembly (ZERO new geometry): the corrected remnant
transport supply, the minimal alpha-native filtered-value construction root, its projection-only converter into the
body-470 filtered `V`, and the one-way legacy compatibility adapter.

* `canonicalCorrectedRemnantTransportSupply` — `remnant` (body-466 component supply), `remnantInj` (body-466 occurrence
  injectivity), `remnantGen` (body-466 gen ∘ `rightFactorOf_eq_rightTerm_of_choiceAt_inr`); NO `corrected = uncorrected`
  graph equality;
* `ResolvedAlphaNativeFilteredValueConstructionSupply` — the minimal honest root: `Measure`, `survivorInj`, `survivorGen`,
  `Quotient` (the body-469 filtered ownership, reading `Measure`);
* `.toFilteredConcreteSummandValueSupply` — projection-only: `Survivor` from the measure, `Remnant` the canonical
  transport, and quotient value / membership / `quot_eq` / `union_eq` ALL from the single `Quotient` projection
  (`hcross` = body-467, `hRdisj` = body-468, `union_eq` = body-469);
* `ResolvedConcreteSummandValueSupply.toFiltered` — the one-way legacy adapter (total fields restricted to `q.1`); NOT a
  constructor claiming the old total `V` is inhabited;
* `fwdMapFilteredAlphaValue_toFiltered` — the `rfl` regression anchor (`fwdMapFilteredAlphaValue F V.toFiltered q =
  fwdMapFilteredValue F V q`).

Per the HALT/guards: NO `W'` five-condition proof; NO `quot_eq` geometry; NO new geometry; strict `StarProm` /
`InnerStarRaw` NOT restored; the old total `V` inhabitability is NOT claimed; body-445 stays a valid conditional; the
downstream 71-file migration is a later body.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`,
no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
  (CarrierProper : ResolvedCarrierProperProvider D) (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-471 — the corrected remnant transport supply** (body-466 assembly). -/
noncomputable def canonicalCorrectedRemnantTransportSupply : ResolvedRemnantTransportSupply D where
  remnant := fun {G} => canonicalCorrectedRemnantComponentSupply Fstar CarrierProper
  remnantInj := fun {G} q _ _ _ _ heq =>
    correctedRemnantComponent_forestOccurrence_injective q Fstar CarrierProper heq
  remnantGen := fun {G} q γ =>
    (correctedRemnantComponent_gen q Fstar (q.forestComponentOccurrence γ)).trans
      (rightFactorOf_eq_rightTerm_of_choiceAt_inr (q.forestComponentOccurrence γ).hchoice).symm

/-- **R-6c-body-471 — the minimal alpha-native filtered-value construction root.**  Only the genuinely-owned leaves
`Measure`, `survivorInj`, `survivorGen`, and the body-469 filtered `Quotient`. -/
structure ResolvedAlphaNativeFilteredValueConstructionSupply
    (D : ResolvedCoproductProperForestData) (CarrierProper : ResolvedCarrierProperProvider D)
    (Fstar : ResolvedCanonicalStarFacts D) where
  /-- The measure-leaf supply. -/
  Measure : ResolvedMeasureLeafSupply D
  /-- Survivor `Finset` injectivity (over the measure survivor). -/
  survivorInj : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ q.rightComponents.attach, ∀ γ₂ ∈ q.rightComponents.attach,
      (survivorSupply_of_measure Measure G).survivorComponent q γ₁
        = (survivorSupply_of_measure Measure G).survivorComponent q γ₂ → γ₁ = γ₂
  /-- Survivor reembed generator equality (over the measure survivor). -/
  survivorGen : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ : {x : _ // x ∈ q.rightComponents},
      resolvedComponentGenTerm ((survivorSupply_of_measure Measure G).survivorComponent q γ)
        = resolvedComponentGenTerm γ.1.1
  /-- The filtered quotient ownership (reads `Measure`). -/
  Quotient : ResolvedFilteredQuotientOwnershipSupply D Measure CarrierProper Fstar

/-- **R-6c-body-471 ∎ — the projection-only converter into the filtered `V` root.** -/
noncomputable def ResolvedAlphaNativeFilteredValueConstructionSupply.toFilteredConcreteSummandValueSupply
    (C : ResolvedAlphaNativeFilteredValueConstructionSupply D CarrierProper Fstar) :
    ResolvedFilteredConcreteSummandValueSupply D where
  Measure := C.Measure
  Survivor :=
    { survivor := fun {G} => survivorSupply_of_measure C.Measure G
      survivorInj := C.survivorInj
      survivorGen := C.survivorGen }
  Remnant := canonicalCorrectedRemnantTransportSupply CarrierProper Fstar
  quotientForestRaw := fun q =>
    ResolvedFilteredQuotientOwnershipSupply.quotientForestRaw C.Measure CarrierProper Fstar C.Quotient q
  hcross := fun q =>
    (canonicalCorrectedQuotientForestCrossSupply Fstar C.Measure CarrierProper).cross q.1
  union_eq := fun q =>
    ResolvedFilteredQuotientOwnershipSupply.union_eq C.Measure CarrierProper Fstar C.Quotient q
  hRdisj := fun q =>
    canonicalCorrectedSurvivorRemnant_elements_disjoint Fstar C.Measure CarrierProper q.1
  quot_eq := fun q => C.Quotient.quot_eq q

variable (V : ResolvedConcreteSummandValueSupply D)

/-- **R-6c-body-471 — the one-way legacy compatibility adapter.**  Restricts the old total quotient fields to `q.1`; NOT a
claim that the old total `V` is inhabited. -/
def ResolvedConcreteSummandValueSupply.toFiltered : ResolvedFilteredConcreteSummandValueSupply D where
  Measure := V.Measure
  Survivor := V.Survivor
  Remnant := V.Remnant
  quotientForestRaw := fun q => V.quotientForestRaw q.1
  hcross := fun q => V.hcross q.1
  union_eq := fun q => V.union_eq q.1
  hRdisj := fun q => V.hRdisj q.1
  quot_eq := fun q => V.quot_eq q.1

/-- **R-6c-body-471 ∎ — the `rfl` regression anchor.**  The alpha forward map over the legacy adapter is the legacy
forward map. -/
theorem fwdMapFilteredAlphaValue_toFiltered (F : ResolvedSelectedOuterFilteredMemSupply D)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    fwdMapFilteredAlphaValue F V.toFiltered q = fwdMapFilteredValue F V q :=
  rfl

end GaugeGeometry.QFT.Combinatorial
