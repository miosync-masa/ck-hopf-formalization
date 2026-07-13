import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterLeftFactorRaw
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCarryingBlock
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactorComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedFactorSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocNonemptyLeavesIntegration
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveSurvivalTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantTransport

/-!
# R-6c-body-259 — canonical `summand_agree_value` from the value root (PROVED, no `S` / `Forward`)

Two-hundred-and-fifty-ninth genuine-body step — the term migration's closure.  The value-side summand agreement
`ResolvedSummandAgreeValueSupply F V` (body-254) is constructed **canonically** — `.ofLegacy`-free — from `V + F`
alone, by feeding the three factor equalities (`hL` raw, `hR` `S`-free, `hQ := V.quot_eq`) into the generic
`resolved_splitChoice_summand_agree_of_factor_eqs` (`ForestCarryingBlock.lean:68`).  No
`ResolvedConcreteSummandBundleSupply` / `Forward` / total selected image supply appears in the declaration type or the
proof term.

## The three factor equalities (all from `V + F` + concrete lemmas)

```text
hL  = resolved_selectedOuter_left_factor_eq_of_parts_raw (body-258)
        (leftOf/promotedOf/cross := (resolvedConcreteForestPromoteSupply D G).{…} q.1  →  union = selectedOuterRawOf q.1)
        (hdisj := V.Measure.leftHDisj)     (left_primitive_factor_concrete)     (promoted_factor_of_hPD … V.Measure.promotedHPD)
hR  = resolved_quotientForest_right_factor_eq_of_parts   (S-free)
        (V.quotientForestRaw, V.Survivor…rightSurvivorForest, V.Remnant…remnantForest, V.hcross, V.union_eq, V.hRdisj,
         V.Survivor.toRightPrimitiveSurvivalTransportSupply.right_primitive_factor, V.Remnant.remnant_factor)
hQ  = V.quot_eq q.1
```

The genuine geometry leaves `hLdisj` / `hPD` are **theorems** on `V.Measure : ResolvedMeasureLeafSupply D`
(`NonemptyLeavesIntegration.lean:72/81`), not new fields — so no assembly record is needed.  Every gap to the generic
theorem's expected `(D.supply G).leftTerm A` / `.leftTerm B` / `.rightTerm B` closes by `rfl`/defeq
(`leftTerm A ≡ resolvedForestLeftTerm A.1`; `A.1 = selectedOuterRawOf q.1` via `fwdMapFilteredValue_outer_fst`; the
promote-supply accessors reduce by `rfl`).

Per the HALT: the canonical value summand agreement is constructed from `V + F` (no `S` / `Forward` / `.ofLegacy`);
this closes the proof-level term migration.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-259 — the canonical value summand agreement.**  `ResolvedSummandAgreeValueSupply F V` built from
`V + F` alone via the generic factor-eqs theorem — no `ResolvedConcreteSummandBundleSupply`, no `Forward`, no
`.ofLegacy`. -/
noncomputable def summand_agree_value_of_value (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) : ResolvedSummandAgreeValueSupply F V where
  summand_agree_value := fun {G} q => by
    have hL := resolved_selectedOuter_left_factor_eq_of_parts_raw q.1
      ((resolvedConcreteForestPromoteSupply D G).leftOf q.1)
      ((resolvedConcreteForestPromoteSupply D G).promotedOf q.1)
      ((resolvedConcreteForestPromoteSupply D G).cross q.1)
      (V.Measure.leftHDisj q.1)
      (left_primitive_factor_concrete q.1)
      (promoted_factor_of_hPD q.1 (V.Measure.promotedHPD q.1))
    have hR := resolved_quotientForest_right_factor_eq_of_parts q.1 _
      (V.quotientForestRaw q.1)
      (V.Survivor.survivor.rightSurvivorForest q.1)
      (V.Remnant.remnant.remnantForest q.1)
      (V.hcross q.1) (V.union_eq q.1) (V.hRdisj q.1)
      (V.Survivor.toRightPrimitiveSurvivalTransportSupply.right_primitive_factor q.1)
      (V.Remnant.remnant_factor q.1)
    exact resolved_splitChoice_summand_agree_of_factor_eqs q.1.1 q.1.2
      (fwdMapFilteredValue F V q).1 (fwdMapFilteredValue F V q).2 hL hR (V.quot_eq q.1)

end GaugeGeometry.QFT.Combinatorial
