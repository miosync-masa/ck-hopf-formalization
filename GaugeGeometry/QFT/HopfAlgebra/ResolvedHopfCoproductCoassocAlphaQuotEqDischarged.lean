import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientExactResidual
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRetargetCoord
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceDischarged
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalUniqueConstructions
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractForget

/-!
# R-6c-body-529 — `internalEdges_domain` + socket inhabit + `quot_eq` DISCHARGED (PROVED)

Five-hundred-and-twenty-ninth genuine-body step — the final wiring.  From body-528's exact residual equality
`Q.internalEdges = R.map f`, the edge-domain field follows by pure subtraction algebra, the body-524 socket is inhabited,
and the adapter chain drives `quot_eq` from a hypothesis all the way down to a canonical theorem: `quot_eq` is no longer
assumed — it is DERIVED from the corrected two-stage geometry.

* **Step 5** — `multiset_sub_sub_cancel_common` (pure multiset cancellation) + `canonicalCorrected_internalEdges_domain`
  (`A.complementEdges.map f = Q.complementEdges`, via `multiset_map_sub_of_le` ×3);
* **Step 6A** — `canonicalCorrectedContractRetargetDomainSupply` (body-524's socket, INHABITED: field 1 = body-526, field
  2 = Step 5);
* **Step 6B** — the adapter chain `toContractTwiceFieldSupply ambientSupportOfW'` → `toContractClassEqSupply` →
  `toQuotEqConstructionSupply`;
* **Step 6C** — `coassoc_gen_of_canonicalMultiStar_alpha_construction_discharged`: native `W'` `Δᵣ`-coassociativity whose
  explicit roots are `Measure` / `E` / `ValueGeometry` / `rep*` only — `quot_eq` / `contract_class_eq` / the contract
  correspondence / global `σ` / `Fmem` / `Split` / `survivorInj` / `survivorGen` / `quotient_mem` / `OccRaw` / strict
  `StarProm` / `InnerStarRaw` are all GONE.

Attainment: pure construction artifacts ZERO; construction/model residual `ValueGeometry`; model laws `Measure` / `E` /
`rep*`.  This is NOT yet an unconditional-coassoc claim — the `ValueGeometry` `legComplete` / `parentCD` decomposition is
the next front.

Per the HALT/guards: count-safe; no `∉ Q.internalEdges` shortcut; `EdgeIdsUnique` NOT used as `Nodup`; `ValueGeometry` is
NOT decomposed; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc claim.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Step 5A — the generic cancellation -/

/-- **R-6c-body-529 — the central multiset cancellation.**  `(G - S) - (A - S) = G - A` for `S ≤ A ≤ G` (pure count). -/
theorem multiset_sub_sub_cancel_common {α : Type*} [DecidableEq α] {S A G : Multiset α}
    (hSA : S ≤ A) (hAG : A ≤ G) : (G - S) - (A - S) = G - A := by
  ext e
  simp only [Multiset.count_sub]
  have hSA' := Multiset.count_le_of_le e hSA
  have hAG' := Multiset.count_le_of_le e hAG
  omega

/-! ## Step 5B — the internal-edge domain -/

/-- **R-6c-body-529 ∎ — the edge-domain field.**  `A.complementEdges.map f = Q.complementEdges`, from body-528's exact
residual by pure subtraction algebra. -/
theorem canonicalCorrected_internalEdges_domain
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    q.1.1.1.complementEdges.map (fun e => e.retarget (selectedOuterVertexDomain q))
      = (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).complementEdges := by
  have hSA : ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).internalEdges ≤ q.1.1.1.internalEdges := selectedOuter_internalEdges_le_inputOuter q.1
  have hAG : q.1.1.1.internalEdges ≤ G.internalEdges := q.1.1.1.internalEdges_le
  have hSG : ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).internalEdges ≤ G.internalEdges := hSA.trans hAG
  have hQ : (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).internalEdges
      = (q.1.1.1.internalEdges
          - ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).internalEdges).map
          (((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1).retargetEdge
            (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
              ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1))) :=
    canonicalCorrectedQuotientRaw_internalEdges_eq_inputResidual Measure q
  show (G.internalEdges - q.1.1.1.internalEdges).map
        (((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
            q.1).retargetEdge
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
            ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
              q.1)))
      = (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).complementEdges
  rw [show (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).complementEdges
        = ((G.internalEdges
              - ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
                  q.1).internalEdges).map
            (((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
                q.1).retargetEdge
              (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
                ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
                  q.1))))
          - (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1).internalEdges
      from rfl,
    hQ, multiset_map_sub_of_le _ hAG, multiset_map_sub_of_le _ hSG, multiset_map_sub_of_le _ hSA]
  exact (multiset_sub_sub_cancel_common (Multiset.map_le_map hSA) (Multiset.map_le_map hAG)).symm

/-! ## Step 6A — the socket inhabitant -/

/-- **R-6c-body-529 ∎ — body-524's retarget-domain socket, INHABITED.** -/
noncomputable def canonicalCorrectedContractRetargetDomainSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E where
  retargetVertex_eq_on_G := fun q => canonicalCorrected_retargetVertex_eq_on_G q Measure E
  internalEdges_domain := fun q => canonicalCorrected_internalEdges_domain Measure q

/-! ## Step 6B — the adapter chain -/

/-- **R-6c-body-529 ∎ — the contract-twice field supply** (body-512), from the socket + `ambientSupportOfW'`. -/
noncomputable def canonicalCorrectedContractTwiceFieldSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalFilteredContractTwiceFieldSupply Measure E :=
  (canonicalCorrectedContractRetargetDomainSupply Measure E).toContractTwiceFieldSupply ambientSupportOfW'

/-- **R-6c-body-529 ∎ — the contract class-equality supply** (body-512 → body-511). -/
noncomputable def canonicalCorrectedContractClassEqSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalFilteredContractClassEqSupply Measure E :=
  (canonicalCorrectedContractTwiceFieldSupply Measure E).toContractClassEqSupply

/-- **R-6c-body-529 ∎ — the `quot_eq` construction supply** (body-511's `quotEq` residual, INHABITED). -/
noncomputable def canonicalCorrectedQuotEqConstructionSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) :
    ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply E :=
  (canonicalCorrectedContractClassEqSupply Measure E).toQuotEqConstructionSupply

/-! ## Step 6C — the final coassoc wrapper (`quot_eq` DISCHARGED) -/

/-- **R-6c-body-529 ∎ — native `W'` `Δᵣ`-coassociativity with `quot_eq` DISCHARGED.**  The explicit roots are `Measure` /
`E` / `ValueGeometry` / `rep*` only; `quot_eq` / `contract_class_eq` / the contract correspondence / global `σ` / `Fmem` /
`Split` / `survivorInj` / `survivorGen` / `quotient_mem` / `OccRaw` are all GONE. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_construction_discharged
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_quotEq_occurrence_discharged E
    (canonicalCorrectedQuotEqConstructionSupply Measure E) ValueGeometry rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
