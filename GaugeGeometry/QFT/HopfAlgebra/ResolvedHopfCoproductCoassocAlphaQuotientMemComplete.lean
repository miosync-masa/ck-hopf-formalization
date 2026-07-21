import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientComplement
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaQuotientMemDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSurvivorDischarge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResidualCountTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientRetargetTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementCountBackbone

/-!
# R-6c-body-501 — quotient complement completion + `quotient_mem` DISCHARGE (PROVED)

Five-hundred-and-first genuine-body step — the count-transport completion of body-500's core, closing body-499's sole
residual and DISCHARGING `quotient_mem`.  The reduced quotient root is thereby shrunk to `Measure + quot_eq`; the only
remaining honest quotient-ownership field is `quot_eq`.

## The witness transport (Steps 1–5)

The input outer `A := q.1.1.1` is a `W'` carrier member, so proper (5th `mem_iff` conjunct), so `0 < A.complementEdges.card`
— pick `e ∈ A.complementEdges` with `count e A.internalEdges < count e G.internalEdges` (body-431).  With `S ≤ A`
(body-500) the strict gap survives subtraction of `S.internalEdges`, and `e ∈ S.complementEdges`.  The through-`S`
retarget `f` is `InjOn` the ambient internal edges (body-436), so count transports both ways:

```text
count (f e) Q.internalEdges
  ≤ count (f e) (R.map f)              body-500 core (Q ≤ R.map f) + count_le_of_le
  = count e R                          count_map_eq_count_of_injOn_mem   (R = A.I − S.I ⊆ G.I)
  < count e S.complementEdges          subtraction arithmetic (count e A.I < count e G.I, S ≤ A)
  = count (f e) H.internalEdges        count_complementEdges_eq_count_contractWithStars (body-433)
```

so `count (f e) Q.internalEdges < count (f e) H.internalEdges`, hence `0 < Q.complementEdges.card`
(`complementEdges_card_pos_of_count_lt`).

## `quotient_mem` and the quotEq-only root (Steps 6–8)

`canonicalCorrectedQuotient_mem` feeds that positivity into body-499's `canonicalCorrectedQuotient_mem_of_complement` —
`quotient_mem` is now a THEOREM.  `ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply` keeps only `Measure` and
the honest `quot_eq`; its converter builds body-498's reduced root (filling `Quotient.quotient_mem` from the theorem), and
`coassoc_gen_of_canonicalMultiStar_alpha_quotEq_root` threads it into body-498's thin theorem — `quotient_mem` GONE.

```text
survivorInj / survivorGen   GONE (body-498)
Fmem / Split                GONE (body-496/497)
quotient_mem                GONE (this body)
remaining quotient root     quot_eq ONLY
```

Per the HALT/guards: everything stays count-safe (`EdgeIdsUnique` NOT used as `Nodup`, no `∉ Q.internalEdges` shortcut);
`quot_eq` itself is NOT proved (kept as the root's sole honest field); no raw `∀ s` membership (filtered `q`); no
back-computation from the forward round-trip; `OccRaw` / `ValueGeometry` NOT entered; strict `StarProm` / `InnerStarRaw`
stay ZERO; body-445/498/499/500 are NOT edited (new decls only); NO unconditional-coassoc claim.  No facade, no flat term,
no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable {G : ResolvedFeynmanGraph}

/-! ## The strict-count witness → quotient complement positivity -/

/-- **R-6c-body-501 ∎ — the quotient complement is nonempty.**  The input outer's complement witness `e`, retargeted
through `S`, is counted strictly less in `Q` than in the contract graph `H` (body-500 core + the two count transports), so
`Q.complementEdges.card > 0`. -/
theorem canonicalCorrectedQuotientRaw_complementEdges_card_pos
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    0 < (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).complementEdges.card := by
  set S := (resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
    q.1 with hSdef
  set f := S.retargetEdge (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G S) with hfdef
  -- Step 1 — the input-outer residual witness
  have hId : G.EdgeIdsUnique := edgeIdsUnique_of_carrier_mem q.1.1.2
  have hApf : q.1.1.1.IsProperForest :=
    ((mem_canonicalUniqueSupportedCarrier_iff _).mp q.1.1.2).2.2.2.2
  obtain ⟨e, heA⟩ := Multiset.card_pos_iff_exists_mem.mp
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest hApf)
  have hAG : Multiset.count e q.1.1.1.internalEdges < Multiset.count e G.internalEdges :=
    ResolvedAdmissibleSubgraph.count_lt_of_mem_complementEdges heA
  -- Step 2 — subtraction survives the strict gap
  have hSA : S.internalEdges ≤ q.1.1.1.internalEdges := selectedOuter_internalEdges_le_inputOuter q.1
  have hcSA : Multiset.count e S.internalEdges ≤ Multiset.count e q.1.1.1.internalEdges :=
    Multiset.count_le_of_le e hSA
  have heG : e ∈ G.internalEdges := Multiset.mem_of_le (Multiset.sub_le_self _ _) heA
  have heS : e ∈ S.complementEdges := by
    show e ∈ G.internalEdges - S.internalEdges
    rw [← Multiset.count_pos, Multiset.count_sub]; omega
  have hRstrict : Multiset.count e (q.1.1.1.internalEdges - S.internalEdges)
      < Multiset.count e S.complementEdges := by
    show Multiset.count e (q.1.1.1.internalEdges - S.internalEdges)
      < Multiset.count e (G.internalEdges - S.internalEdges)
    rw [Multiset.count_sub, Multiset.count_sub]; omega
  -- Step 3 — residual map-side transport
  have hRmap : Multiset.count (f e)
        ((q.1.1.1.internalEdges - S.internalEdges).map f)
      = Multiset.count e (q.1.1.1.internalEdges - S.internalEdges) :=
    count_map_eq_count_of_injOn_mem
      (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId S _)
      (fun a ha => Multiset.mem_of_le q.1.1.1.internalEdges_le
        (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)) heG
  -- Step 4 — contract-ambient transport
  have hH : Multiset.count e S.complementEdges
      = Multiset.count (f e) (S.contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G S)).internalEdges :=
    ResolvedAdmissibleSubgraph.count_complementEdges_eq_count_contractWithStars hId S _ heS
  -- Step 5 — the quotient's strict count
  have hQcount : Multiset.count (f e)
        (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).internalEdges
      ≤ Multiset.count (f e) ((q.1.1.1.internalEdges - S.internalEdges).map f) :=
    Multiset.count_le_of_le _
      (canonicalCorrectedQuotientRaw_internalEdges_le_inputResidual Measure _ _ q.1)
  refine ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_count_lt (e := f e) ?_
  show Multiset.count (f e)
      (canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1).internalEdges
    < Multiset.count (f e) (S.contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G S)).internalEdges
  omega

/-! ## `quotient_mem` — CANONICAL DERIVED -/

/-- **R-6c-body-501 ∎ — the canonical filtered quotient membership, DISCHARGED.**  body-499's assembly fed the
strict-count positivity; `quotient_mem` is now a THEOREM. -/
theorem canonicalCorrectedQuotient_mem
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    canonicalCorrectedQuotientRaw Measure
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        canonicalUniqueStarFactsOfW' q.1
      ∈ canonicalUniqueSupportedCarrierProperSupply.toData.carrier
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1) :=
  canonicalCorrectedQuotient_mem_of_complement Measure E q
    (canonicalCorrectedQuotientRaw_complementEdges_card_pos Measure q)

/-! ## The quotEq-only reduced root + signature wrapper -/

/-- **R-6c-body-501 — the canonical-`W'` quotEq-only construction root.**  Only `Measure` and the honest `quot_eq`; the
quotient membership is DERIVED. -/
structure ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The measure-leaf supply. -/
  Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData
  /-- The right-term agreement — the sole honest quotient-ownership field, over a filtered `q`. -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    (canonicalUniqueSupportedCarrierProperSupply.toData.supply G).rightTerm q.1.1
      = (canonicalUniqueSupportedCarrierProperSupply.toData.supply
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)).rightTerm
          ⟨canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1,
            canonicalCorrectedQuotient_mem Measure E q⟩

/-- **R-6c-body-501 ∎ — the converter into body-498's reduced quotient root.**  `Quotient.quotient_mem` is filled from
the discharged theorem; `quot_eq` passes through. -/
noncomputable def ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply.toAlphaNativeFilteredQuotientConstructionSupply
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (C : ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply E) :
    ResolvedAlphaNativeFilteredQuotientConstructionSupply
      canonicalUniqueSupportedCarrierProperSupply.toData
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      canonicalUniqueStarFactsOfW' where
  Measure := C.Measure
  Quotient :=
    { quotient_mem := fun {_G} q => canonicalCorrectedQuotient_mem C.Measure E q
      quot_eq := C.quot_eq }

/-- **R-6c-body-501 ∎ — canonical-`W'` native `Δᵣ`-coassociativity with `quotient_mem` DISCHARGED.**  A thin wrapper over
body-498's `coassoc_gen_of_canonicalMultiStar_alpha_quotient_root`: the quotEq-only root supplies the reduced root
internally, so `quotient_mem` is GONE from the signature.  The remaining explicit roots are `Measure + quot_eq` (as
`CquotEq`) / `E` / `ValueGeometry` / `OccRaw` / `rep`. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_quotEq_root
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (CquotEq : ResolvedCanonicalUniqueAlphaFilteredQuotEqConstructionSupply E)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_quotient_root
    (CquotEq.toAlphaNativeFilteredQuotientConstructionSupply E) E ValueGeometry OccRaw rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
