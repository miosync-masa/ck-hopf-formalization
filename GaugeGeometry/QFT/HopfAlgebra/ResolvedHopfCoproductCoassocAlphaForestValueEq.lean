import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaMembershipQz
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagIdentityAdapter

/-!
# R-6c-body-493 — forest exact-B DERIVED + the full canonical alpha round-trip + W' native coassoc (PROVED)

Four-hundred-and-ninety-third genuine-body step — the completion body.  The last opaque `forest_value_eq` leaf is DERIVED
(no `forestTag_agrees` field): bodies 288/362 are mirrored to the alpha recovered side, so `forest_value_eq` follows from
the `OccInv` exact-`B` transport + the body-488 forest-tag / forest-recovered wirings (both `rfl`).  The body-492
membership supply, the body-490 `houter`, and the body-492 filtered quotient HEq then assemble the body-479 round-trip
leaf, which the body-482 wrapper carries to native `W'` `Δᵣ`-coassociativity.

* `occurrenceAlphaValue` / `parent_recovered_alpha_value` (`rfl`) / `forestTag_fwd_alpha_value` /
  `forest_choiceAt_eq_alpha_value` — the body-288 recovered-occurrence helpers, over `fwdMapFilteredAlphaValue` + the
  body-479 alpha forest bridge;
* `forestTag_agrees_alpha` — the body-362 exact-`B` adapter over the alpha `Data` (`OccInv.innerIdx_occurrence` →
  `forestTag_agrees_multi`);
* `forest_value_eq_alpha` — the body-288 leaf-3 reduction (pure `recoverChoiceAlphaValue` unfold + `Sum.inr.inj`);
* `canonicalMultiStarAlphaRoundTripLeafSupply` — the body-479 round-trip leaf (`Data` bound ONCE);
* `coassoc_gen_of_canonicalMultiStar_alpha` — native `W'` coassociativity, a projection into the body-482 wrapper.

Per the HALT/guards: NO detour through the body-478 aggregate (490/492 used directly); `forestTag_agrees` is NOT re-fielded
as a new datum (exact-`B` is DERIVED from `OccInv`); corrected permutations are NOT compared; strict `StarProm` /
`InnerStarRaw` stay ZERO; `forest_nonempty` / `survivor_mem` / `remnant_mem` are the honest geometric inputs, kept explicit;
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

namespace ResolvedRecoveredPreimageAlphaValueMemSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-493 — the recovered forest occurrence** (alpha; its `B` comes from `q.1`'s own `choiceAt`, breaking the
cycle). -/
noncomputable def occurrenceAlphaValue (R : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredAlphaValue Fmem V q)).elements) :
    ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1 :=
  let hsel := (R.Tags.Closure.Assembly.forestRecovered_forward_alpha_membership q γ.1).mp hmem
  ⟨⟨γ.1, hsel.choose⟩, hsel.choose_spec.choose, hsel.choose_spec.choose_spec⟩

/-- **R-6c-body-493 — the parent recovery** (`rfl`). -/
theorem parent_recovered_alpha_value (R : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredAlphaValue Fmem V q)).elements) :
    (R.occurrenceAlphaValue q γ hmem).γ = γ :=
  rfl

/-- **R-6c-body-493 — the recovered forest tag** (the occurrence's `B`, transported to `γ`). -/
noncomputable def forestTag_fwd_alpha_value (R : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredAlphaValue Fmem V q)).elements) :
    (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  (R.parent_recovered_alpha_value q γ hmem) ▸ (R.occurrenceAlphaValue q γ hmem).B

/-- **R-6c-body-493 — the forest-component choice value** (body-200's `forest_choiceAt_eq`, alpha root). -/
theorem forest_choiceAt_eq_alpha_value (R : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hmem : γ.1 ∈ (R.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredAlphaValue Fmem V q)).elements) :
    q.1.2 γ (Finset.mem_attach _ _) = Sum.inr (R.forestTag_fwd_alpha_value q γ hmem) :=
  heq_transport_choice (R.occurrenceAlphaValue q γ hmem) γ (R.parent_recovered_alpha_value q γ hmem)

end ResolvedRecoveredPreimageAlphaValueMemSupply

/-- **R-6c-body-493 — the forest-tag identity adapter over the alpha `Data`** (body-362 mirror).  `Data.Tags.forestTag =
forestTag_fwd_alpha_value` at forward images, from the `OccInv` exact-`B` transport + the `hForest` / `hFT` wirings. -/
theorem forestTag_agrees_alpha
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (Data : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterAlphaValue z).1.elements})
      (h : γ'.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      Data.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterAlphaValue (fwdMapFilteredAlphaValue Fmem V q)).1.elements)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered
      (fwdMapFilteredAlphaValue Fmem V q)).elements) :
    Data.Tags.forestTag (fwdMapFilteredAlphaValue Fmem V q) ⟨γ.1, hu⟩ hmem
      = Data.forestTag_fwd_alpha_value q γ hmem := by
  have hfr : γ.1 ∈ (M.forestRecoveredMulti Fstar (fwdMapFilteredAlphaValue Fmem V q)).elements := by
    rw [← hForest (fwdMapFilteredAlphaValue Fmem V q)]; exact hmem
  rw [hFT (fwdMapFilteredAlphaValue Fmem V q) ⟨γ.1, hu⟩ hmem hfr]
  set z := fwdMapFilteredAlphaValue Fmem V q with hz
  set δ := M.forestSource Fstar z ⟨γ.1, hfr⟩ with hδ
  have hps : M.parent z δ = γ.1 := M.forestSource_spec Fstar z ⟨γ.1, hfr⟩
  have hmm : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements := hps ▸ hfr
  have hsub : (⟨γ.1, hfr⟩ : {x // x ∈ (M.forestRecoveredMulti Fstar z).elements})
      = ⟨M.parent z δ, hmm⟩ := Subtype.ext hps.symm
  apply eq_of_heq
  have hc : HEq (M.forestTag Fstar z ⟨γ.1, hfr⟩) (M.forestTag Fstar z ⟨M.parent z δ, hmm⟩) := by
    rw [hsub]
  refine hc.trans ?_
  exact M.forestTag_agrees_multi S Fstar Measure z δ q.1 (Data.occurrenceAlphaValue q γ hmem) hps hmm

/-- **R-6c-body-493 — the forest exact-B leaf, DERIVED** (body-288 leaf-3; pure `recoverChoiceAlphaValue` unfold +
`Sum.inr.inj`, using the DERIVED `forestTag_agrees_alpha`). -/
theorem forest_value_eq_alpha
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (Data : ResolvedRecoveredPreimageAlphaValueMemSupply Fmem V)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterAlphaValue z).1.elements})
      (h : γ'.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      Data.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterAlphaValue (fwdMapFilteredAlphaValue Fmem V q)).1.elements)
    (B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered (fwdMapFilteredAlphaValue Fmem V q)).elements)
    (hqB : q.1.2 γ (Finset.mem_attach _ _) = Sum.inr B) :
    Data.Tags.recoverChoiceAlphaValue (fwdMapFilteredAlphaValue Fmem V q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = Sum.inr B := by
  rw [ResolvedRegionTagAlphaValueSupply.recoverChoiceAlphaValue,
    if_neg (Data.Tags.forest_notMem_left (fwdMapFilteredAlphaValue Fmem V q) ⟨γ.1, hu⟩ hmem),
    if_neg (Data.Tags.forest_notMem_right (fwdMapFilteredAlphaValue Fmem V q) ⟨γ.1, hu⟩ hmem),
    dif_pos hmem, forestTag_agrees_alpha M Fstar S Measure Data hForest hFT q γ hu hmem]
  exact congrArg Sum.inr
    (Sum.inr.inj ((Data.forest_choiceAt_eq_alpha_value q γ hmem).symm.trans hqB))

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
  (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
  (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
  (Split : ResolvedAlphaValueQuotientRegionSplitSupply Fmem VBuild.toCanonicalFilteredValue)
  (forest_nonempty : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G),
    resolvedIsForestImage z.1 z.2 →
    ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).Closure.Assembly.Region.forestRecovered z).elements.Nonempty)
  (survivor_mem : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ ((survivorSupply_of_measure VBuild.Measure G).rightSurvivorForest
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ rightDomain z))
  (remnant_mem : ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalUniqueSupportedCarrierProperSupply.toData G)
    (x₁ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph
      ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)))
    (x₂ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G z.1.1))),
    HEq x₁ x₂ →
    (x₁ ∈ ((canonicalCorrectedRemnantComponentSupply canonicalUniqueStarFactsOfW'
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider).remnantForest
        ((canonicalMultiStarRegionTagAlphaValueSupply VBuild ValueGeometry OccRaw Split).recoveredPreimageAlphaValue z)).elements
      ↔ x₂ ∈ forestDomain z))

/-- **R-6c-body-493 — the full canonical alpha round-trip leaf** (`Data` bound ONCE).  `forward_outer_value` = body-490,
`forward_quotient_value` = body-492, `forest_value_eq` = the DERIVED body-493 leaf. -/
noncomputable def canonicalMultiStarAlphaRoundTripLeafSupply :
    ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply Fmem VBuild.toCanonicalFilteredValue where
  Data := canonicalMultiStarRecoveredPreimageAlphaValueMemSupply VBuild ValueGeometry OccRaw Split
    forest_nonempty survivor_mem remnant_mem
  forward_outer_value := fun z => canonicalMultiStar_alpha_houter VBuild ValueGeometry OccRaw Split z
  forward_quotient_value := fun z =>
    canonicalMultiStar_alpha_forward_quotient VBuild ValueGeometry OccRaw Split
      forest_nonempty survivor_mem remnant_mem z
  forest_value_eq := fun q γ hu B hmem hqB =>
    forest_value_eq_alpha
      (ValueGeometry.toCoreBuild.toValueCore.toDecontractionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore))
      canonicalUniqueStarFactsOfW'
      (ValueGeometry.toCoreBuild.toValueCore.toForestOccurrenceInversionSupply
        (canonicalUniqueInnerRawCarrierClosureSupply ValueGeometry.toCoreBuild.toValueCore) OccRaw)
      VBuild.Measure
      (canonicalMultiStarRecoveredPreimageAlphaValueMemSupply VBuild ValueGeometry OccRaw Split
        forest_nonempty survivor_mem remnant_mem)
      (fun {_G} _z => rfl) (fun {_G} _z _γ' _h _h' => rfl) q γ hu B hmem hqB

include VBuild ValueGeometry OccRaw Split forest_nonempty survivor_mem remnant_mem

/-- **R-6c-body-493 ∎ — native `W'` `Δᵣ`-coassociativity from the canonical alpha round-trip leaf.**  A projection into
the body-482 wrapper; `forest_nonempty` / `survivor_mem` / `remnant_mem` remain the honest geometric inputs. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonical_unique_alpha_roundtrip VBuild
    (canonicalMultiStarAlphaRoundTripLeafSupply VBuild ValueGeometry OccRaw Split
      forest_nonempty survivor_mem remnant_mem)
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
