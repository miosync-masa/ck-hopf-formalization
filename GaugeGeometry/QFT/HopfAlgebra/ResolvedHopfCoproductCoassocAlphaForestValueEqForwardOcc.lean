import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaForestValueEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaOccurrenceInversionInhabit

/-!
# R-6c-body-505 — alpha forest exact-B migrated onto the faithful forward socket (PROVED)

Five-hundred-and-fifth genuine-body step — continuing body-504's proof-ownership re-plumbing.  The body-493 forest
exact-`B` consumers are re-issued as `_forwardOcc` PARALLELS driven by body-502/503's faithful socket instead of the
legacy `∀ s` `OccInv`.

The forest exact-`B` uses `M.forestTag_agrees_multi S … z δ q.1 o hps hmm`, which is body-342's
`M.forestTag_agrees_of_innerIdx_occurrence … (M.innerIdx_occurrence S z δ q.1 o hps)`.  The only `OccInv`-dependent atom
is the inner `M.innerIdx_occurrence S (fwd q) δ q.1 o hps : HEq (M.innerIdx (fwd q) δ) o.B`; body-503's
`ForwardOcc.occurrence_inner_idx_alpha q δ o hps` has the SAME type, so the forest proof ports verbatim with that single
substitution.

## Migrated (Step 1.B)

```text
forestTag_agrees_alpha_forwardOcc
forest_value_eq_alpha_forwardOcc
```

Step 1.C (body-495 remnant correspondence — whose inner de-contraction runs at the RECOVERED `z`, not the forward `q`, so
it needs a distinct backward analysis) and Phases 2/3 (faithful Tags / houter / membership / round-trip / final wrapper)
are the body-506 continuation (per the plan's safe-stop — the forward-`q` forest exact-`B` is a clean self-contained
slice; the backward remnant threading and the full assembly are deferred rather than rushed).

Per the HALT/guards: the legacy `∀ s` `OccRaw` is NOT canonically inhabited; `toForestOccurrenceInversionSupply … OccRaw`
is NOT used in the new path; body-489 is NOT reverse-used for `hidx`; nothing is back-computed from body-492 quotient HEq
or coassoc; corrected permutations are NOT compared; `quot_eq` / `legComplete` are NOT entered; the legacy body-493
theorems stay valid conditionals (NON-destructive); strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc
claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-505 — forest exact-B, on the faithful socket** (body-493 mirror; `ForwardOcc` drives the inner
`innerIdx_occurrence`). -/
theorem forestTag_agrees_alpha_forwardOcc
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Measure : ResolvedMeasureLeafSupply D)
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
  exact M.forestTag_agrees_of_innerIdx_occurrence Fstar Measure z δ hmm
    (Data.occurrenceAlphaValue q γ hmem).B
    (ForwardOcc.occurrence_inner_idx_alpha q δ (Data.occurrenceAlphaValue q γ hmem) hps)

/-- **R-6c-body-505 — the forest exact-B leaf, on the faithful socket** (body-493 mirror). -/
theorem forest_value_eq_alpha_forwardOcc
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedFilteredConcreteSummandValueSupply D}
    (M : ResolvedMultiStarDecontractionSupply D) (Fstar : ResolvedCanonicalStarFacts D)
    (ForwardOcc : ResolvedForwardForestOccurrenceInversionAlphaValueSupply M Fmem V)
    (Measure : ResolvedMeasureLeafSupply D)
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
    dif_pos hmem,
    forestTag_agrees_alpha_forwardOcc M Fstar ForwardOcc Measure Data hForest hFT q γ hu hmem]
  exact congrArg Sum.inr
    (Sum.inr.inj ((Data.forest_choiceAt_eq_alpha_value q γ hmem).symm.trans hqB))

end GaugeGeometry.QFT.Combinatorial
