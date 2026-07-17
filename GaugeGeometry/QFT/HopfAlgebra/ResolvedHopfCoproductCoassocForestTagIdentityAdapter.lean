import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredIdentityRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestValueEqValue

/-!
# R-6c-body-362 — the forest-tag identity adapter: `Tags.forestTag = forestTag_fwd_value` (PROVED)

Three-hundred-and-sixty-second genuine-body step — the ONE type audit the consolidation needs.  Body-361 carries the
exact-`B` leaf in `M`'s vocabulary (`M.forestTag ≍ o.B`); body-288's `ResolvedForestValueEqValueSupply.forestTag_agrees`
reads it in `Tags`' vocabulary (`Tags.forestTag = forestTag_fwd_value`).  On the concrete multi-star `Tags` these are
the SAME map (`multiStarRegionTagValueSupply`'s `forestTag := M.forestTag`, an `rfl`), and `forestTag_fwd_value =
parent_recovered_value ▸ occurrenceValue.B` with `parent_recovered_value = rfl`, so `forestTag_fwd_value =
occurrenceValue.B` — exactly the `o.B` body-343 targets.  The adapter re-exposes body-341's definitional wiring, not a
new datum:

* `hFT` (the model's `Tags.forestTag = M.forestTag` — an `rfl` for the multi-star `Tags`) and `hForest`
  (`forestRecovered = forestRecoveredMulti`, also `rfl`) are the two wirings;
* `forestSource` recovers the source `δ`, and body-343's `forestTag_agrees_multi` at the `occurrenceValue`
  occurrence gives the `HEq`, aligned to the equality by proof-irrelevance on the parent membership.

Landed axiom-clean: `forestTag_agrees_for_identity_tags`.

Per the HALT: only the forest-tag identity adapter is proved; the mem/`Data`/round-trip/cover assembly is next; the
full `V.Remnant` provider is NOT claimed complete.  No forward hidden round-trip, no facade, no flat term, no
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

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-362 — the forest-tag identity adapter.**  The membership supply's `Tags.forestTag` equals its
`forestTag_fwd_value` at forward images, re-keying body-343 through the multi-star wirings `hFT` / `hForest`. -/
theorem forestTag_agrees_for_identity_tags (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (Data : ResolvedRecoveredPreimageValueMemSupply Fmem V)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (Data.Tags.Closure.unionOuterValue z).1.elements})
      (h : γ'.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      Data.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements})
    (hu : γ.1 ∈ (Data.Tags.Closure.unionOuterValue (fwdMapFilteredValue Fmem V q)).1.elements)
    (hmem : γ.1 ∈ (Data.Tags.Closure.Assembly.Region.forestRecovered
      (fwdMapFilteredValue Fmem V q)).elements) :
    Data.Tags.forestTag (fwdMapFilteredValue Fmem V q) ⟨γ.1, hu⟩ hmem
      = Data.forestTag_fwd_value q γ hmem := by
  have hfr : γ.1 ∈ (M.forestRecoveredMulti Fstar (fwdMapFilteredValue Fmem V q)).elements := by
    rw [← hForest (fwdMapFilteredValue Fmem V q)]; exact hmem
  rw [hFT (fwdMapFilteredValue Fmem V q) ⟨γ.1, hu⟩ hmem hfr]
  set z := fwdMapFilteredValue Fmem V q with hz
  set δ := M.forestSource Fstar z ⟨γ.1, hfr⟩ with hδ
  have hps : M.parent z δ = γ.1 := M.forestSource_spec Fstar z ⟨γ.1, hfr⟩
  have hmm : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements := hps ▸ hfr
  have hsub : (⟨γ.1, hfr⟩ : {x // x ∈ (M.forestRecoveredMulti Fstar z).elements})
      = ⟨M.parent z δ, hmm⟩ := Subtype.ext hps.symm
  apply eq_of_heq
  have hc : HEq (M.forestTag Fstar z ⟨γ.1, hfr⟩) (M.forestTag Fstar z ⟨M.parent z δ, hmm⟩) := by
    rw [hsub]
  refine hc.trans ?_
  exact M.forestTag_agrees_multi S Fstar Measure z δ q.1 (Data.occurrenceValue q γ hmem) hps hmm

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
