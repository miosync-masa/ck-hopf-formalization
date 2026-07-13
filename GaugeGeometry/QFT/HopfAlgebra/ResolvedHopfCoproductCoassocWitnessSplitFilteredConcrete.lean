import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitFilteredCover

/-!
# R-6c-body-251 — filtered witnessSplit branch data: the cover WITHOUT the legacy bridge (PROVED)

Two-hundred-and-fifty-first genuine-body step — the filtered restatement of the witnessSplit branch specs.  The branch
preimages + their filtered round-trip specs are stated against `fwdMapFiltered` (body-249), and the `dite` assembly
(body-141 mirror) builds `ResolvedWitnessSplitFilteredCoverSupply` (body-250) **without the legacy bridge** — the
cover's round-trips no longer route through `fwdMap S` / the retired total root in their statements.

## The filtered branch data

`ResolvedWitnessSplitFilteredConcreteData F S`: the two preimages (membership-free, classifier-guarded), their
domain-membership facts, and the four round-trip specs — all phrased against `fwdMapFiltered F S`:

```lean
forestPreimage / mixedPreimage : ForestBlockCodType D G → (¬)resolvedIsForestImage z.1 z.2 → ForestBlockDomType D G
forestPreimage_mem / mixedPreimage_mem : … z ∈ forestBlockCodFinset G → preimage z h ∈ forestBlockDomFinset G
forest_forward / mixed_forward : fwdMapFiltered F S ⟨preimage z h, preimage_mem z h hz⟩ = z
forest_backward / mixed_backward : preimage (fwdMapFiltered F S q) h = q.1
```

## The `dite` assembly (body-141 mirror, legacy-free)

`witnessSplitFiltered W z = if h : resolvedIsForestImage z.1 z.2 then forestPreimage z h else mixedPreimage z h`, its
membership by `split_ifs`, and the round-trips by `by_cases` on the classifier + `Subtype.ext (dif_pos/neg h)`
(proof irrelevance: `fwdMapFiltered`'s value depends only on the domain `.1`, not the carrier tag).  `toCover`
assembles them into the body-250 cover.

## Audit — the residual `Forward` boundary (body-253)

The branch **specs** now avoid `fwdMap S` (hence `S.Forward.selectedOuter_mem`, the retired total root).  But
`ResolvedConcreteSummandBundleSupply` still has `Forward : ResolvedForwardMapCoherenceSupply D` as a **required field**
(`ConcreteSummandBundle.lean:82`), whose sole leaf `selectedOuter_mem : ∀ s` (`ForwardMapCoherence.lean:72`) is false
at `p_R` — so `S` itself is **not canonically inhabitable as currently typed**.  Every *other* `Forward` use in the
bundle (`quotientForest`, `quot_eq`) is via `((Forward.imageSupply G).selectedOuterOf q).1`, which is `rfl`-defeq to
`selectedOuterRawOf q` (`ForwardMapCoherence.selectedOuter_eq`) — value-only, no membership tag.  So the residual
migration boundary is the **`Forward` field itself**; body-253 extracts a value-only bundle (dropping `Forward`,
retyping `quotientForest`/`quot_eq` via `selectedOuterRawOf`) to make the whole chain canonically inhabitable.

Per the HALT: the filtered branch data + the legacy-free `dite` assembly into the cover are defined/proved; no bundle
field is changed; the residual `Forward` boundary is named for body-253.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-251 — the filtered witnessSplit branch data.**  Preimages + membership + round-trip specs, all phrased
against `fwdMapFiltered` (no `fwdMap S`, no retired total root in the statements). -/
structure ResolvedWitnessSplitFilteredConcreteData (F : ResolvedSelectedOuterFilteredMemSupply D)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The mixed-branch preimage (classifier-negated), membership-free. -/
  mixedPreimage : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 → ForestBlockDomType D G
  /-- The forest-branch preimage (classifier), membership-free. -/
  forestPreimage : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → ForestBlockDomType D G
  /-- The mixed preimage lands in the filtered domain. -/
  mixedPreimage_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : ¬ resolvedIsForestImage z.1 z.2), z ∈ forestBlockCodFinset G →
    mixedPreimage z h ∈ forestBlockDomFinset G
  /-- The forest preimage lands in the filtered domain. -/
  forestPreimage_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : resolvedIsForestImage z.1 z.2), z ∈ forestBlockCodFinset G →
    forestPreimage z h ∈ forestBlockDomFinset G
  /-- The mixed-branch forward round-trip (against `fwdMapFiltered`). -/
  mixed_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G) (h : ¬ resolvedIsForestImage z.1 z.2),
    fwdMapFiltered F S ⟨mixedPreimage z h, mixedPreimage_mem z h hz⟩ = z
  /-- The forest-branch forward round-trip (against `fwdMapFiltered`). -/
  forest_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G) (h : resolvedIsForestImage z.1 z.2),
    fwdMapFiltered F S ⟨forestPreimage z h, forestPreimage_mem z h hz⟩ = z
  /-- The mixed-branch backward round-trip. -/
  mixed_backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (h : ¬ resolvedIsForestImage (fwdMapFiltered F S q).1 (fwdMapFiltered F S q).2),
    mixedPreimage (fwdMapFiltered F S q) h = q.1
  /-- The forest-branch backward round-trip. -/
  forest_backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (h : resolvedIsForestImage (fwdMapFiltered F S q).1 (fwdMapFiltered F S q).2),
    forestPreimage (fwdMapFiltered F S q) h = q.1

namespace ResolvedWitnessSplitFilteredConcreteData

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-251 — the filtered backward map** (`dite` on the classifier, body-141 mirror). -/
noncomputable def witnessSplitFiltered (W : ResolvedWitnessSplitFilteredConcreteData F S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ForestBlockDomType D G :=
  if h : resolvedIsForestImage z.1 z.2 then W.forestPreimage z h else W.mixedPreimage z h

/-- **R-6c-body-251 — the filtered backward map lands in the domain.** -/
theorem witnessSplitFiltered_mem (W : ResolvedWitnessSplitFilteredConcreteData F S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (hz : z ∈ forestBlockCodFinset G) :
    W.witnessSplitFiltered z ∈ forestBlockDomFinset G := by
  unfold witnessSplitFiltered
  split_ifs with h
  · exact W.forestPreimage_mem z h hz
  · exact W.mixedPreimage_mem z h hz

/-- **R-6c-body-251 — the filtered forward round-trip** (legacy-free, from the branch forward specs). -/
theorem forward_witnessFiltered (W : ResolvedWitnessSplitFilteredConcreteData F S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (hz : z ∈ forestBlockCodFinset G) :
    fwdMapFiltered F S ⟨W.witnessSplitFiltered z, W.witnessSplitFiltered_mem z hz⟩ = z := by
  by_cases h : resolvedIsForestImage z.1 z.2
  · have he : (⟨W.witnessSplitFiltered z, W.witnessSplitFiltered_mem z hz⟩ : FilteredForestBlockDom D G)
        = ⟨W.forestPreimage z h, W.forestPreimage_mem z h hz⟩ :=
      Subtype.ext (dif_pos h)
    rw [he]; exact W.forest_forward z hz h
  · have he : (⟨W.witnessSplitFiltered z, W.witnessSplitFiltered_mem z hz⟩ : FilteredForestBlockDom D G)
        = ⟨W.mixedPreimage z h, W.mixedPreimage_mem z h hz⟩ :=
      Subtype.ext (dif_neg h)
    rw [he]; exact W.mixed_forward z hz h

/-- **R-6c-body-251 — the filtered backward round-trip** (legacy-free, from the branch backward specs). -/
theorem backward_witnessFiltered (W : ResolvedWitnessSplitFilteredConcreteData F S)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    W.witnessSplitFiltered (fwdMapFiltered F S q) = q.1 := by
  unfold witnessSplitFiltered
  by_cases h : resolvedIsForestImage (fwdMapFiltered F S q).1 (fwdMapFiltered F S q).2
  · rw [dif_pos h]; exact W.forest_backward q h
  · rw [dif_neg h]; exact W.mixed_backward q h

/-- **R-6c-body-251 — the filtered cover from the filtered branch data** (legacy-bridge-free).  The round-trips are
discharged from the `fwdMapFiltered`-phrased branch specs, never through `fwdMap S` / the retired total root. -/
noncomputable def toCover (W : ResolvedWitnessSplitFilteredConcreteData F S) :
    ResolvedWitnessSplitFilteredCoverSupply F S where
  witnessSplit := W.witnessSplitFiltered
  witnessSplit_mem := W.witnessSplitFiltered_mem
  forward_witness := W.forward_witnessFiltered
  backward_witness := W.backward_witnessFiltered

end ResolvedWitnessSplitFilteredConcreteData

end GaugeGeometry.QFT.Combinatorial
