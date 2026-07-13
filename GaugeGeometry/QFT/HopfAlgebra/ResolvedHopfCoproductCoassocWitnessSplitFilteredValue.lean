import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue

/-!
# R-6c-body-253 — the value-root witnessSplit cover: `S.Forward` eliminated from the round-trip chain (PROVED)

Two-hundred-and-fifty-third genuine-body step — the re-point that finishes the structural migration.  The filtered
witnessSplit cover and its branch data are restated over the **value root** `ResolvedConcreteSummandValueSupply`
(body-252, no `Forward`) and the value map `fwdMapFilteredValue`, so the canonical round-trip chain no longer mentions
`ResolvedConcreteSummandBundleSupply` / the retired total root `S.Forward` anywhere in its **statements**.

## The canonical value cover + branch data (legacy-free)

* `ResolvedWitnessSplitFilteredValueCoverSupply F V` — the cover, round-trips phrased against `fwdMapFilteredValue F V`.
* `ResolvedWitnessSplitFilteredValueConcreteData F V` — the branch preimages + membership + round-trip specs, also
  against `fwdMapFilteredValue F V`.
* `toCover` — the `dite` assembly (body-141 mirror), proved verbatim as in body-251 (`Subtype.ext (dif_pos/neg h)`,
  proof irrelevance: `fwdMapFilteredValue`'s value depends only on the domain `.1`).  It uses **no** `.ofLegacy` and
  **no** `ResolvedConcreteSummandBundleSupply`.

The design guard holds: the canonical declarations never name `ResolvedConcreteSummandBundleSupply`; `toCover` never
uses a legacy bridge; deleting `fwdMapFilteredValue_ofLegacy_eq` (body-252) leaves this file type-checking; every
forward/backward law is quantified over the filtered domain / codomain membership.

## Residual migration boundary (body-254+)

The **round-trip / witnessSplit** layer is now `Forward`-free.  The next boundary is the **term-agreement** path
`summand_agree` / `toSummandBundle` (`ConcreteSummandBundle.lean:114-139`), whose statement still routes through
`S.toSummandBundle` (built via `S.Forward.toSummandBundle`).  Every occurrence there is again `selectedOuterOf … .1 =
selectedOuterRawOf …` (`rfl`-defeq), and its data are exactly `V.quotientForestRaw` / `V.Survivor` / `V.Remnant` /
`V.Measure` / `V.quot_eq` — all carried by the value root — so a value-side `summand_agree` restatement drops
`S.Forward` there too.  That restatement is the next migration step; after it, the retired total root survives only
inside the `.ofLegacy` comparison lemmas.

Per the HALT: the value cover + value branch data + the legacy-free `toCover` are defined/proved; the term-agreement
boundary is named; no bundle field is changed.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-253 — the value-root filtered witnessSplit cover.**  Round-trips phrased against `fwdMapFilteredValue`
(value root, no `Forward`). -/
structure ResolvedWitnessSplitFilteredValueCoverSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The backward map, total on the codomain. -/
  witnessSplit : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ForestBlockDomType D G
  /-- The backward map lands in the filtered domain. -/
  witnessSplit_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    z ∈ forestBlockCodFinset G → witnessSplit z ∈ forestBlockDomFinset G
  /-- Forward round-trip on the filtered domain. -/
  forward_witness : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G),
    fwdMapFilteredValue F V ⟨witnessSplit z, witnessSplit_mem z hz⟩ = z
  /-- Backward round-trip on the filtered domain. -/
  backward_witness : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    witnessSplit (fwdMapFilteredValue F V q) = q.1

/-- **R-6c-body-253 — the value-root filtered witnessSplit branch data.**  Preimages + membership + round-trip specs,
all phrased against `fwdMapFilteredValue` (no `fwdMap S`, no retired total root). -/
structure ResolvedWitnessSplitFilteredValueConcreteData (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
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
  /-- The mixed-branch forward round-trip (against `fwdMapFilteredValue`). -/
  mixed_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G) (h : ¬ resolvedIsForestImage z.1 z.2),
    fwdMapFilteredValue F V ⟨mixedPreimage z h, mixedPreimage_mem z h hz⟩ = z
  /-- The forest-branch forward round-trip (against `fwdMapFilteredValue`). -/
  forest_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestBlockCodFinset G) (h : resolvedIsForestImage z.1 z.2),
    fwdMapFilteredValue F V ⟨forestPreimage z h, forestPreimage_mem z h hz⟩ = z
  /-- The mixed-branch backward round-trip. -/
  mixed_backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (h : ¬ resolvedIsForestImage (fwdMapFilteredValue F V q).1 (fwdMapFilteredValue F V q).2),
    mixedPreimage (fwdMapFilteredValue F V q) h = q.1
  /-- The forest-branch backward round-trip. -/
  forest_backward : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (h : resolvedIsForestImage (fwdMapFilteredValue F V q).1 (fwdMapFilteredValue F V q).2),
    forestPreimage (fwdMapFilteredValue F V q) h = q.1

namespace ResolvedWitnessSplitFilteredValueConcreteData

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-253 — the value-root filtered backward map** (`dite` on the classifier). -/
noncomputable def witnessSplitFilteredValue (W : ResolvedWitnessSplitFilteredValueConcreteData F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ForestBlockDomType D G :=
  if h : resolvedIsForestImage z.1 z.2 then W.forestPreimage z h else W.mixedPreimage z h

/-- **R-6c-body-253 — the value-root backward map lands in the domain.** -/
theorem witnessSplitFilteredValue_mem (W : ResolvedWitnessSplitFilteredValueConcreteData F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (hz : z ∈ forestBlockCodFinset G) :
    W.witnessSplitFilteredValue z ∈ forestBlockDomFinset G := by
  unfold witnessSplitFilteredValue
  split_ifs with h
  · exact W.forestPreimage_mem z h hz
  · exact W.mixedPreimage_mem z h hz

/-- **R-6c-body-253 — the value-root forward round-trip** (legacy-free). -/
theorem forward_witnessFilteredValue (W : ResolvedWitnessSplitFilteredValueConcreteData F V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (hz : z ∈ forestBlockCodFinset G) :
    fwdMapFilteredValue F V ⟨W.witnessSplitFilteredValue z, W.witnessSplitFilteredValue_mem z hz⟩ = z := by
  by_cases h : resolvedIsForestImage z.1 z.2
  · have he : (⟨W.witnessSplitFilteredValue z, W.witnessSplitFilteredValue_mem z hz⟩ :
          FilteredForestBlockDom D G)
        = ⟨W.forestPreimage z h, W.forestPreimage_mem z h hz⟩ :=
      Subtype.ext (dif_pos h)
    rw [he]; exact W.forest_forward z hz h
  · have he : (⟨W.witnessSplitFilteredValue z, W.witnessSplitFilteredValue_mem z hz⟩ :
          FilteredForestBlockDom D G)
        = ⟨W.mixedPreimage z h, W.mixedPreimage_mem z h hz⟩ :=
      Subtype.ext (dif_neg h)
    rw [he]; exact W.mixed_forward z hz h

/-- **R-6c-body-253 — the value-root backward round-trip** (legacy-free). -/
theorem backward_witnessFilteredValue (W : ResolvedWitnessSplitFilteredValueConcreteData F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G) :
    W.witnessSplitFilteredValue (fwdMapFilteredValue F V q) = q.1 := by
  unfold witnessSplitFilteredValue
  by_cases h : resolvedIsForestImage (fwdMapFilteredValue F V q).1 (fwdMapFilteredValue F V q).2
  · rw [dif_pos h]; exact W.forest_backward q h
  · rw [dif_neg h]; exact W.mixed_backward q h

/-- **R-6c-body-253 — the value cover from the value branch data** (legacy-bridge-free, `Forward`-free).  Round-trips
discharged from the `fwdMapFilteredValue`-phrased branch specs; no `ResolvedConcreteSummandBundleSupply` appears. -/
noncomputable def toCover (W : ResolvedWitnessSplitFilteredValueConcreteData F V) :
    ResolvedWitnessSplitFilteredValueCoverSupply F V where
  witnessSplit := W.witnessSplitFilteredValue
  witnessSplit_mem := W.witnessSplitFilteredValue_mem
  forward_witness := W.forward_witnessFilteredValue
  backward_witness := W.backward_witnessFilteredValue

end ResolvedWitnessSplitFilteredValueConcreteData

end GaugeGeometry.QFT.Combinatorial
