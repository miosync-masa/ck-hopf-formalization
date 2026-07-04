import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRoundTrips
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitBranchCombiner

/-!
# R-6c-body-147 — region round-trip reduction: the branch forward/backward specs from the outer/choice round-trips

Hundred-and-forty-seventh genuine-body step, closing the proof-shape of the backward map.  The four branch
forward/backward specs (body-142/143) are **derived** from two whole-split-choice round-trips — the outer/quotient
round-trip and the outer/choice round-trip — via `Sigma.ext`.  Together with body-146's region tags, this produces
BOTH branch data (`ResolvedMixedPreimageData` / `ResolvedForestPreimageData`) and, through body-144/141/139, the
whole index/cover bijection, entirely from the region-local facts.

## The two round-trips (fielded) and the four branch specs (PROVED)

Since `mixedOuter = forestOuter = unionOuter` (body-145) and both branches share `recoverChoice` (body-146), the
four branch forward/backward specs are the SAME two round-trips (the branch hypothesis `h` is unused in the
reconstruction).  `ResolvedRegionRoundTripReductionSupply D S` fields them at the `Sigma`-component level:

* `forward_outer` / `forward_quotient` — `selectedOuterOf ⟨unionOuter z, recoverChoice z⟩ = z.1` and the (HEq)
  `quotientForest … = z.2` — the forward round-trip (`fwdMap ∘ reconstruct = id`);
* `backward_outer` / `backward_choice` — `unionOuter (fwdMap q) = q.1` and the (HEq) `recoverChoice … = q.2` — the
  backward round-trip (`reconstruct ∘ fwdMap = id`).

`Sigma.ext` assembles each into the branch spec:
`mixed_forward` = `forest_forward` = `Sigma.ext forward_outer forward_quotient`;
`mixed_backward` = `forest_backward` = `Sigma.ext backward_outer backward_choice`.

## What this produces

`.toMixedPreimageData` / `.toForestPreimageData` fill body-142/143's records entirely from the region supply
(`mixedOuter`/`forestOuter` = `unionOuter`, `mixedChoice`/`forestChoice` = `recoverChoice`, `mixed_no_forest` =
`all_inl`, `forest_has_inr` = `exists_inr`, and the two round-trips).  `.toBranchSupply` bundles them into body-144's
`ResolvedWitnessSplitBranchSupply`, so the entire backward map — `witnessSplit`, its two whole round-trips, and the
four provider inverse laws — flows from `ResolvedRegionRoundTripReductionSupply`.

So the backward map's proof-shape is fully local: the residual is the region geometry only — the two `Sigma`-level
round-trips (`forward_outer` / `forward_quotient` / `backward_outer` / `backward_choice`), the three region tags,
and the `forestRecovered` empty/nonempty — plus the outer union construction of body-145.

Per the HALT: no region fact is proved; the four branch specs are derived from the two round-trips by `Sigma.ext`;
`backward_choice` / `forward_quotient` are the fielded (HEq) choice/quotient parts.

Landed:

* `ResolvedRegionRoundTripReductionSupply D S` — the region supply + the two `Sigma`-level round-trips;
* `.toMixedPreimageData` / `.toForestPreimageData` — body-142/143's branch data (PROVED specs);
* `.toBranchSupply` — body-144's branch bundle (→ `witnessSplit` → the four provider inverse laws).

Toolkit body (like body-146).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-147 — the region round-trip reduction supply.**  The region choice supply (body-146) together with
the two `Sigma`-component round-trips (outer/quotient forward, outer/choice backward). -/
structure ResolvedRegionRoundTripReductionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The region choice / tag supply (body-146). -/
  Region : ResolvedRegionChoiceRoundTripSupply D S
  /-- Forward outer: the selected outer of the reconstruction is the original `A`. -/
  forward_outer : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) = z.1
  /-- Forward quotient: the quotient forest of the reconstruction is the original `B` (heterogeneous). -/
  forward_quotient : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
      (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2
  /-- Backward outer: the reconstruction's outer of a forward image is the original outer. -/
  backward_outer : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Region.Union.unionOuter (fwdMap S q) = q.1
  /-- Backward choice: the reconstruction's choice of a forward image is the original choice (heterogeneous). -/
  backward_choice : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    HEq (Region.recoverChoice (fwdMap S q)) q.2

namespace ResolvedRegionRoundTripReductionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-147 — body-142's mixed preimage data from the region round-trips.** -/
def toMixedPreimageData (R : ResolvedRegionRoundTripReductionSupply D S) :
    ResolvedMixedPreimageData D S where
  mixedOuter := fun {G} z h => R.Region.Union.unionOuter z
  mixedChoice := fun {G} z h => R.Region.recoverChoice z
  mixed_no_forest := fun {G} z h => R.Region.all_inl z h
  mixed_forward := fun {G} z h => Sigma.ext (R.forward_outer z) (R.forward_quotient z)
  mixed_backward := fun {G} q h => Sigma.ext (R.backward_outer q) (R.backward_choice q)

/-- **R-6c-body-147 — body-143's forest preimage data from the region round-trips.** -/
def toForestPreimageData (R : ResolvedRegionRoundTripReductionSupply D S) :
    ResolvedForestPreimageData D S where
  forestOuter := fun {G} z h => R.Region.Union.unionOuter z
  forestChoice := fun {G} z h => R.Region.recoverChoice z
  forest_has_inr := fun {G} z h => R.Region.exists_inr z h
  forest_forward := fun {G} z h => Sigma.ext (R.forward_outer z) (R.forward_quotient z)
  forest_backward := fun {G} q h => Sigma.ext (R.backward_outer q) (R.backward_choice q)

/-- **R-6c-body-147 — body-144's branch bundle from the region round-trips** (→ `witnessSplit` → the four provider
inverse laws). -/
def toBranchSupply (R : ResolvedRegionRoundTripReductionSupply D S) :
    ResolvedWitnessSplitBranchSupply D S where
  Mixed := R.toMixedPreimageData
  Forest := R.toForestPreimageData

end ResolvedRegionRoundTripReductionSupply

end GaugeGeometry.QFT.Combinatorial
