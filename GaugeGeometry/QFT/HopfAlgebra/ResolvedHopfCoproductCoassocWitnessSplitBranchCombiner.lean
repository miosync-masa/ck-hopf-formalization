import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitMixed
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitForest

/-!
# R-6c-body-144 — witnessSplit branch combiner: mixed ⊕ forest → the full backward map

Hundred-and-forty-fourth genuine-body step, a wiring win.  Body-142's mixed branch
(`ResolvedMixedPreimageData`) and body-143's forest branch (`ResolvedForestPreimageData`) are bundled into
body-141's `ResolvedWitnessSplitConcreteData`, completing the two-branch `witnessSplit` and, through body-139, the
four provider inverse laws.  After this, the bijection side needs only the branch-local outer reconstructions and
their round-trip specs — no separate witness machinery.

## The combiner (PROVED wiring)

`ResolvedWitnessSplitBranchSupply D S` holds one `Mixed` and one `Forest` preimage datum;
`.toWitnessSplitConcreteData` streams their preimage constructors and four forward/backward specs into body-141's
record:

```text
mixedPreimage  := Mixed.mixedPreimage      forestPreimage  := Forest.forestPreimage
mixed_forward  := Mixed.forward            forest_forward  := Forest.forward
mixed_backward := Mixed.backward           forest_backward := Forest.backward
```

`.toWitnessSplitCoverSupply` then chains body-141 → body-139, so the whole index/cover bijection
(`witnessSplit` + `forward_witness` / `backward_witness` + the four inverse laws) flows from `Mixed + Forest`.

The two branch `p`-tags are already proved (`Mixed.mixed_not_forestCarrying`, body-142;
`Forest.forest_isForestCarrying`, body-143) and are re-exported here (`.mixed_not_forestCarrying` /
`.forest_isForestCarrying`) for body-133's `invFun_mem` tags (which additionally need the `forestChoiceCarrier`
membership, a separate fact).

Per the HALT: no new geometry; the branch preimage constructors and specs are only bundled, not filled; the record
is flat (`Mixed` + `Forest`), avoiding `extends`-projection friction.

Landed:

* `ResolvedWitnessSplitBranchSupply D S` — the mixed + forest branch bundle;
* `.toWitnessSplitConcreteData` — body-141's two-branch data;
* `.toWitnessSplitCoverSupply` — body-139's cover supply (→ the four provider inverse laws);
* `.mixed_not_forestCarrying` / `.forest_isForestCarrying` — the two proved `p`-tags, re-exported.

Toolkit body (like body-139), one combiner supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-144 — the witness-split branch bundle.**  The mixed (body-142) and forest (body-143) preimage
data against a fixed summand bundle `S`. -/
structure ResolvedWitnessSplitBranchSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The mixed branch (primitive-only reconstruction, body-142). -/
  Mixed : ResolvedMixedPreimageData D S
  /-- The forest branch (de-contraction reconstruction, body-143). -/
  Forest : ResolvedForestPreimageData D S

namespace ResolvedWitnessSplitBranchSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-144 — body-141's two-branch witness-split data from the branch bundle.** -/
def toWitnessSplitConcreteData (W : ResolvedWitnessSplitBranchSupply D S) :
    ResolvedWitnessSplitConcreteData D S where
  mixedPreimage := fun {G} z h => W.Mixed.mixedPreimage z h
  forestPreimage := fun {G} z h => W.Forest.forestPreimage z h
  mixed_forward := fun {G} z h => W.Mixed.forward z h
  forest_forward := fun {G} z h => W.Forest.forward z h
  mixed_backward := fun {G} q h => W.Mixed.backward q h
  forest_backward := fun {G} q h => W.Forest.backward q h

/-- **R-6c-body-144 — body-139's witness-split cover supply from the branch bundle** (→ the four provider
inverse laws). -/
noncomputable def toWitnessSplitCoverSupply (W : ResolvedWitnessSplitBranchSupply D S) :
    ResolvedWitnessSplitCoverSupply D S :=
  W.toWitnessSplitConcreteData.toWitnessSplitCoverSupply

/-- **R-6c-body-144 — the mixed `p`-tag, re-exported** (body-142). -/
theorem mixed_not_forestCarrying (W : ResolvedWitnessSplitBranchSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    ¬ isForestCarryingChoice (W.Mixed.mixedPreimage z h).1 (W.Mixed.mixedPreimage z h).2 :=
  W.Mixed.mixed_not_forestCarrying z h

/-- **R-6c-body-144 — the forest `p`-tag, re-exported** (body-143). -/
theorem forest_isForestCarrying (W : ResolvedWitnessSplitBranchSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    isForestCarryingChoice (W.Forest.forestPreimage z h).1 (W.Forest.forestPreimage z h).2 :=
  W.Forest.forest_isForestCarrying z h

end ResolvedWitnessSplitBranchSupply

end GaugeGeometry.QFT.Combinatorial
