import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitFromCover

/-!
# R-6c-body-141 — witnessSplit concrete construction: the two-branch backward map

Hundred-and-forty-first genuine-body step, opening the last box.  The bijection primitive `witnessSplit`
(body-139) is given its concrete two-branch shape — `if star-touch then forestPreimage else mixedPreimage` —
matching the flat `forestComponentSplitPhiInverseConstructionOfClassifier` (`Coassoc.lean:28811`) exactly.  The two
whole-`Sigma` round-trips (`forward_witness` / `backward_witness`) are then **proved** from four branch-local specs,
so `witnessSplit` is no longer a monolithic field.

## The branching (the flat classifier form)

For a codomain pair `z = (A, B)`, the star classifier `resolvedIsForestImage A B` (body-102) decides the branch:

```text
witnessSplit z = if h : resolvedIsForestImage z.1 z.2 then forestPreimage z h else mixedPreimage z h
```

* the **mixed** branch (`¬ resolvedIsForestImage`, `B` avoids `A`'s star): `mixedPreimage` — a primitive-only split
  choice (`inl true` / `inl false`, no `inr`);
* the **forest** branch (`resolvedIsForestImage`, `B` touches `A`'s star): `forestPreimage` — with the star-touching
  components tagged `inr Bᵧ`, star-avoiding `inl false`, the rest `inl true`.

This is the resolved image of the flat `inv := X.inv` built from the branch classifier's `forest_data` / `mixed_data`.

## The round-trips (PROVED from four branch specs)

With the forward map `fwdMap s = ⟨selectedOuterOf s, quotientForest s⟩` (`= ForestBlockCodType`), the two round-trips
reduce by `apply_dite` + `split_ifs` to the branch specs:

* `forward_witness` (`fwdMap (witnessSplit z) = z`): `apply_dite fwdMap` splits into `forest_forward` /
  `mixed_forward` (`fwdMap (forestPreimage z h) = z` / `fwdMap (mixedPreimage z h) = z`);
* `backward_witness` (`witnessSplit (fwdMap q) = q`): `split_ifs` on `resolvedIsForestImage (fwdMap q).1 (fwdMap
  q).2` splits into `forest_backward` / `mixed_backward` (`forestPreimage (fwdMap q) h = q` / `mixedPreimage (fwdMap
  q) h = q`).

So `.toWitnessSplitCoverSupply` produces body-139's `ResolvedWitnessSplitCoverSupply` — and hence the four
provider inverse laws — from `ResolvedWitnessSplitConcreteData`, whose content is now exactly the two branch
preimage constructors plus their four forward/backward specs.

## What remains (the branch-local geometry)

`mixedPreimage` / `forestPreimage` and their four specs are the branch-local backward reconstruction: the mixed
branch is the primitive relabelling (light), the forest branch reassembles the forest-choice parents from the
star-touching remnants (the de-contraction content).  They are fielded here; the star/`p`-tag facts (body-132/133)
follow from the same branch data.

Per the HALT: the branch preimage constructors and their forward/backward specs are fielded (they need the sector
backward geometry); the two whole round-trips are PROVED from them; `witnessSplit` is the concrete two-branch
`dite`, matching the flat classifier form.

Landed:

* `fwdMap` — the forward map as a named function;
* `ResolvedWitnessSplitConcreteData D S` — the two branch preimages + four branch specs;
* `.witnessSplit` — the two-branch `dite`;
* `.forward_witness` / `.backward_witness` — the two round-trips (PROVED from the branch specs);
* `.toWitnessSplitCoverSupply` — into body-139 (→ the four provider inverse laws).

Toolkit body (like body-139).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-141 — the forward map** `(A', p) ↦ (A, B)` as a named function (`= ForestBlockCodType`). -/
noncomputable def fwdMap (S : ResolvedConcreteSummandBundleSupply D) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ForestBlockCodType D G :=
  ⟨(S.Forward.imageSupply G).selectedOuterOf s, S.quotientForest s⟩

/-- **R-6c-body-141 — the two-branch witness-split data.**  The mixed / forest preimage constructors and their
four forward / backward specs against a fixed summand bundle `S` — the concrete content of the backward map. -/
structure ResolvedWitnessSplitConcreteData (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The mixed-branch preimage (`B` avoids the star; primitive-only choice). -/
  mixedPreimage : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 → ResolvedCoassocSplitChoice D G
  /-- The forest-branch preimage (`B` touches the star; forest-choice parents reassembled). -/
  forestPreimage : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → ResolvedCoassocSplitChoice D G
  /-- Mixed forward: the forward of the mixed preimage is `z`. -/
  mixed_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : ¬ resolvedIsForestImage z.1 z.2), fwdMap S (mixedPreimage z h) = z
  /-- Forest forward: the forward of the forest preimage is `z`. -/
  forest_forward : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (h : resolvedIsForestImage z.1 z.2), fwdMap S (forestPreimage z h) = z
  /-- Mixed backward: the mixed preimage of a mixed forward image is the original split choice. -/
  mixed_backward : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (h : ¬ resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2), mixedPreimage (fwdMap S q) h = q
  /-- Forest backward: the forest preimage of a forest forward image is the original split choice. -/
  forest_backward : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (h : resolvedIsForestImage (fwdMap S q).1 (fwdMap S q).2), forestPreimage (fwdMap S q) h = q

namespace ResolvedWitnessSplitConcreteData

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-141 — the concrete two-branch witness split** `if star-touch then forestPreimage else
mixedPreimage`. -/
noncomputable def witnessSplit (W : ResolvedWitnessSplitConcreteData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : ResolvedCoassocSplitChoice D G :=
  if h : resolvedIsForestImage z.1 z.2 then W.forestPreimage z h else W.mixedPreimage z h

/-- **R-6c-body-141 — the forward round-trip** (`fwdMap ∘ witnessSplit = id`), from the two branch forward specs. -/
theorem forward_witness (W : ResolvedWitnessSplitConcreteData D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) : fwdMap S (W.witnessSplit z) = z := by
  rw [witnessSplit, apply_dite (fwdMap S)]
  split_ifs with h
  · exact W.forest_forward z h
  · exact W.mixed_forward z h

/-- **R-6c-body-141 — the backward round-trip** (`witnessSplit ∘ fwdMap = id`), from the two branch backward
specs. -/
theorem backward_witness (W : ResolvedWitnessSplitConcreteData D S) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) : W.witnessSplit (fwdMap S q) = q := by
  rw [witnessSplit]
  split_ifs with h
  · exact W.forest_backward q h
  · exact W.mixed_backward q h

/-- **R-6c-body-141 — body-139's witness-split cover supply from the concrete two-branch data.** -/
noncomputable def toWitnessSplitCoverSupply (W : ResolvedWitnessSplitConcreteData D S) :
    ResolvedWitnessSplitCoverSupply D S where
  witnessSplit := fun {G} z => W.witnessSplit z
  forward_witness := fun {G} z => W.forward_witness z
  backward_witness := fun {G} q => W.backward_witness q

end ResolvedWitnessSplitConcreteData

end GaugeGeometry.QFT.Combinatorial
