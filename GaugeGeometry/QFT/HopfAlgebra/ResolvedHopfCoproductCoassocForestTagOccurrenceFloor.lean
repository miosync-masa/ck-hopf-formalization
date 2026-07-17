import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedForestTagBiUnion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagAgreesFloor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant

/-!
# R-6c-body-342 — exact-B compatibility floor: `forestTag_agrees` reduces to `HEq (innerIdx) o.B` (audit + reduction)

Three-hundred-and-forty-second genuine-body step — the exact-B compatibility floor audit for `forestTag_agrees`.
With `forestTag := M.forestTag` (body-333 CONSTRUCTION, not the old opaque body-282 field), `forestTag_agrees`
is no longer a standing model leaf: it REDUCES, via body-333's `forestTag_of_parent`, to a single elements-level
occurrence datum.  This body PROVES the reduction and pins the verdict on the residual floor.

## The chain

At the forward image `z = fwdMapFilteredValue F V q`, a `forestDomain z` component `δ` and the forest-choice
occurrence `o : q.1.ForestChoiceOccurrence` it matches satisfy:

```text
M.parent z δ = o.γ.1     -- forest bridge (body-278) + D4 uniqueness (localizedParent_ne); PROVABLE
M.innerIdx z δ = o.B     -- THE CORE (heterogeneous: HEq (M.innerIdx z δ) o.B)
```

Body-333's `forestTag_of_parent : HEq (M.forestTag … ⟨M.parent z δ, _⟩) (M.innerIdx z δ)` then composes with the
core by `HEq.trans` to give `HEq (M.forestTag … ⟨M.parent z δ, _⟩) o.B` — this IS `forestTag_agrees` (the tag at
the recovered parent equals the occurrence's chosen sub-forest).  Proved below as
`forestTag_agrees_of_innerIdx_occurrence`.

## Verdict on the residual floor `HEq (M.innerIdx z δ) o.B`

**It is a CONCRETE de-contraction (occurrence-inversion) datum, NOT free from M1/M3.** Equivalently, at
elements level (`ext_elements` lifts `ForestIdx.1` equality to the full forest):

```text
(innerRaw z δ …).elements = o.B.1.elements
```

* `forest_sound` / `forest_complete` (body-341's bridge gates) select the parent `γ` but **forget `B`** — they
  cannot pin *which* sub-forest, so they cannot yield exact-B on their own (the body-295 floor observation,
  now localized to `innerRaw` vs `o.B`).
* M3 (`promote_innerRaw_elements`) gives the PROMOTED elements `= touchedOuterComponents z δ`, i.e. the
  de-contracted forest's *promoted* image — NOT the raw `innerRaw.elements = o.B.1.elements` full-forest
  identity; the promote layer collapses exactly the datum in question.
* Using the forward round-trip or the existing `forestTag_agrees` (body-288) to prove it is CIRCULAR.

So the minimal honest floor is the occurrence-inversion `HEq (M.innerIdx z δ) o.B` (elements form
`innerRaw.elements = o.B.1.elements`), a concrete carrier fact: de-contracting `δ`'s touched components
recovers `q`'s original chosen forest.  It is the SAME transport as culprit-D (`ForestIdx transport`), so
fixing it discharges both at once.

Per the HALT: only the reduction is PROVED; the occurrence-inversion floor is NOT proved (it is the localized
concrete datum, `forestTag_of_parent`-composable); the forward quotient (body-290) is NOT entered; no forward
round-trip, no circular use of `forestTag_agrees`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and
NO `promote_collapse` / singleton / floor-297.
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

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-342 — `forestTag_agrees` from the occurrence-inversion floor.**  Composing body-333's
`forestTag_of_parent` (the constructed tag is heterogeneously the source's `innerIdx`) with the single
occurrence datum `HEq (M.innerIdx z δ) Bocc` yields the tag-agreement `HEq (forestTag …) Bocc` — the
`forestTag_agrees` shape.  The residual is ONLY the occurrence datum (audit: a concrete de-contraction
inversion, not free from M1/M3). -/
theorem forestTag_agrees_of_innerIdx_occurrence (Fstar : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (hmem : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements)
    {Hγ : ResolvedFeynmanGraph} (Bocc : (D.supply Hγ).ForestIdx)
    (hidx : HEq (M.innerIdx z δ) Bocc) :
    HEq (M.forestTag Fstar z ⟨M.parent z δ, hmem⟩) Bocc :=
  (M.forestTag_of_parent Fstar Measure z δ hmem).trans hidx

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
