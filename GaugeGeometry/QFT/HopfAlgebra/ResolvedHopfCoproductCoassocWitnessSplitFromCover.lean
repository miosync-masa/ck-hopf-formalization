import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoverOuterConcreteScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-139 — witnessSplit from a cover: the exact bijection primitive is one map + two round-trips

Hundred-and-thirty-ninth genuine-body step, settling the source of `witnessSplit` (body-138).

## Scout conclusion: no proved concrete `witnessSplit` in the existing machinery

The candidate sources are exhausted:

* the **σ-cover** `ResolvedCoassocSplitPhiFiniteData` (`FiniteCover.lean`, support-9 route) offers only an
  *existential* `cover_on` (`∀ z ∈ imageCarrier, ∃ q ∈ forestCarrier ∪ mixedCarrier, imageOf q.1 = z`) plus
  `forest_inj_on` / `mixed_inj_on` — not a concrete `(A, B) ↦ (A', p)` function, and those `cover_on` / `inj_on`
  are themselves the fielded obligations of the *other* (support-9) route, which the outer-mixing route must not
  conflate with;
* every outer-mixing `invConstruct` / `mixedInvFun` / `forestInvFun` (bodies 99–104/112/131) is a **fielded**
  slot — the very obligation this campaign is discharging, not a source.

So `witnessSplit` is **not** recoverable as a proved map; it is the exact bijection primitive.  But because
`ForestBlockDomType = ResolvedCoassocSplitChoice` definitionally (body-138), the primitive is extraordinarily
compact: **one map plus two whole-`Sigma` round-trips** — the resolved image of the flat
`forestComponentSplitPhiInverseConstruction` (`inv` + `right_inv` + `left_inv`).

## The primitive (PROVED to feed the bijection)

`ResolvedWitnessSplitCoverSupply D S` fields:

* `witnessSplit : ForestBlockCodType D G → ResolvedCoassocSplitChoice D G` — the backward map;
* `forward_witness` : `⟨selectedOuterOf (witnessSplit z), quotientForest (witnessSplit z)⟩ = z` (the cover's
  surjective right-inverse, `forestComponentSplitPhi ∘ inv = id`);
* `backward_witness` : `witnessSplit ⟨selectedOuterOf q, quotientForest q⟩ = q` (the injective left-inverse,
  `inv ∘ forestComponentSplitPhi = id`).

Because `invConstruct = witnessSplit` (body-138, `rfl`), the two round-trips ARE body-131's four inverse laws
**verbatim** — no `Sigma.ext` split (body-136) is needed: `right_inv` = `forward_witness`, `left_inv` =
`backward_witness`, and the mixed / forest variants differ only in the unused domain hypothesis.  `.toReassemblyData`
gives body-134's reassembly and `.mixed_left_inv` / `.forest_left_inv` / `.mixed_right_inv` / `.forest_right_inv`
the four provider inverse-law fields.

## Net: the whole bijection is one map + two round-trips + the tag facts

Combined with bodies 132/133 (membership plumbing) the entire index/cover bijection now rests on:
`witnessSplit`, its two round-trips (`forward_witness` / `backward_witness`), and the four star / `p`-tag facts.
That is the minimal honest form of the backward map.

Per the HALT: no round-trip is proved; the σ-cover route is not conflated; `witnessSplit` is placed as the exact
primitive with its two round-trips, and shown to discharge the four inverse laws directly.

Landed:

* `ResolvedWitnessSplitCoverSupply D S` — `witnessSplit` + `forward_witness` + `backward_witness`;
* `.toReassemblyData` / `.invConstructFn` — the structured backward map;
* `.mixed_left_inv` / `.forest_left_inv` / `.mixed_right_inv` / `.forest_right_inv` — the four provider inverse laws.

Toolkit body (like body-138), one primitive supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-139 — the witness-split cover primitive.**  The single backward map `witnessSplit` together with
its two whole-`Sigma` round-trips against a fixed summand bundle `S` — the exact bijection primitive (the resolved
image of the flat `forestComponentSplitPhiInverseConstruction`). -/
structure ResolvedWitnessSplitCoverSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The backward map `(A, B) ↦ (A', p)` as a single split-choice-valued function. -/
  witnessSplit : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedCoassocSplitChoice D G
  /-- The surjective right-inverse: forward of the reconstruction is the identity. -/
  forward_witness : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (⟨(S.Forward.imageSupply G).selectedOuterOf (witnessSplit z),
        S.quotientForest (witnessSplit z)⟩ : ForestBlockCodType D G) = z
  /-- The injective left-inverse: reconstruction of the forward is the identity. -/
  backward_witness : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    witnessSplit (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G) = q

namespace ResolvedWitnessSplitCoverSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-139 — the witness-split reassembly data** (body-138). -/
def toRecoverOuterFromWitness (W : ResolvedWitnessSplitCoverSupply D S) :
    ResolvedRecoverOuterFromWitness D where
  witnessSplit := fun {G} z => W.witnessSplit z

/-- **R-6c-body-139 — body-134's reassembly data.** -/
def toReassemblyData (W : ResolvedWitnessSplitCoverSupply D S) : ResolvedOuterMixingReassemblyData D :=
  W.toRecoverOuterFromWitness.toReassemblyData

/-- **R-6c-body-139 — the `∀ G`-form backward map.** -/
def invConstructFn (W : ResolvedWitnessSplitCoverSupply D S) (G : ResolvedFeynmanGraph) :
    ForestBlockCodType D G → ForestBlockDomType D G :=
  fun z => W.witnessSplit z

/-- **R-6c-body-139 — the provider's `mixed_left_inv`** (= `backward_witness`, verbatim). -/
theorem mixed_left_inv (W : ResolvedWitnessSplitCoverSupply D S) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G) :
    W.toReassemblyData.invConstruct
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q :=
  W.backward_witness q

/-- **R-6c-body-139 — the provider's `forest_left_inv`.** -/
theorem forest_left_inv (W : ResolvedWitnessSplitCoverSupply D S) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) (hq : q ∈ forestCarryingDomFinset G) :
    W.toReassemblyData.invConstruct
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q :=
  W.backward_witness q

/-- **R-6c-body-139 — the provider's `mixed_right_inv`** (= `forward_witness`, verbatim). -/
theorem mixed_right_inv (W : ResolvedWitnessSplitCoverSupply D S) (G : ResolvedFeynmanGraph)
    (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf (W.toReassemblyData.invConstruct r),
        S.quotientForest (W.toReassemblyData.invConstruct r)⟩ : ForestBlockCodType D G) = r :=
  W.forward_witness r

/-- **R-6c-body-139 — the provider's `forest_right_inv`.** -/
theorem forest_right_inv (W : ResolvedWitnessSplitCoverSupply D S) (G : ResolvedFeynmanGraph)
    (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf (W.toReassemblyData.invConstruct r),
        S.quotientForest (W.toReassemblyData.invConstruct r)⟩ : ForestBlockCodType D G) = r :=
  W.forward_witness r

end ResolvedWitnessSplitCoverSupply

end GaugeGeometry.QFT.Combinatorial
