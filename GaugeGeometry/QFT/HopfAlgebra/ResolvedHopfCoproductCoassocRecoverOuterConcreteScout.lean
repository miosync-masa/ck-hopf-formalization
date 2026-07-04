import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingInvConstruct

/-!
# R-6c-body-138 — concrete recoverOuter/recoverChoice scout: the backward map is ONE witness split

Hundred-and-thirty-eighth genuine-body step, the boss scout.  It settles the concrete strategy for the backward
map `invConstruct : (A, B) ↦ (A', p)`, resolving the apparent per-`s` obstruction of the sector backward maps.

## The decisive type identity

`ResolvedCoassocSplitChoice D G` unfolds (`SplitChoice.lean:44`) to

```text
Σ A : {A // A ∈ D.carrier G}, ∀ γ ∈ A.1.elements.attach, (Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)
```

which is **definitionally `ForestBlockDomType D G`** (`ForestBlockBijection.lean:73`).  So the domain of the
backward map is exactly the split-choice type, and:

* a map `witnessSplit : ForestBlockCodType D G → ResolvedCoassocSplitChoice D G` **IS** an `invConstruct`
  (`ForestBlockCodType → ForestBlockDomType`);
* `recoverOuter z = (witnessSplit z).1`, `recoverChoice z = (witnessSplit z).2` — the two projections
  (body-134/135's fields are just `Sigma.fst` / `Sigma.snd` of one map).

So the whole reassembly collapses to **one function** `witnessSplit`, and the `s`-dependence "obstruction"
dissolves: the source split choice `s` **is** the output `witnessSplit z`, not something reconstructed
component-by-component from the sector maps.

## Why this is the flat pattern (type correspondence)

The flat backward map (`forestComponentSplitPhiInverseConstruction`, `Coassoc.lean:27993`) is likewise ONE map
`inv : forestQuotientForestSigma g → forestComponentSplitChoiceSigma g`, built from a **branch-decision cover**
(`forestComponentSplitPhiBranchDecisionPredicateCover`, `:28088`): a predicate `isForest` on RHS terms, plus
`forest_data` / `mixed_data` returning the preimage directly when the predicate holds / fails.  The sector maps are
the FORWARD helpers used to construct and verify that preimage — NOT a per-`s` reconstruction.  Correspondence:

| flat | resolved |
|---|---|
| `inv : forestQuotientForestSigma → forestComponentSplitChoiceSigma` | `witnessSplit : ForestBlockCodType → ResolvedCoassocSplitChoice` |
| `forestComponentSplitChoiceSigma` (the `(A', p)` domain) | `ResolvedCoassocSplitChoice = ForestBlockDomType` |
| `forestQuotientForestSigma` (the `(A, B)` codomain) | `ForestBlockCodType` |
| `isForest` branch predicate | `resolvedIsForestImage` (star-touch, body-102) |
| `forest_data` / `mixed_data` (preimage per branch) | `witnessSplit` on the forest / mixed cod classes |
| `right_inv : forestComponentSplitPhi (inv r) = r` | `right_inv` : `⟨selectedOuterOf (witnessSplit z), quotientForest …⟩ = z` (body-136) |
| `left_inv : inv (forestComponentSplitPhi q) = q` | `left_inv` : `witnessSplit ⟨selectedOuterOf q, quotientForest q⟩ = q` (body-136) |
| `inv_mem` (branch membership) | `mixed_/forest_ invFun_mem` (body-133, `p`-tag) |

## The strategy DECISION

Adopt the **witness-split construction**: `invConstruct := witnessSplit`, a single map into `ResolvedCoassocSplitChoice`.
Everything bodies 132–136 fielded is then a property of that one map:

* `right_inv` (body-136): the forward of `witnessSplit z` is `z` (the cover's surjective right-inverse);
* `left_inv` (body-136): `witnessSplit` of the forward of `q` is `q` (the cover's injective left-inverse);
* the star facts (body-132) and the `p`-tag facts (body-133): the tags of `witnessSplit z` by its branch class.

So the boss reduces to constructing ONE `witnessSplit` (the resolved branch-decision cover) and proving its two
round-trips — no separate `recoverOuter` union / `recoverChoice` tagging, and no sector-map re-parameterization.

Per the HALT: no round-trip is proved; the `witnessSplit` type is adopted and the flat↔resolved correspondence is
recorded; `recoverOuter` / `recoverChoice` are pinned as the two projections of `witnessSplit`.

Landed:

* `ResolvedRecoverOuterFromWitness D` — the single `witnessSplit` map;
* `.toReassemblyData` — body-134's reassembly data (projections of `witnessSplit`);
* `.invConstructFn` / `witnessSplit_eq_invConstruct` — the backward map is `witnessSplit`, verbatim.

Toolkit body (scout, like body-134).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-138 — the witness-split backward map.**  The single map `witnessSplit : (A, B) ↦ (A', p)` into
`ResolvedCoassocSplitChoice` (`= ForestBlockDomType`), the resolved analogue of the flat
`forestComponentSplitPhiInverseConstruction.inv`.  Its two projections are `recoverOuter` / `recoverChoice`. -/
structure ResolvedRecoverOuterFromWitness (D : ResolvedCoproductProperForestData) where
  /-- The backward map as a single split-choice-valued function. -/
  witnessSplit : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedCoassocSplitChoice D G

/-- **R-6c-body-138 — body-134's reassembly data as the two projections of `witnessSplit`.** -/
def ResolvedRecoverOuterFromWitness.toReassemblyData (W : ResolvedRecoverOuterFromWitness D) :
    ResolvedOuterMixingReassemblyData D where
  recoverOuter := fun {G} z => (W.witnessSplit z).1
  recoverChoice := fun {G} z => (W.witnessSplit z).2

/-- **R-6c-body-138 — the `∀ G`-form backward map** (`= witnessSplit`, verbatim). -/
def ResolvedRecoverOuterFromWitness.invConstructFn (W : ResolvedRecoverOuterFromWitness D)
    (G : ResolvedFeynmanGraph) : ForestBlockCodType D G → ForestBlockDomType D G :=
  fun z => W.witnessSplit z

/-- **R-6c-body-138 — the reassembly's `invConstruct` IS `witnessSplit`** (`rfl`; `ForestBlockDomType =
ResolvedCoassocSplitChoice`).  The whole backward map is one function. -/
@[simp] theorem ResolvedRecoverOuterFromWitness.witnessSplit_eq_invConstruct
    (W : ResolvedRecoverOuterFromWitness D) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    W.toReassemblyData.invConstruct z = W.witnessSplit z :=
  rfl

end GaugeGeometry.QFT.Combinatorial
