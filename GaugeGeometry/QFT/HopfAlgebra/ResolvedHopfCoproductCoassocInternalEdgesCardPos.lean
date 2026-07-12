import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# R-6c-body-246 — aggregate positive internal edges from a nonempty forest with positive components (PROVED)

Two-hundred-and-forty-sixth genuine-body step — the third `IsProperForest` conjunct `0 < A.internalEdges.card`
(`ResolvedSubGraph.lean:151`, the aggregate `Multiset`) for the constructed forests, generic.  Body-237's scout fixed
the dependency: it needs a **witness component** (`IsNonempty`, body-241/244) with a positive internal-edge count
(`HasPositiveInternalEdgesComponents`, body-238) — that component contributes an edge to the aggregate multiset.

## The lemma

```lean
internalEdges_card_pos_of_isNonempty
  (A : ResolvedAdmissibleSubgraph G) (hA : A.IsNonempty) (hPos : A.HasPositiveInternalEdgesComponents) :
  0 < A.internalEdges.card
```

`hA` gives a component `γ ∈ A.elements`; `hPos γ` gives an edge `e ∈ γ.internalEdges`; `mem_internalEdges`
(`ResolvedCoproductIndex.lean:38`) lifts it to `e ∈ A.internalEdges`; `Multiset.card_pos_iff_exists_mem` closes.

## What this settles

Conjunct #3 is now suppliable for both constructed forests:

* `X = selectedOuterRawOf` — from `selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier` (body-244) +
  `hasPositiveInternalEdgesComponents_of_cdPositive` (body-238);
* `Y = recovered-outer union` — from `recoveredOuter_isNonempty` (body-241) + body-238.

The only remaining `IsProperForest` conjunct is #5 `0 < A.complementEdges.card` (strict properness).

Per the HALT: only this conjunct is proved — no `complementEdges`, no certificate assembled.  No facade, no flat term,
no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace ResolvedAdmissibleSubgraph

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]
variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-246 — aggregate internal edges are positive for a nonempty forest with positive components.**  A
witness component contributes an edge to the aggregate multiset. -/
theorem internalEdges_card_pos_of_isNonempty (A : ResolvedAdmissibleSubgraph G) (hA : A.IsNonempty)
    (hPos : A.HasPositiveInternalEdgesComponents) : 0 < A.internalEdges.card := by
  obtain ⟨γ, hγ⟩ := hA
  obtain ⟨e, he⟩ := Multiset.card_pos_iff_exists_mem.mp (hPos γ hγ)
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, A.mem_internalEdges.mpr ⟨γ, hγ, he⟩⟩

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
