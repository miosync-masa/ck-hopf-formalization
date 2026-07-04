import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionConstruction

/-!
# R-6c-body-146 — region-wise choice tags: the branch `p`-tags from the three region tags

Hundred-and-forty-sixth genuine-body step, reducing the branch tag specs to region-local facts.  With the
recovered outer forest a three-region union (body-145), the recovered choice's tag on each component is fixed by
which region it lies in, and the branch witnesses `mixed_no_forest` (body-142) / `forest_has_inr` (body-143) are
**proved** from the three region tags plus the mixed-empty / forest-nonempty facts of `forestRecovered`.

## The region tags (fielded) and the branch witnesses (PROVED)

`ResolvedRegionChoiceRoundTripSupply D S` fields the choice function `recoverChoice` on `unionOuter`'s components
and the three region tags:

* `left_tag` — a `leftResidual` component is tagged `inl true`;
* `right_tag` — a `rightRecovered` component is tagged `inl false`;
* `forest_tag` — a `forestRecovered` component is tagged `inr Bᵧ`;

plus `forestEmpty_of_mixed` (mixed ⇒ `forestRecovered` empty) and `forestNonempty_of_forest` (forest ⇒
`forestRecovered` nonempty).  From these:

* `all_inl` (= body-142's `mixed_no_forest`): every component of a mixed `z` is `inl` — by `union_eq`, each
  component is in `leftResidual ∪ rightRecovered` (the forest region is empty), and both tag to `inl`;
* `exists_inr` (= body-143's `forest_has_inr`): a forest `z` has an `inr` component — the nonempty
  `forestRecovered` gives a component, which `forest_tag` tags `inr`.

Both use `Finset.ext_iff` on `union_eq` to case-split membership in the recovered outer (avoiding the
dependent-motive `rw` on `unionOuter`'s carrier).  So the two branch `p`-tag witnesses reduce exactly to the three
region tags — the last of the `p`-tag content is region-local.

## What remains region-local

The branch forward / backward round-trips (body-142/143) decompose the same way — `leftResidual` identity,
`componentToRight` round-trip, `componentToForest` round-trip, glued by `union_eq` — but they act on the forward
map and are fielded here as the region round-trips.  So the branch specs are no longer monolithic: they are
exactly the region tags + the region round-trips.

Per the HALT: the region tags and `forestRecovered` emptiness/nonemptiness are fielded; the two branch tag
witnesses are proved via `union_eq` case-split; the round-trips remain region-local fields.

Landed:

* `ResolvedRegionChoiceRoundTripSupply D S` — the choice + three region tags + `forestRecovered` empty/nonempty;
* `.all_inl` — body-142's `mixed_no_forest` (PROVED from the region tags);
* `.exists_inr` — body-143's `forest_has_inr` (PROVED from the region tags).

Toolkit body (like body-145).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-146 — the region choice / round-trip supply.**  The recovered choice on `unionOuter`'s components,
the three region tags, and the `forestRecovered` empty (mixed) / nonempty (forest) facts. -/
structure ResolvedRegionChoiceRoundTripSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The three-region outer union (body-145). -/
  Union : ResolvedOuterUnionConstructionSupply D S
  /-- The recovered choice on the outer forest's components. -/
  recoverChoice : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Union.unionOuter z).1.elements.attach,
      Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- A left-residual component is tagged `inl true`. -/
  left_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (Union.leftResidual z).elements),
    recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl true
  /-- A right-recovered component is tagged `inl false`. -/
  right_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (Union.rightRecovered z).elements),
    recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl false
  /-- A forest-recovered component is tagged `inr Bᵧ`. -/
  forest_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (Union.forestRecovered z).elements),
    ∃ B, recoverChoice z γ (Finset.mem_attach _ _) = Sum.inr B
  /-- Mixed ⇒ the forest region is empty. -/
  forestEmpty_of_mixed : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ¬ resolvedIsForestImage z.1 z.2 → (Union.forestRecovered z).elements = ∅
  /-- Forest ⇒ the forest region is nonempty. -/
  forestNonempty_of_forest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    resolvedIsForestImage z.1 z.2 → (Union.forestRecovered z).elements.Nonempty

namespace ResolvedRegionChoiceRoundTripSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-146 — body-142's `mixed_no_forest` from the region tags.**  In the mixed case the forest region is
empty, so every component tags `inl`. -/
theorem all_inl (R : ResolvedRegionChoiceRoundTripSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (R.Union.unionOuter z).1.elements})
    (hγ : γ ∈ (R.Union.unionOuter z).1.elements.attach) :
    ∃ b, R.recoverChoice z γ hγ = Sum.inl b := by
  have hmem : γ.1 ∈ (R.Union.leftResidual z).elements ∪ (R.Union.rightRecovered z).elements
      ∪ (R.Union.forestRecovered z).elements := (Finset.ext_iff.mp (R.Union.union_eq z) γ.1).mp γ.2
  rw [R.forestEmpty_of_mixed z h, Finset.union_empty] at hmem
  rcases Finset.mem_union.mp hmem with hl | hr
  · exact ⟨true, R.left_tag z γ hl⟩
  · exact ⟨false, R.right_tag z γ hr⟩

/-- **R-6c-body-146 — body-143's `forest_has_inr` from the region tags.**  In the forest case the forest region is
nonempty, giving a component tagged `inr`. -/
theorem exists_inr (R : ResolvedRegionChoiceRoundTripSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    ∃ γ, ∃ (hγ : γ ∈ (R.Union.unionOuter z).1.elements.attach),
      ∃ B, R.recoverChoice z γ hγ = Sum.inr B := by
  obtain ⟨δ, hδ⟩ := R.forestNonempty_of_forest z h
  have hδu : δ ∈ (R.Union.unionOuter z).1.elements :=
    (Finset.ext_iff.mp (R.Union.union_eq z) δ).mpr (Finset.mem_union.mpr (Or.inr hδ))
  obtain ⟨B, hB⟩ := R.forest_tag z ⟨δ, hδu⟩ hδ
  exact ⟨⟨δ, hδu⟩, Finset.mem_attach _ _, B, hB⟩

end ResolvedRegionChoiceRoundTripSupply

end GaugeGeometry.QFT.Combinatorial
