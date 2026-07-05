import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRoundTrips

/-!
# R-6c-body-152 — region tags concrete: `recoverChoice` as a region-priority tag function

Hundred-and-fifty-second genuine-body step, making the region tags definitional.  The recovered choice
`recoverChoice` is defined concretely as a **region-priority tag function** — `leftResidual → inl true`,
`rightRecovered → inl false`, `forestRecovered → inr Bᵧ` — so body-146's three region tags become PROVED from the
definition (given the regions are mutually exclusive on the recovered component).

## The concrete choice (region priority)

`ResolvedRegionTagDefinitionSupply D S` fields the outer union (body-145), a forest-index map `forestTag`
(`forestRecovered` component ↦ its quotient sub-forest `Bᵧ`), and the region exclusivities (`rightRecovered` and
`forestRecovered` components lie outside `leftResidual`; `forestRecovered` outside `rightRecovered`).
`.recoverChoice` is then the priority `dite`:

```text
recoverChoice z γ = if γ ∈ leftResidual  then inl true
                    else if γ ∈ rightRecovered then inl false
                    else if h : γ ∈ forestRecovered then inr (forestTag z γ h)
                    else inl true            -- unreachable (γ ∈ union = left ∪ right ∪ forest)
```

The three tags follow by `if_pos` / `if_neg` (using the exclusivities) + `dif_pos`:

* `left_tag` — `if_pos`;
* `right_tag` — `if_neg (right ∉ left)` then `if_pos`;
* `forest_tag` — `if_neg (forest ∉ left)`, `if_neg (forest ∉ right)`, `dif_pos`, witness `⟨forestTag …, rfl⟩`.

## The supply

`.toRegionChoiceRoundTripSupply` fills body-146's `ResolvedRegionChoiceRoundTripSupply` with this concrete
`recoverChoice` and its three PROVED tags (the `forestRecovered` empty/nonempty facts are passed through).  So the
region tagging is now concrete — no longer a fielded choice; the residual region geometry is the outer union
(body-145) and the round-trips (body-147), plus the exclusivities and `forestTag` here.

Per the HALT: `recoverChoice` is made concrete (the region-priority tag function); the three tags are proved from
it; no round-trip is entered; `unionOuter` membership is untouched (the exclusivities are the only new region
facts).

Landed:

* `ResolvedRegionTagDefinitionSupply D S` — the union + `forestTag` + region exclusivities;
* `.recoverChoice` — the concrete region-priority tag function;
* `.left_tag` / `.right_tag` / `.forest_tag` — the three tags (PROVED);
* `.toRegionChoiceRoundTripSupply` — body-146's supply, tags concrete.

Toolkit body (like body-150/151).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-152 — the region tag-definition supply.**  The outer union, a forest-index map for the forest
region, and the region exclusivities — the data defining `recoverChoice` as a region-priority tag function. -/
structure ResolvedRegionTagDefinitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The three-region outer union (body-145). -/
  Union : ResolvedOuterUnionConstructionSupply D S
  /-- The quotient sub-forest `Bᵧ` of each forest-recovered component. -/
  forestTag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements}),
    γ.1 ∈ (Union.forestRecovered z).elements → (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- A right-recovered component is not left-residual. -/
  right_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements}),
    γ.1 ∈ (Union.rightRecovered z).elements → γ.1 ∉ (Union.leftResidual z).elements
  /-- A forest-recovered component is not left-residual. -/
  forest_notMem_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements}),
    γ.1 ∈ (Union.forestRecovered z).elements → γ.1 ∉ (Union.leftResidual z).elements
  /-- A forest-recovered component is not right-recovered. -/
  forest_notMem_right : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Union.unionOuter z).1.elements}),
    γ.1 ∈ (Union.forestRecovered z).elements → γ.1 ∉ (Union.rightRecovered z).elements

namespace ResolvedRegionTagDefinitionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-152 — the concrete region-priority tag function.** -/
noncomputable def recoverChoice (T : ResolvedRegionTagDefinitionSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Union.unionOuter z).1.elements})
    (hγ : γ ∈ (T.Union.unionOuter z).1.elements.attach) :
    Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  if γ.1 ∈ (T.Union.leftResidual z).elements then Sum.inl true
  else if γ.1 ∈ (T.Union.rightRecovered z).elements then Sum.inl false
  else if h : γ.1 ∈ (T.Union.forestRecovered z).elements then Sum.inr (T.forestTag z γ h)
  else Sum.inl true

/-- **R-6c-body-152 — the left tag** (`inl true`). -/
theorem left_tag (T : ResolvedRegionTagDefinitionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (T.Union.leftResidual z).elements) :
    T.recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl true := by
  rw [recoverChoice, if_pos hm]

/-- **R-6c-body-152 — the right tag** (`inl false`). -/
theorem right_tag (T : ResolvedRegionTagDefinitionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (T.Union.rightRecovered z).elements) :
    T.recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl false := by
  rw [recoverChoice, if_neg (T.right_notMem_left z γ hm), if_pos hm]

/-- **R-6c-body-152 — the forest tag** (`inr Bᵧ`). -/
theorem forest_tag (T : ResolvedRegionTagDefinitionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Union.unionOuter z).1.elements})
    (hm : γ.1 ∈ (T.Union.forestRecovered z).elements) :
    ∃ B, T.recoverChoice z γ (Finset.mem_attach _ _) = Sum.inr B := by
  rw [recoverChoice, if_neg (T.forest_notMem_left z γ hm), if_neg (T.forest_notMem_right z γ hm),
    dif_pos hm]
  exact ⟨_, rfl⟩

/-- **R-6c-body-152 — body-146's region choice supply with the concrete tags** (`forestRecovered`
empty/nonempty passed through). -/
noncomputable def toRegionChoiceRoundTripSupply (T : ResolvedRegionTagDefinitionSupply D S)
    (forestEmpty_of_mixed : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ¬ resolvedIsForestImage z.1 z.2 → (T.Union.forestRecovered z).elements = ∅)
    (forestNonempty_of_forest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      resolvedIsForestImage z.1 z.2 → (T.Union.forestRecovered z).elements.Nonempty) :
    ResolvedRegionChoiceRoundTripSupply D S where
  Union := T.Union
  recoverChoice := fun {G} z γ hγ => T.recoverChoice z γ hγ
  left_tag := fun {G} z γ hm => T.left_tag z γ hm
  right_tag := fun {G} z γ hm => T.right_tag z γ hm
  forest_tag := fun {G} z γ hm => T.forest_tag z γ hm
  forestEmpty_of_mixed := fun {G} z h => forestEmpty_of_mixed z h
  forestNonempty_of_forest := fun {G} z h => forestNonempty_of_forest z h

end ResolvedRegionTagDefinitionSupply

end GaugeGeometry.QFT.Combinatorial
