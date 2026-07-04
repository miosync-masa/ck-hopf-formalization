import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingInvConstruct

/-!
# R-6c-body-135 — grounding the reassembly: `recoverOuter` / `recoverChoice` as three tagged regions

Hundred-and-thirty-fifth genuine-body step, grounding body-134's reassembly skeleton.  The two reconstruction
fields `recoverOuter` / `recoverChoice` are no longer arbitrary: the recovered outer forest `A'` is partitioned
into THREE regions, each sourced from a definite piece of the codomain pair `(A, B)` and carrying a definite
choice tag.  This turns the opaque backward map into a tagged three-region reassembly, so the inverse-law
round-trips decompose region-by-region.

## The three regions (structure fielded; sector source named)

For the recovered `A' = recoverOuter z` from `z = (A, B)`:

* `leftRegion z` — the LEFT-PRIMITIVE components: the `leftOf` pieces of `A` not arising from `B`; tagged
  `inl true` (`choice_left`).  Source: the left residual of `A` (the components of `A` untouched by the quotient).
* `rightRegion z` — the RIGHT-PRIMITIVE components: recovered from `B`'s star-AVOIDING (right-survivor)
  components via the sector backward map `componentToRight` (`right_surj`); tagged `inl false` (`choice_right`).
* `forestRegion z` — the FOREST-CHOICE parents: recovered from `B`'s star-TOUCHING (remnant) components via
  `componentToForest` (`forest_surj`); tagged `inr Bᵧ` (`choice_forest`).

`region_cover`: the three regions cover all of `A'`'s components (`elements.attach = leftRegion ∪ rightRegion ∪
forestRegion`).  The three `choice_*` specs pin `recoverChoice` on each region.  So the whole reassembly is
determined by the three regions plus the tag specs — the sector-map content is exactly the construction of
`rightRegion` / `forestRegion` from `componentToRight` / `componentToForest`, isolated here as fielded data.

## Consequence for the inverse laws

With this grounding, the two round-trips (body-134) decompose region-by-region:

* `forward ∘ reassembly = id` (`right_inv`): on the `rightRegion` it is the sector `componentToRight` right-inverse
  (`right_right_inv`), on the `forestRegion` the `componentToForest` right-inverse (`forest_right_inv`), on the
  `leftRegion` the left-residual identity;
* `reassembly ∘ forward = id` (`left_inv`): the source split choice's components are re-tagged into the three
  regions by their original `p`-value (`inl true` / `inl false` / `inr`), and each region round-trips by the
  matching sector `left_inv` plus the left-residual identity.

Per the HALT: the inverse laws are NOT proved; the union construction is kept as `region_cover` + the `choice_*`
specs; the sector component maps are connected to the three regions by fielded data (`rightRegion` /
`forestRegion` are the images of `componentToRight` / `componentToForest`, named above).

Landed:

* `ResolvedReassemblyFromSectorSupply D` — `recoverOuter` / `recoverChoice` with the three tagged regions and the
  cover + tag specs;
* `.toReassemblyData` — into body-134's `ResolvedOuterMixingReassemblyData`.

Toolkit body (like body-134), one grounding supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-135 — the reassembly grounded in three tagged regions.**  The recovered outer forest `A'` is
partitioned into a left-primitive region (from `A`'s left residual, tagged `inl true`), a right-primitive region
(from `B`'s star-avoiding survivors via `componentToRight`, tagged `inl false`), and a forest-choice region (from
`B`'s star-touching remnants via `componentToForest`, tagged `inr Bᵧ`). -/
structure ResolvedReassemblyFromSectorSupply (D : ResolvedCoproductProperForestData) where
  /-- The recovered original outer forest `A'`. -/
  recoverOuter : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G}
  /-- The recovered component choice `p` on `A'`. -/
  recoverChoice : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (recoverOuter z).1.elements.attach,
      Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx
  /-- The left-primitive region (from `A`'s left residual). -/
  leftRegion : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}
  /-- The right-primitive region (from `B`'s survivors via `componentToRight`). -/
  rightRegion : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}
  /-- The forest-choice region (from `B`'s remnants via `componentToForest`). -/
  forestRegion : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}
  /-- The three regions cover all of `A'`'s components. -/
  region_cover : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (recoverOuter z).1.elements.attach = leftRegion z ∪ rightRegion z ∪ forestRegion z
  /-- The left region is tagged `inl true` (left-primitive). -/
  choice_left : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}) (h : γ ∈ leftRegion z),
    recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl true
  /-- The right region is tagged `inl false` (right-primitive). -/
  choice_right : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}) (h : γ ∈ rightRegion z),
    recoverChoice z γ (Finset.mem_attach _ _) = Sum.inl false
  /-- The forest region is tagged `inr Bᵧ` (forest-choice). -/
  choice_forest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (recoverOuter z).1.elements}) (h : γ ∈ forestRegion z),
    ∃ B, recoverChoice z γ (Finset.mem_attach _ _) = Sum.inr B

/-- **R-6c-body-135 — body-134's reassembly data from the grounded supply.**  The `recoverOuter` / `recoverChoice`
of the three-region supply. -/
def ResolvedReassemblyFromSectorSupply.toReassemblyData (R : ResolvedReassemblyFromSectorSupply D) :
    ResolvedOuterMixingReassemblyData D where
  recoverOuter := R.recoverOuter
  recoverChoice := R.recoverChoice

end GaugeGeometry.QFT.Combinatorial
