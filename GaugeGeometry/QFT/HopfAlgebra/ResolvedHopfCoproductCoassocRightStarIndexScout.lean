import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentPartition

/-!
# R-6c-heart-6a-8c-0 — `indexEquiv` left-case sanity check (🔴 GRANULARITY MISMATCH FOUND)

Before constructing `OneStageStarIndex ≃ TwoStageStarIndex`, this checks whether every one-stage star has
a two-stage *star* image.  **It does NOT.**

The 5b-1 `componentPartition` docstring states the classification of an input-outer component `γ` of
`A = s.1.1` by `s.choiceAt γ`:

* `Sum.inl true`  — **left primitive**: selected-outer side, **NOT quotient**;
* `Sum.inl false` — **right primitive**: quotient **right-survivor**;
* `Sum.inr B`     — **forest choice**: selected-outer promoted piece **and** quotient **remnant** piece.

Geometric consequence for the contract-twice picture (`A = γ ⊇ selectedOuter = δ`,
`quotientForest = γ/δ`):

* a **right** component's star (one-stage) ↔ a **RightSurvivor** quotient-forest star (two-stage) ✓;
* a **forest** component's star (one-stage) ↔ a **Remnant** quotient-forest star (two-stage) ✓;
* a **left** component is fully inside `selectedOuter = δ`; in `quotientForest = γ/δ` it collapses to a
  single point with no internal edges — **it is NOT a quotient-forest component**.  So its one-stage star
  becomes, in the two-stage graph, a **surviving vertex** (the surviving `δ`-star of `G/δ`), **NOT a
  two-stage star**.

## 🔴 FINDING — `OneStageStarIndex ≃ TwoStageStarIndex` is FALSE as typed

`OneStageStarIndex` ranges over **all** components of `s.1.1` (left + right + forest); the two-stage star
set ranges over **quotientForest = Right ⊔ Remnant** (right + forest only).  The **left** primitives have
**no two-stage-star codomain** — they cross to two-stage *survivors*.  So:

```
|OneStageStarIndex|  =  |left| + |right| + |forest|
|TwoStageStarIndex|  =          |right| + |forest|   (= |Right ⊔ Remnant|)
```

The correspondence source must be the **right + forest** sub-index, NOT all of `OneStageStarIndex`.

## Knock-on consequences (to revisit upstream)

* **6a-8b-1 `indexEquiv` type** must change: source = `{i : OneStageStarIndex // i.hasQuotientStar}`
  (right ∨ forest), codomain `TwoStageStarIndex`.
* **6a-5c-2b `ResolvedContractStarMapSupply`** (`starToStar : {one-stage star} → {two-stage star}`, total)
  is **uninhabitable when left primitives exist** — left one-stage stars have no two-stage-star image.  The
  vertex correspondence must route **left stars to two-stage survivors** (identity on the shared `δ`-star
  VertexId), so the "star↔star + surviving↔surviving" split needs a third route.
* **6a-7b `quotientForest` surviving connectors** — connector (3)
  `selectedOuter_starVertices_subset_quotientForest` is **FALSE**: the **left** `δ`-stars are NOT in
  `quotientForest` (they survive stage 2).  Only the right/forest `δ`-stars are re-contracted.

Per the HALT, NO `Equiv`, NO `starToStar`, NO pushing left into the codomain.  This is the sanity stop: the
star correspondence is finer-grained than "all `A` components ↔ all quotient components".

Landed (classification only):

* `OneStageStarIndex.toComponent` / `isLeft` / `isRight` / `isForest` — the one-stage classification;
* `OneStageStarIndex.hasQuotientStar` — `isRight ∨ isForest` (the corrected `indexEquiv` source predicate).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {s : ResolvedCoassocSplitChoice D G}

/-- **R-6c-heart-6a-8c-0 — the one-stage star index as a split-choice component. -/
def OneStageStarIndex.toComponent (i : OneStageStarIndex D G s) :
    {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} := ⟨i.η, i.hη⟩

/-- **R-6c-heart-6a-8c-0 — a left-primitive one-stage star (no quotient image). -/
def OneStageStarIndex.isLeft (i : OneStageStarIndex D G s) : Prop :=
  s.isLeftPrimitive i.toComponent

/-- **R-6c-heart-6a-8c-0 — a right-primitive one-stage star (↦ quotient RightSurvivor). -/
def OneStageStarIndex.isRight (i : OneStageStarIndex D G s) : Prop :=
  s.isRightPrimitive i.toComponent

/-- **R-6c-heart-6a-8c-0 — a forest-choice one-stage star (↦ quotient Remnant). -/
def OneStageStarIndex.isForest (i : OneStageStarIndex D G s) : Prop :=
  s.isForestChoice i.toComponent

/-- **R-6c-heart-6a-8c-0 — the corrected `indexEquiv` source predicate.**  A one-stage star has a
two-stage *star* image iff its component is right-primitive or forest-choice (NOT left-primitive). -/
def OneStageStarIndex.hasQuotientStar (i : OneStageStarIndex D G s) : Prop :=
  i.isRight ∨ i.isForest

/-- **R-6c-heart-6a-8c-0 — exhaustiveness: every one-stage star is left, right, or forest.**  (Left has no
two-stage-star image; right/forest do.) -/
theorem OneStageStarIndex.isLeft_or_hasQuotientStar (i : OneStageStarIndex D G s) :
    i.isLeft ∨ i.hasQuotientStar :=
  s.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice i.toComponent

end GaugeGeometry.QFT.Combinatorial
