import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitMixed
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitForest

/-!
# R-6c-body-145 — outer-union construction: `mixedOuter` / `forestOuter` as a three-region union

Hundred-and-forty-fifth genuine-body step, the core of the last geometry.  The recovered outer forests
`mixedOuter` (body-142) and `forestOuter` (body-143) are given their concrete shape as a **three-region union**

```text
A' = leftResidual(A, B) ∪ rightRecovered(B) ∪ forestRecovered(B)
```

so both branch outers are no longer opaque, and their branch round-trip specs decompose region-by-region.

## The three regions (sources named)

For a codomain pair `z = (A, B)`:

* `leftResidual z` — the LEFT-PRIMITIVE pieces: the components of `A` not represented by the quotient `B` (the
  left residual of `A`); source of the `inl true` tags;
* `rightRecovered z` — the RIGHT-PRIMITIVE pieces: `B`'s star-AVOIDING (survivor) components pulled back to their
  source components via the sector `componentToRight` (`right_surj`); source of the `inl false` tags;
* `forestRecovered z` — the FOREST-CHOICE parents: `B`'s star-TOUCHING (remnant) components pulled back to their
  parent components via `componentToForest` (`forest_surj`) / `ForestPrimitiveIndex.toOccurrence`; source of the
  `inr Bᵧ` tags.

`unionOuter z` is the assembled carrier forest and `union_eq` states its elements are the union of the three
regions' elements.  In the **mixed** case (`B` avoids the star) `forestRecovered z` is empty (all of `B`'s
components are survivors), so `mixedOuter = unionOuter` with no forest region; in the **forest** case
`forestRecovered z` is nonempty (the `inr` witness), and `forestOuter = unionOuter`.

## The reduction

With this, the branch forward/backward round-trips (body-142/143) decompose region-by-region:

* the `leftResidual` region round-trips by the left-residual identity;
* the `rightRecovered` region by the sector `componentToRight` round-trip (`right_left_inv` / `right_right_inv`);
* the `forestRecovered` region by the sector `componentToForest` round-trip (`forest_left_inv` /
  `forest_right_inv`);

glued by `union_eq` (`Finset`-union extensionality).  So `mixed_forward` / `forest_forward` and their backward
partners reduce to the three region-local round-trips plus union extensionality — the last genuine geometry.

Per the HALT: the three regions and `unionOuter` are fielded (their construction from the sector maps + carrier
membership is the geometry); `union_eq` is at the `elements` level; no round-trip is proved; the region sources
(`componentToRight` / `componentToForest` / left residual) are named.  `.toMixedOuter` / `.toForestOuter` supply
body-142/143's outer fields as `unionOuter`.

Landed:

* `ResolvedOuterUnionConstructionSupply D S` — the three regions + `unionOuter` + `union_eq`;
* `.toMixedOuter` / `.toForestOuter` — body-142/143's recovered outer forests (`= unionOuter`).

Toolkit body (scout, like body-135).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-145 — the outer-union construction supply.**  The recovered outer forest `A'` as the union of
three regions — the left residual of `A`, the survivors of `B` (via `componentToRight`), and the forest-choice
parents of `B` (via `componentToForest`) — assembled into a carrier forest `unionOuter`. -/
structure ResolvedOuterUnionConstructionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The left-primitive region (left residual of `A`). -/
  leftResidual : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The right-primitive region (`B`'s survivors via `componentToRight`). -/
  rightRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The forest-choice region (`B`'s remnant parents via `componentToForest`). -/
  forestRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The assembled outer forest (a carrier forest). -/
  unionOuter : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G}
  /-- The outer forest's elements are the union of the three regions' elements. -/
  union_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (unionOuter z).1.elements
      = (leftResidual z).elements ∪ (rightRecovered z).elements ∪ (forestRecovered z).elements

namespace ResolvedOuterUnionConstructionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-145 — body-142's recovered mixed outer forest** (`= unionOuter`; the forest region is empty). -/
def toMixedOuter (U : ResolvedOuterUnionConstructionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : ¬ resolvedIsForestImage z.1 z.2) :
    {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  U.unionOuter z

/-- **R-6c-body-145 — body-143's recovered forest outer forest** (`= unionOuter`; the forest region is nonempty). -/
def toForestOuter (U : ResolvedOuterUnionConstructionSupply D S) {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType D G) (h : resolvedIsForestImage z.1 z.2) :
    {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  U.unionOuter z

end ResolvedOuterUnionConstructionSupply

end GaugeGeometry.QFT.Combinatorial
