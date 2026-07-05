import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-156 — region construction from sector maps: `rightRecovered` / `forestRecovered` as sector images

Hundred-and-fifty-sixth genuine-body step, the region-layer boss.  Two of body-153's three regions —
`rightRecovered` and `forestRecovered` — are made concrete as `ofElements` images of the star-classified quotient
components under the sector backward maps `componentToRight` / `componentToForest`.  So the survivor / remnant
halves of the recovered outer forest are no longer arbitrary: they are exactly the sector-map images.

## The star split of the quotient `B`

For a codomain pair `z = (A, B)` (`A = z.1`, `B = z.2` a forest over `A.1.contractWithStars`), the components of
`B` split by the outer star `starOfZ z := z.1.1.starVertices (starOf G z.1.1)`:

* `rightDomain z` — the star-AVOIDING (survivor) components: `B`'s elements `δ` with `Disjoint δ.vertices
  (starOfZ z)`;
* `forestDomain z` — the star-TOUCHING (remnant) components: `¬ Disjoint …`.

## The two regions (concrete `ofElements` images)

`ResolvedRegionConstructionFromSectorSupply D S` fields the two sector backward maps and their `CD` /
disjointness:

* `componentToRight z : {δ ∈ rightDomain z} → ResolvedFeynmanSubgraph G` — a survivor component pulled back to its
  source outer component (`right_surj` of the sector machinery);
* `componentToForest z : {δ ∈ forestDomain z} → ResolvedFeynmanSubgraph G` — a remnant component pulled back to its
  forest-choice parent (`forest_surj` / `ForestPrimitiveIndex.toOccurrence`);

with `rightComponentCD` / `rightComponentDisjoint` (and the forest analogues) for the `ofElements` well-formedness.
Then

```text
rightRecovered  z = ofElements ((rightDomain z).attach.image  (componentToRight  z)) …
forestRecovered z = ofElements ((forestDomain z).attach.image (componentToForest z)) …
```

and `rightRecovered_elements_eq` / `forestRecovered_elements_eq` hold by `rfl` (`ofElements_elements`).  This is
the backward mirror of the forward survivor forest (body-125, `rightSurvivorForest = ofElements (rightComponents
.attach.image survivorComponent)`).

## What remains

The two sector maps and their `CD` / disjointness are the genuine sector geometry, fielded here (the sector
`componentToRight` / `componentToForest` inputs).  Body-153's third region `leftResidual` (the "not represented in
`B`" filter of `A`), the cross-disjointnesses, and the carrier membership are not built here — they are the
remaining outer-reassembly geometry.

Per the HALT: no round-trip is entered; `leftResidual` is not built; the sector maps `componentToRight` /
`componentToForest` are accepted as fielded inputs; the element-shape equations of `rightRecovered` /
`forestRecovered` are established (`rfl`).

Landed:

* `starOfZ` / `rightDomain` / `forestDomain` — the outer star and the star-split of `B`;
* `ResolvedRegionConstructionFromSectorSupply D S` — the two sector maps + `CD` / disjointness;
* `.rightRecovered` / `.forestRecovered` — the concrete `ofElements` images;
* `.rightRecovered_elements_eq` / `.forestRecovered_elements_eq` — the element-shape equations (`rfl`).

Toolkit body (like body-125, the forward mirror).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-156 — the outer star of a codomain pair** `z = (A, B)`. -/
noncomputable def starOfZ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : Finset VertexId :=
  z.1.1.starVertices (D.starOf G z.1.1)

/-- **R-6c-body-156 — the star-avoiding (survivor) components of `B`.** -/
noncomputable def rightDomain {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    Finset (ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :=
  z.2.1.elements.filter (fun δ => Disjoint δ.vertices (starOfZ z))

/-- **R-6c-body-156 — the star-touching (remnant) components of `B`.** -/
noncomputable def forestDomain {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    Finset (ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :=
  z.2.1.elements.filter (fun δ => ¬ Disjoint δ.vertices (starOfZ z))

/-- **R-6c-body-156 — the sector region-construction supply.**  The two sector backward maps
(`componentToRight` / `componentToForest`) pulling the star-classified quotient components back to source outer
components, with their `CD` / disjointness. -/
structure ResolvedRegionConstructionFromSectorSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- A survivor component pulled back to its source outer component. -/
  componentToRight : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x // x ∈ rightDomain z} → ResolvedFeynmanSubgraph G
  /-- Each recovered right component is connected-divergent. -/
  rightComponentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ rightDomain z}), (componentToRight z δ).forget.IsConnectedDivergent
  /-- The recovered right components are pairwise disjoint. -/
  rightComponentDisjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ ⦃γ⦄, γ ∈ (rightDomain z).attach.image (componentToRight z) →
    ∀ ⦃δ⦄, δ ∈ (rightDomain z).attach.image (componentToRight z) → γ ≠ δ → γ.Disjoint δ
  /-- A remnant component pulled back to its forest-choice parent. -/
  componentToForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G
  /-- Each recovered forest parent is connected-divergent. -/
  forestComponentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ forestDomain z}), (componentToForest z δ).forget.IsConnectedDivergent
  /-- The recovered forest parents are pairwise disjoint. -/
  forestComponentDisjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ ⦃γ⦄, γ ∈ (forestDomain z).attach.image (componentToForest z) →
    ∀ ⦃δ⦄, δ ∈ (forestDomain z).attach.image (componentToForest z) → γ ≠ δ → γ.Disjoint δ

namespace ResolvedRegionConstructionFromSectorSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-156 — the recovered right region** (`componentToRight` image of the survivor components). -/
noncomputable def rightRecovered (T : ResolvedRegionConstructionFromSectorSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements ((rightDomain z).attach.image (T.componentToRight z))
    (by intro δ hδ; obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ; exact T.rightComponentCD z γ)
    (T.rightComponentDisjoint z)

/-- **R-6c-body-156 — the recovered forest region** (`componentToForest` image of the remnant components). -/
noncomputable def forestRecovered (T : ResolvedRegionConstructionFromSectorSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements ((forestDomain z).attach.image (T.componentToForest z))
    (by intro δ hδ; obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ; exact T.forestComponentCD z γ)
    (T.forestComponentDisjoint z)

/-- **R-6c-body-156 — the right region's element shape** (`rfl`). -/
@[simp] theorem rightRecovered_elements_eq (T : ResolvedRegionConstructionFromSectorSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (T.rightRecovered z).elements = (rightDomain z).attach.image (T.componentToRight z) :=
  rfl

/-- **R-6c-body-156 — the forest region's element shape** (`rfl`). -/
@[simp] theorem forestRecovered_elements_eq (T : ResolvedRegionConstructionFromSectorSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (T.forestRecovered z).elements = (forestDomain z).attach.image (T.componentToForest z) :=
  rfl

end ResolvedRegionConstructionFromSectorSupply

end GaugeGeometry.QFT.Combinatorial
