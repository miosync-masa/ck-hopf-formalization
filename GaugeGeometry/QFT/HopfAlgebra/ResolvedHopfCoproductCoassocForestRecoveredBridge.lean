import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionRegionsConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualConstruction

/-!
# R-6c-body-184 — forest recovered bridge: the union built from the concrete region constructions

Hundred-and-eighty-fourth genuine-body step, discharging body-183's `forestRecovered_eq` wiring bridge (and, for
free, body-178's `leftResidual_eq`) by **building** the outer union from the concrete region constructions.

Body-183's `forestRecovered_eq` — `(Region.Union.forestRecovered z).elements = (Construction.forestRecovered
z).elements` — is not provable for an *abstract* `Region.Union` (a `ResolvedOuterUnionConstructionSupply` field with
no shape).  But it is `rfl` the moment the union's `forestRecovered` field is *set* to body-156's construction.  So
rather than field the bridge, this body assembles body-153's concrete region supply from the concrete pieces —
`rightRecovered` / `forestRecovered` from body-156's `componentToForest` / `componentToRight` construction,
`leftResidual` from body-157's filter — and reads the two bridges off as `rfl`.

## The concrete union (regions from the constructions)

`ResolvedConcreteRegionUnionSupply D S` fields body-156's sector region construction (`Forest`), body-157's
left-residual construction (`Left`), and the union well-formedness that is genuinely geometric (the two
cross-disjointnesses and the carrier membership — the same fields body-153 already isolated).
`.toOuterUnionRegionsConcreteSupply` plugs

```text
leftResidual    := Left.leftResidual          (body-157, the "not represented" filter)
rightRecovered  := Forest.rightRecovered      (body-156, componentToRight survivors)
forestRecovered := Forest.forestRecovered     (body-156, componentToForest remnant parents)
```

into body-153's supply, and `.toOuterUnionConstructionSupply` runs body-153 out to body-145's
`ResolvedOuterUnionConstructionSupply` (with `union_eq` proved there).

## The bridges, read off as `rfl`

Because `toOuterUnionConstructionSupply.forestRecovered` is *definitionally* the plugged field, both wiring bridges
are `rfl`:

* `forestRecovered_eq` — `(toOuterUnionConstructionSupply.forestRecovered z).elements = (Forest.forestRecovered
  z).elements` (body-183's bridge);
* `leftResidual_eq` — `(toOuterUnionConstructionSupply.leftResidual z).elements = (Left.leftResidual z).elements`
  (body-178's bridge).

So the abstract-union ↔ concrete-construction gap is closed by construction, not fielded: any decomposition
(bodies 178/183) whose `Region.Union` is this built union gets its wiring bridge for free.

## Consequence

Body-183's forest-recovery box loses its first leaf: `forestRecovered_eq` is `rfl` for the built union, leaving
`parent_mem_carrier` (shallow) and `promoted_eq_forestRecovered` (the deep de-contraction round-trip).  And
body-178's `leftResidual_eq` is discharged the same way.  The remaining outer-union geometry is exactly what
body-153 always isolated: the two cross-disjointnesses and the carrier membership.

Per the HALT: the `componentToForest` inverse / `parent_mem_carrier` / `promoted_eq_forestRecovered` are not
entered; only the union is built from the constructions and the two bridges read off (`rfl`).

Landed:

* `ResolvedConcreteRegionUnionSupply D S` — the concrete region constructions + union well-formedness;
* `.toOuterUnionRegionsConcreteSupply` / `.toOuterUnionConstructionSupply` — body-153 / body-145 supplies;
* `.forestRecovered_eq` / `.leftResidual_eq` — body-183 / body-178 wiring bridges (PROVED `rfl`).

Toolkit body (like body-153).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-184 — the concrete region-union supply.**  The three regions taken from body-156's sector
construction (`rightRecovered` / `forestRecovered`) and body-157's left-residual filter (`leftResidual`), plus the
genuinely geometric union well-formedness (cross-disjointnesses + carrier membership). -/
structure ResolvedConcreteRegionUnionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- Body-156's sector region construction (`componentToRight` / `componentToForest` images). -/
  Forest : ResolvedRegionConstructionFromSectorSupply D S
  /-- Body-157's left-residual construction (the "not represented in `B`" filter). -/
  Left : ResolvedLeftResidualConstructionSupply D S
  /-- Left / right cross-disjointness. -/
  hcross_lr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (Left.leftResidual z).elements, ∀ δ ∈ (Forest.rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- (Left ∪ right) / forest cross-disjointness. -/
  hcross_lrf : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ ((Left.leftResidual z).union (Forest.rightRecovered z) (hcross_lr z)).elements,
    ∀ δ ∈ (Forest.forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- The assembled outer forest is a carrier forest. -/
  recoveredOuter_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((Left.leftResidual z).union (Forest.rightRecovered z) (hcross_lr z)).union
        (Forest.forestRecovered z) (hcross_lrf z)
      ∈ D.carrier G

namespace ResolvedConcreteRegionUnionSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-184 — body-153's concrete region supply from the constructions.** -/
noncomputable def toOuterUnionRegionsConcreteSupply (U : ResolvedConcreteRegionUnionSupply D S) :
    ResolvedOuterUnionRegionsConcreteSupply D S where
  leftResidual := fun {G} z => U.Left.leftResidual z
  rightRecovered := fun {G} z => U.Forest.rightRecovered z
  forestRecovered := fun {G} z => U.Forest.forestRecovered z
  hcross_lr := fun {G} z => U.hcross_lr z
  hcross_lrf := fun {G} z => U.hcross_lrf z
  recoveredOuter_mem := fun {G} z => U.recoveredOuter_mem z

/-- **R-6c-body-184 — body-145's outer-union supply from the constructions.** -/
noncomputable def toOuterUnionConstructionSupply (U : ResolvedConcreteRegionUnionSupply D S) :
    ResolvedOuterUnionConstructionSupply D S :=
  U.toOuterUnionRegionsConcreteSupply.toOuterUnionConstructionSupply

/-- **R-6c-body-184 — body-183's `forestRecovered_eq` bridge, read off as `rfl`.** -/
theorem forestRecovered_eq (U : ResolvedConcreteRegionUnionSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (U.toOuterUnionConstructionSupply.forestRecovered z).elements
      = (U.Forest.forestRecovered z).elements :=
  rfl

/-- **R-6c-body-184 — body-178's `leftResidual_eq` bridge, read off as `rfl`.** -/
theorem leftResidual_eq (U : ResolvedConcreteRegionUnionSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (U.toOuterUnionConstructionSupply.leftResidual z).elements
      = (U.Left.leftResidual z).elements :=
  rfl

end ResolvedConcreteRegionUnionSupply

end GaugeGeometry.QFT.Combinatorial
