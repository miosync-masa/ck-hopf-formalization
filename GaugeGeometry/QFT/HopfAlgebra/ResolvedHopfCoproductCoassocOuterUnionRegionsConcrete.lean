import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterUnionConstruction

/-!
# R-6c-body-153 — outer union region construction: the recovered outer as a concrete three-region union

Hundred-and-fifty-third genuine-body step, assembling the recovered outer forest.  Body-145's `unionOuter` and
`union_eq` are made concrete: `unionOuter` is the literal admissible-forest union `(leftResidual ∪ rightRecovered)
∪ forestRecovered`, and `union_eq` is **proved** (`Finset.ext` + `union_elements`).  The three regions are
identified by their sources — the sector backward maps and the left residual — and the residual outer-reassembly
geometry (the region contents, the cross-disjointnesses, and the carrier membership) is isolated as fielded data.

## The three regions (sources named)

`ResolvedOuterUnionRegionsConcreteSupply D S` fields the three region forests with their intended sources:

* `rightRecovered z` — `B`'s star-AVOIDING (survivor) components pulled back to their source components via the
  sector backward map `componentToRight` (`right_surj`);
* `forestRecovered z` — `B`'s star-TOUCHING (remnant) components pulled back to their parent components via
  `componentToForest` (`forest_surj`) / `ForestPrimitiveIndex.toOccurrence`;
* `leftResidual z` — the components of the target outer `A` not represented by the quotient `B` (the "not
  represented in `B`" filter) — the genuinely new left-reassembly obstruction, fielded and named here.

plus the two cross-disjointnesses (`hcross_lr`, `hcross_lrf`) for the admissible-forest union, and the carrier
membership `recoveredOuter_mem` of the assembled outer forest.

## The assembly (PROVED `union_eq`)

`.unionOuter z = ⟨(leftResidual.union rightRecovered) .union forestRecovered, recoveredOuter_mem⟩` and
`.toOuterUnionConstructionSupply` builds body-145's `ResolvedOuterUnionConstructionSupply` with `union_eq` proved
by `Finset.ext` + `union_elements` (absorbing the `Finset` `DecidableEq` instance diamond).  So the recovered outer
is now a concrete union; the residual region geometry is exactly the region contents (the sector-map images and the
left residual), the cross-disjointnesses, and the carrier membership.

Per the HALT: no inverse law is entered; `rightRecovered` / `forestRecovered` are named as the sector-backward-map
images and `leftResidual` as the "not represented in `B`" residual; the region contents / carrier membership are
fielded; `union_eq` is proved from the union assembly.

Landed:

* `ResolvedOuterUnionRegionsConcreteSupply D S` — the three region forests + cross-disjointnesses + carrier
  membership;
* `.unionOuter` — the concrete `(leftResidual ∪ rightRecovered) ∪ forestRecovered`;
* `.toOuterUnionConstructionSupply` — body-145's supply with `union_eq` PROVED.

Toolkit body (like body-152).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-153 — the concrete outer-union region supply.**  The three region forests (`leftResidual`, the
survivor-recovered `rightRecovered`, the remnant-recovered `forestRecovered`), their cross-disjointnesses, and the
carrier membership of the assembled outer forest. -/
structure ResolvedOuterUnionRegionsConcreteSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The left-primitive region (target outer `A` components not represented by `B`). -/
  leftResidual : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The right-primitive region (`B`'s survivors via `componentToRight`). -/
  rightRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- The forest-choice region (`B`'s remnants via `componentToForest`). -/
  forestRecovered : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G
  /-- Left / right cross-disjointness. -/
  hcross_lr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- (Left ∪ right) / forest cross-disjointness. -/
  hcross_lrf : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ γ ∈ ((leftResidual z).union (rightRecovered z) (hcross_lr z)).elements,
    ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ
  /-- The assembled outer forest is a carrier forest. -/
  recoveredOuter_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((leftResidual z).union (rightRecovered z) (hcross_lr z)).union (forestRecovered z) (hcross_lrf z)
      ∈ D.carrier G

namespace ResolvedOuterUnionRegionsConcreteSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-153 — the concrete recovered outer forest** `(leftResidual ∪ rightRecovered) ∪ forestRecovered`. -/
noncomputable def unionOuter (U : ResolvedOuterUnionRegionsConcreteSupply D S)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  ⟨((U.leftResidual z).union (U.rightRecovered z) (U.hcross_lr z)).union (U.forestRecovered z)
      (U.hcross_lrf z), U.recoveredOuter_mem z⟩

/-- **R-6c-body-153 — body-145's outer-union supply with `union_eq` PROVED.** -/
noncomputable def toOuterUnionConstructionSupply (U : ResolvedOuterUnionRegionsConcreteSupply D S) :
    ResolvedOuterUnionConstructionSupply D S where
  leftResidual := fun {G} z => U.leftResidual z
  rightRecovered := fun {G} z => U.rightRecovered z
  forestRecovered := fun {G} z => U.forestRecovered z
  unionOuter := fun {G} z => U.unionOuter z
  union_eq := fun {G} z => by
    show (((U.leftResidual z).union (U.rightRecovered z) (U.hcross_lr z)).union (U.forestRecovered z)
      (U.hcross_lrf z)).elements = _
    ext δ
    simp [ResolvedAdmissibleSubgraph.union_elements]

end ResolvedOuterUnionRegionsConcreteSupply

end GaugeGeometry.QFT.Combinatorial
