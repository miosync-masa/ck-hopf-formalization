import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTargetOuterCoverage

/-!
# R-6c-body-179 — forest recovery geometry: the shared provider behind `forestRecovered_mem` and `promoted_region_eq`

Hundred-and-seventy-ninth genuine-body step, a design consolidation.  Two residual forward-outer leaves — body-177's
`forestRecovered_mem` (the coverage view) and body-175's `promoted_region_eq` (the selected-outer view) — are two
faces of **the same** `componentToForest` de-contraction round-trip.  Rather than attack them separately, this body
bundles them into one shared geometry provider, so the whole forest-recovery obstruction is a single box.

## The one round-trip, two views

For a codomain pair `z = (A, B)`, the star-**touching** remnant components of the quotient `B` are pulled back to
their forest-choice **parent** components of `A` by the sector map `componentToForest` (body-156).  That same
de-contraction underlies both leaves:

* **coverage view** (`forestRecovered_mem`) — a component `γ` of `A` lies in `forestRecovered` iff it *is* such a
  remnant parent (`representedByForest z γ`); this is the `A`-side classification used by the coverage partition
  (body-177);
* **selected-outer view** (`promoted_region_eq`) — the promoted forest of the recovered choice
  (`promotedOf recovered`, the de-contracted `inr Bᵧ` choices) has exactly the `forestRecovered` components; this is
  the forward-outer equality used by the region partition (bodies 175/174/167).

Both say: *the `componentToForest` parents of `B`'s remnants = the promoted/de-contracted forest choices*.  Isolating
them together means the forest-recovery geometry is proved once and reused twice.

## The provider

`ResolvedForestRecoveryGeometrySupply D S Region` fields the remnant-parent predicate `representedByForest` and the
two views:

* `forestRecovered_mem : γ ∈ forestRecovered z ↔ γ ∈ A ∧ representedByForest z γ`;
* `promoted_region_eq : (promotedOf recovered).elements = forestRecovered z .elements`.

`.toPromotedRegionRoundTripSupply` re-exports the selected-outer view as body-175's supply; the coverage view
(`forestRecovered_mem` + `representedByForest`) is exposed for the eventual body-177 coverage assembly (which still
needs `coverage`).  So the two leaves now provably share one source.

## Consequence

The forward-outer residual compresses to **one forest-recovery geometry box** (this provider) plus **`coverage`**
(body-177).  Once `coverage` is opened, the outer round-trip is: `leftOf` (body-174, tags), `leftResidual_mem`
(body-178, filter), the forest-recovery geometry (this body), and the star-touch/remnant coverage classification.

Per the HALT: the actual `componentToForest` inverse / de-contraction proof is not entered; `coverage` is not
touched; this body is the shared-provider design and its wiring only.

Landed:

* `ResolvedForestRecoveryGeometrySupply D S Region` — the remnant-parent predicate + the two views;
* `.toPromotedRegionRoundTripSupply` — body-175's supply from the selected-outer view.

Toolkit body (like body-175).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-179 — the forest-recovery geometry supply.**  The single `componentToForest` de-contraction
round-trip, in its two faces: the coverage-view membership `forestRecovered_mem` and the selected-outer-view
equality `promoted_region_eq`, sharing the remnant-parent predicate `representedByForest`. -/
structure ResolvedForestRecoveryGeometrySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- `γ` is recovered from a remnant / forest-choice parent of `B` (the `componentToForest` image). -/
  representedByForest : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop
  /-- Coverage view: the forest region is the remnant-parent filter of `A`. -/
  forestRecovered_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.forestRecovered z).elements ↔ γ ∈ z.1.1.elements ∧ representedByForest z γ
  /-- Selected-outer view: the promoted (de-contracted) forest is the forest-recovered region. -/
  promoted_region_eq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements

namespace ResolvedForestRecoveryGeometrySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-179 — body-175's promotion supply from the selected-outer view.** -/
def toPromotedRegionRoundTripSupply (F : ResolvedForestRecoveryGeometrySupply D S Region) :
    ResolvedPromotedRegionRoundTripSupply D S Region where
  promoted_region_eq := fun {G} z => F.promoted_region_eq z

end ResolvedForestRecoveryGeometrySupply

end GaugeGeometry.QFT.Combinatorial
