import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRegionRoundTrip

/-!
# R-6c-body-177 — target outer coverage: `leftResidual ∪ forestRecovered = A` as a represented-classification

Hundred-and-seventy-seventh genuine-body step, carving body-174's second forward-outer leaf
(`target_outer_partition`) into a **coverage classification**.  Where body-175 isolated the promotion leaf, this
body isolates the coverage leaf and reduces it — by pure logic, the coverage twin of body-173's trichotomy — to
three represented-classification facts.  So the two forward-outer residuals are now completely separated: one is a
de-contraction *equality* (`promoted_region_eq`), the other a coverage *classification* (`target_outer_coverage`).

## Why `rightRecovered` is absent from the target

The target outer `A = z.1.1` is the *forward selected outer* — the left factor of the coproduct.  Its components
are the ones that stayed outside the quotient `B`:

* `leftResidual` — the `A`-components **not represented** in the quotient `B` (the left-primitive pieces);
* `forestRecovered` / promoted — the `A`-components recovered from `B`'s **star-touching remnant** components (the
  forest-choice parents).

`B`'s **star-avoiding survivor** components (`rightRecovered`) went into the quotient side, not the outer, so they
do **not** contribute to `A`.  That is exactly why the target partition is `leftResidual ∪ forestRecovered = A` and
not the three-region union of the backward side.

## The coverage classification (PROVED from three facts)

`ResolvedTargetOuterCoverageSupply D S Region` fields two `A`-component predicates and their region
characterisations plus a coverage disjunction:

* `represented z γ` — `γ` is represented in the quotient `B`;
* `representedByForest z γ` — `γ` is recovered from a remnant / forest-choice parent;
* `leftResidual_mem` — `γ ∈ leftResidual ↔ γ ∈ A ∧ ¬ represented` (the "not represented" filter);
* `forestRecovered_mem` — `γ ∈ forestRecovered ↔ γ ∈ A ∧ representedByForest` (the remnant parents);
* `coverage` — `γ ∈ A → ¬ represented ∨ representedByForest` (every `A`-component is either untouched by `B` or a
  remnant parent — never a bare survivor, which would be in `B`).

Then `target_outer_coverage` — body-174's `target_outer_partition` — is **PROVED** by pure logic: the forward
direction reads off `γ ∈ A` from either membership; the backward direction case-splits `coverage` and reassembles
via the two `_mem` equivalences.  This is the coverage analogue of body-173's `choice_tag_trichotomy`.

`.toSelectedOuterRegionAssemblySupply` takes a promotion leaf (body-175) and produces body-174's assembly supply
with `target_outer_partition` PROVED — so the two forward-outer residuals are the promotion equality (175) and this
coverage classification, cleanly apart.

Per the HALT: the `componentToForest` / remnant sector inverse body is not entered; `promoted_region_eq` is not
touched; coverage and promotion are kept apart; `leftResidual_mem` is fielded (it becomes provable only once the
abstract `Region.Union.leftResidual` is tied to body-157's concrete `filterElements` construction, which is not
done here).

Landed:

* `ResolvedTargetOuterCoverageSupply D S Region` — the two predicates + three represented-classification facts;
* `.target_outer_coverage` — body-174's `target_outer_partition` (PROVED from the three);
* `.toSelectedOuterRegionAssemblySupply` — body-174's assembly supply from this coverage + a promotion leaf.

Toolkit body (like body-173, the backward twin).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-177 — the target-outer coverage supply.**  The represented-classification of the target outer `A`:
`leftResidual` is the not-represented filter, `forestRecovered` the remnant parents, and every `A`-component is one
or the other (never a bare survivor, which lives in the quotient `B`). -/
structure ResolvedTargetOuterCoverageSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- `γ` is represented in the quotient `B`. -/
  represented : ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop
  /-- `γ` is recovered from a remnant / forest-choice parent of `B`. -/
  representedByForest : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop
  /-- The left residual is the not-represented filter of `A`. -/
  leftResidual_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.leftResidual z).elements ↔ γ ∈ z.1.1.elements ∧ ¬ represented z γ
  /-- The forest region is the remnant-parent filter of `A`. -/
  forestRecovered_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ (Region.Union.forestRecovered z).elements ↔ γ ∈ z.1.1.elements ∧ representedByForest z γ
  /-- Every `A`-component is either not represented (left) or a remnant parent (forest). -/
  coverage : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → ¬ represented z γ ∨ representedByForest z γ

namespace ResolvedTargetOuterCoverageSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-177 — body-174's `target_outer_partition` from the represented-classification.**  Pure logic (the
coverage twin of body-173's `choice_tag_trichotomy`): read off `γ ∈ A` from either membership; case-split coverage
and reassemble via the two `_mem` equivalences. -/
theorem target_outer_coverage (C : ResolvedTargetOuterCoverageSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ (Region.Union.leftResidual z).elements ∨ γ ∈ (Region.Union.forestRecovered z).elements)
      ↔ γ ∈ z.1.1.elements := by
  constructor
  · rintro (hl | hf)
    · exact ((C.leftResidual_mem z γ).mp hl).1
    · exact ((C.forestRecovered_mem z γ).mp hf).1
  · intro hmem
    rcases C.coverage z γ hmem with hnr | hrf
    · exact Or.inl ((C.leftResidual_mem z γ).mpr ⟨hmem, hnr⟩)
    · exact Or.inr ((C.forestRecovered_mem z γ).mpr ⟨hmem, hrf⟩)

/-- **R-6c-body-177 — body-174's assembly supply from this coverage + a promotion leaf.** -/
def toSelectedOuterRegionAssemblySupply (C : ResolvedTargetOuterCoverageSupply D S Region)
    (Promoted : ResolvedPromotedRegionRoundTripSupply D S Region) :
    ResolvedSelectedOuterRegionAssemblySupply D S Region :=
  Promoted.toSelectedOuterRegionAssemblySupply (fun {G} z γ => C.target_outer_coverage z γ)

end ResolvedTargetOuterCoverageSupply

end GaugeGeometry.QFT.Combinatorial
