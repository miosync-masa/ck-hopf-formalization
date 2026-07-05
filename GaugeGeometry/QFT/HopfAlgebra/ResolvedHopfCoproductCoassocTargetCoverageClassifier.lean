import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRecoveryGeometry

/-!
# R-6c-body-180 — target coverage classifier: `coverage` reduced to a star/remnant `represented_cases`

Hundred-and-eightieth genuine-body step, reducing body-177's last coverage fact to a single star/remnant
classifier.  Body-177's `coverage` — every `A`-component is not-represented (left) or a remnant parent (forest) —
is, by excluded middle on "represented in `B`", equivalent to the one-directional classifier: *if* an `A`-component
is represented in `B` at all, *then* it is represented as a forest/remnant parent.

## Why the classifier is one-directional

For a component `γ` of the target outer `A = z.1`:

* if `γ` is **not** represented in the quotient `B`, it is a left-primitive piece — `leftResidual` — with no forest
  content, so the left disjunct holds outright;
* if `γ` **is** represented in `B`, the representation can only be through a **star-touching remnant** parent
  (`representedByForest`) — never a bare **star-avoiding survivor**, because a survivor is a component of `B` on the
  quotient side, not a representation of an outer `A`-component in the selected outer.

So the only content of `coverage` is the second bullet: `represented → representedByForest`.  The
survivor / `rightRecovered` case is vacuous for the target outer — it lives on the quotient side — which is exactly
why the target partition is `leftResidual ∪ forestRecovered` (two regions), not three.

## The classifier (fielded) and `coverage` (PROVED)

`ResolvedTargetCoverageClassifierSupply D S Region` fields the two `A`-component predicates and the one-directional
classifier

```text
represented_cases : γ ∈ A → represented z γ → representedByForest z γ
```

Then `coverage` is **PROVED** by pure logic (`by_cases` on `represented z γ`): the represented branch applies
`represented_cases`, the unrepresented branch gives `¬ represented` directly.  So body-177's `coverage` is no longer
fielded; it is `represented_cases` + excluded middle.

## Consequence

The forward-outer residual is now just two boxes:

* the **forest-recovery geometry** (body-179, `forestRecovered_mem` + `promoted_region_eq`);
* the **star/remnant classifier** (this body, `represented_cases`).

plus the already-proved `leftOf` (body-174) and `leftResidual_mem` (body-178).  The next body assembles
178 + 179 + 180 into body-177's `ResolvedTargetOuterCoverageSupply` and flows it to body-174 → 167 → 162.

Per the HALT: the body of `represented_cases` (the star-touch / remnant sector geometry) is not entered;
`forestRecovered_mem` / `promoted_region_eq` are used from body-179 only; the survivor / `rightRecovered`
non-contribution is recorded in the doc.

Landed:

* `ResolvedTargetCoverageClassifierSupply D S Region` — the two predicates + the one-directional classifier;
* `.coverage` — body-177's coverage disjunction (PROVED from `represented_cases`).

Toolkit body (like body-177).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-180 — the target coverage classifier supply.**  The one-directional star/remnant classifier: a
represented `A`-component is a forest/remnant parent (never a bare survivor). -/
structure ResolvedTargetCoverageClassifierSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- `γ` is represented in the quotient `B`. -/
  represented : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop
  /-- `γ` is recovered from a remnant / forest-choice parent of `B`. -/
  representedByForest : ∀ {G : ResolvedFeynmanGraph},
    ForestBlockCodType D G → ResolvedFeynmanSubgraph G → Prop
  /-- A represented `A`-component is represented as a forest/remnant parent (the survivor case is vacuous for the
  target outer — it lives on the quotient side). -/
  represented_cases : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → represented z γ → representedByForest z γ

namespace ResolvedTargetCoverageClassifierSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-180 — body-177's `coverage` from the one-directional classifier.**  Pure logic: `by_cases` on
whether `γ` is represented in `B`. -/
theorem coverage (C : ResolvedTargetCoverageClassifierSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) (γ : ResolvedFeynmanSubgraph G)
    (hγ : γ ∈ z.1.1.elements) :
    ¬ C.represented z γ ∨ C.representedByForest z γ := by
  by_cases hrep : C.represented z γ
  · exact Or.inr (C.represented_cases z γ hγ hrep)
  · exact Or.inl hrep

end ResolvedTargetCoverageClassifierSupply

end GaugeGeometry.QFT.Combinatorial
