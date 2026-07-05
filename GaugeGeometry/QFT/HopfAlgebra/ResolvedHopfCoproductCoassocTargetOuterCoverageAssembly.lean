import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTargetCoverageClassifier

/-!
# R-6c-body-181 — target outer coverage assembly: 178 + 179 + 180 → body-177 → 174 → 167 → 162

Hundred-and-eighty-first genuine-body step, the forward-outer coverage assembly.  The three coverage components —
body-178's `leftResidual_membership`, body-179's forest-recovery geometry, and body-180's star/remnant classifier —
are wired into body-177's `ResolvedTargetOuterCoverageSupply`, with the two `A`-component predicates unified as
`representedInQuotient` (body-157/178) and `representedByForest` (body-179).  The result flows all the way to
body-162's `ResolvedSelectedOuterPartitionSupply`, so the forward-outer partition chain is now a single line.

## The predicate unification

Body-177's coverage supply carries one pair of predicates `represented` / `representedByForest`.  Here they are
pinned:

* `represented := Left.L.representedInQuotient` (body-178's construction, the `leftResidual` filter predicate);
* `representedByForest := Forest.representedByForest` (body-179's forest-recovery predicate).

With that pinning the three components fit body-177 exactly:

```text
leftResidual_mem     := Left.leftResidual_membership        (body-178, filter)          -- uses represented
forestRecovered_mem  := Forest.forestRecovered_mem          (body-179, geometry view)   -- uses representedByForest
coverage             := (classifier).coverage               (body-180, PROVED)          -- uses both
```

where `classifier` is body-180's supply built on the *same* pinned predicates, so its `represented_cases` field —
"a represented `A`-component is a forest/remnant parent" — is the only genuinely fielded content of the coverage
side (the survivor case is vacuous, body-180).

## The chain, one line

```text
ResolvedTargetOuterCoverageAssemblySupply  (178 + 179 + 180)
  → ResolvedTargetOuterCoverageSupply                     (body-177, coverage classification)
  → ResolvedSelectedOuterRegionAssemblySupply             (body-174, via 179's promotion leaf)
  → ResolvedSelectedOuterRegionPartitionSupply            (body-167, leftOf PROVED)
  → ResolvedSelectedOuterPartitionSupply                  (body-162, leftOf ⊔ promotedOf = A)
  → … → witnessSplit → coassoc_gen
```

`.toTargetOuterCoverageSupply` builds body-177; `.toSelectedOuterRegionAssemblySupply` grafts body-179's promotion
leaf and produces body-174's supply; `.toSelectedOuterPartitionSupply` runs it out to body-162.

## Consequence — the forward-outer floor

After this assembly the forward-outer partition stands on exactly:

* the **forest-recovery geometry** (body-179, `forestRecovered_mem` + `promoted_region_eq` — the `componentToForest`
  de-contraction round-trip);
* the **star/remnant classifier** (body-180, `represented_cases`);
* the **wiring bridge** `leftResidual_eq` (body-178, abstract union ↔ body-157 filter).

with `leftOf` (body-174) and `leftResidual_mem` (body-178) proved.  The remaining coassociativity residual is these
forward-outer leaves, the backward trichotomy's sector bridges (bodies 170/171/172), the two `HEq` transports, the
disjointnesses / carrier closure, and the non-region base.

Per the HALT: `represented_cases`, `promoted_region_eq`, and `forestRecovered_mem` bodies are not entered; this body
is the 178/179/180 wiring only.

Landed:

* `ResolvedTargetOuterCoverageAssemblySupply D S Region` — the three components with unified predicates;
* `.toTargetOuterCoverageSupply` — body-177's supply;
* `.toSelectedOuterRegionAssemblySupply` — body-174's supply (with body-179's promotion leaf);
* `.toSelectedOuterPartitionSupply` — body-162's supply (the forward-outer chain closed).

Toolkit body (like body-173, the backward assembly).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-181 — the target outer coverage assembly supply.**  Body-178's left-residual membership, body-179's
forest-recovery geometry, and body-180's star/remnant classifier (as its `represented_cases` field), with the two
predicates pinned to `representedInQuotient` and `representedByForest`. -/
structure ResolvedTargetOuterCoverageAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-178: the left-residual membership (filter) supply. -/
  Left : ResolvedLeftResidualMembershipSupply D S Region
  /-- Body-179: the forest-recovery geometry provider. -/
  Forest : ResolvedForestRecoveryGeometrySupply D S Region
  /-- Body-180's classifier content: a represented `A`-component is a forest/remnant parent. -/
  represented_cases : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : ResolvedFeynmanSubgraph G),
    γ ∈ z.1.1.elements → Left.L.representedInQuotient z γ → Forest.representedByForest z γ

namespace ResolvedTargetOuterCoverageAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-181 — body-180's classifier on the pinned predicates.** -/
def classifier (A : ResolvedTargetOuterCoverageAssemblySupply D S Region) :
    ResolvedTargetCoverageClassifierSupply D S Region where
  represented := fun {G} z γ => A.Left.L.representedInQuotient z γ
  representedByForest := fun {G} z γ => A.Forest.representedByForest z γ
  represented_cases := fun {G} z γ hγ hrep => A.represented_cases z γ hγ hrep

/-- **R-6c-body-181 — body-177's coverage supply from the three components.** -/
def toTargetOuterCoverageSupply (A : ResolvedTargetOuterCoverageAssemblySupply D S Region) :
    ResolvedTargetOuterCoverageSupply D S Region where
  represented := fun {G} z γ => A.Left.L.representedInQuotient z γ
  representedByForest := fun {G} z γ => A.Forest.representedByForest z γ
  leftResidual_mem := fun {G} z γ => A.Left.leftResidual_membership z γ
  forestRecovered_mem := fun {G} z γ => A.Forest.forestRecovered_mem z γ
  coverage := fun {G} z γ hγ => A.classifier.coverage z γ hγ

/-- **R-6c-body-181 — body-174's assembly supply from the coverage + body-179's promotion leaf.** -/
def toSelectedOuterRegionAssemblySupply (A : ResolvedTargetOuterCoverageAssemblySupply D S Region) :
    ResolvedSelectedOuterRegionAssemblySupply D S Region :=
  A.toTargetOuterCoverageSupply.toSelectedOuterRegionAssemblySupply A.Forest.toPromotedRegionRoundTripSupply

/-- **R-6c-body-181 — body-162's selected-outer partition supply (the forward-outer chain closed).** -/
def toSelectedOuterPartitionSupply (A : ResolvedTargetOuterCoverageAssemblySupply D S Region) :
    ResolvedSelectedOuterPartitionSupply D S Region :=
  A.toSelectedOuterRegionAssemblySupply.toSelectedOuterRegionPartitionSupply.toSelectedOuterPartitionSupply

end ResolvedTargetOuterCoverageAssemblySupply

end GaugeGeometry.QFT.Combinatorial
