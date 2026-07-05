import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftResidualSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegionSectorBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterRegionPartition

/-!
# R-6c-body-173 — recovered region membership assembly: the backward-outer partition from the three bridges

Hundred-and-seventy-third genuine-body step, assembling body-168's `recovered_region_membership` from the three
sector bridges (bodies 170/171/172) and the choice-tag trichotomy.  The three recovered regions of a forward image
are exactly the three choice-tag classes of `q`, and every component of `q.1` has exactly one tag — so the three
region memberships partition `q.1.1.elements`.  This is the first place the three region colours close into a
circle.

## The choice-tag trichotomy (PROVED)

`choice_tag_trichotomy`: for a component `γ` of a split choice `q`,

```text
(leftSelectedConcrete q γ ∨ rightPrimSelected q γ ∨ forestChoiceSelected q γ)  ↔  γ ∈ q.1.1.elements
```

— every component of `q.1` has exactly one tag (`inl true` / `inl false` / `inr`), by `Sum` / `Bool` case analysis
on `choiceAt q ⟨γ, hγ⟩`; conversely each tag predicate carries the membership `∃ hγ`.

## The assembly (PROVED)

`ResolvedRecoveredRegionMembershipAssemblySupply D S Region` bundles the three sector bridges (`Left` / `Right` /
`Forest`).  `.recovered_region_membership` is **proved** by rewriting the three region memberships into their tag
predicates (bodies 172/170/171) and applying the trichotomy:

```text
(γ ∈ leftResidual ∨ γ ∈ rightRecovered ∨ γ ∈ forestRecovered)
   ↔ (leftSelectedConcrete ∨ rightPrimSelected ∨ forestChoiceSelected)   -- the three bridges
   ↔ γ ∈ q.1.1.elements                                                  -- the trichotomy
```

`.toRecoveredOuterRegionPartitionSupply` produces body-168's `ResolvedRecoveredOuterRegionPartitionSupply` — and
hence, through body-168 → 163 → 160 → …, the backward-outer round-trip.  So body-168's
`recovered_region_membership` is no longer fielded: it is PROVED from the three sector bridges and the trichotomy.

## Consequence

The backward-outer partition is now entirely in choice-tag vocabulary.  The remaining outer-partition content is
the three forward facts of body-167 (`leftOf_recovered_eq` / `promotedOf_recovered_eq` / `target_outer_partition`)
and the three sector bridges (bodies 170/171/172), which are the sector inverse laws.

Per the HALT: no sector bridge internals, no `representedInQuotient`, no `HEq` round-trip; pure logical assembly +
`Sum` case analysis.

Landed:

* `choice_tag_trichotomy` — the choice-tag trichotomy (PROVED);
* `ResolvedRecoveredRegionMembershipAssemblySupply D S Region` — the three-bridge bundle;
* `.recovered_region_membership` — body-168's membership (PROVED from the bridges + trichotomy);
* `.toRecoveredOuterRegionPartitionSupply` — body-168's supply (→ the backward-outer round-trip).

Toolkit body (like body-167/168).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-173 — the choice-tag trichotomy.**  Every component of `q.1` has exactly one tag
(`inl true` / `inl false` / `inr`). -/
theorem choice_tag_trichotomy (q : ResolvedCoassocSplitChoice D G) (γ : ResolvedFeynmanSubgraph G) :
    (ResolvedCoassocSplitChoice.leftSelectedConcrete q γ ∨ rightPrimSelected q γ
        ∨ forestChoiceSelected q γ)
      ↔ γ ∈ q.1.1.elements := by
  constructor
  · rintro (⟨hγ, _⟩ | ⟨hγ, _⟩ | ⟨hγ, _, _⟩) <;> exact hγ
  · intro hmem
    rcases h : ResolvedCoassocSplitChoice.choiceAt q ⟨γ, hmem⟩ with b | B
    · cases b
      · exact Or.inr (Or.inl ⟨hmem, h⟩)
      · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr (Or.inr ⟨hmem, B, h⟩)

/-- **R-6c-body-173 — the recovered-region membership assembly supply.**  The three sector bridges (left / right /
forest), from which body-168's `recovered_region_membership` follows. -/
structure ResolvedRecoveredRegionMembershipAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- The left residual sector bridge (body-172). -/
  Left : ResolvedLeftResidualSectorBridgeSupply D S Region
  /-- The right region sector bridge (body-170). -/
  Right : ResolvedRightRegionSectorBridgeSupply D S Region
  /-- The forest region sector bridge (body-171). -/
  Forest : ResolvedForestRegionSectorBridgeSupply D S Region

namespace ResolvedRecoveredRegionMembershipAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-173 — body-168's `recovered_region_membership` from the three bridges + the trichotomy.** -/
theorem recovered_region_membership (A : ResolvedRecoveredRegionMembershipAssemblySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (γ : ResolvedFeynmanSubgraph G) :
    (γ ∈ (Region.Union.leftResidual (fwdMap S q)).elements
        ∨ γ ∈ (Region.Union.rightRecovered (fwdMap S q)).elements
        ∨ γ ∈ (Region.Union.forestRecovered (fwdMap S q)).elements)
      ↔ γ ∈ q.1.1.elements := by
  rw [A.Left.leftResidual_forward_membership q γ, A.Right.rightRecovered_forward_membership q γ,
    A.Forest.forestRecovered_forward_membership q γ]
  exact choice_tag_trichotomy q γ

/-- **R-6c-body-173 — body-168's recovered-outer region partition supply from the three bridges.** -/
def toRecoveredOuterRegionPartitionSupply
    (A : ResolvedRecoveredRegionMembershipAssemblySupply D S Region) :
    ResolvedRecoveredOuterRegionPartitionSupply D S Region where
  recovered_region_membership := fun {G} q γ => A.recovered_region_membership q γ

end ResolvedRecoveredRegionMembershipAssemblySupply

end GaugeGeometry.QFT.Combinatorial
