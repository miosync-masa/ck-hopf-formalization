import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorCollection

/-!
# R-6c-body-348 — forest tag partition (mirror of body-345) + remnant construction type audit (PROVED)

Three-hundred-and-forty-eighth genuine-body step — stage 1 of the remnant collection alignment, plus the
type audit that scopes the remnant round-trip (body-349).  The forest-choice components of
`recoveredPreimageValue z` are EXACTLY the forest region's components — the exact mirror of body-345, with the
`left`/`right` tags excluded and only the forest `inr` kept.

## The characterization (mirror of body-345)

`isForestChoice (recovered) γ` unfolds to `∃ B, recoverChoiceValue z γ = Sum.inr B`.  The `dite` cascade hits
`inr` on EXACTLY the `forestRecovered` branch:

* `⟸` `forest_tag` (body-282): `γ.1 ∈ forestRecovered ⟹ ∃ B, recoverChoiceValue = inr B`;
* `⟹` `mem_unionOuterValue_iff` trichotomy — `leftResidual → inl true` / `rightRecovered → inl false` both
  contradict `inr B`, so `γ.1 ∈ forestRecovered`.

Landed axiom-clean: `mem_forestComponents_iff`.

## Remnant construction type audit (scopes body-349)

The concrete remnant `ResolvedConcreteRemnantReembedSupply.remnantComponent R o` is
`o.contractedSourceGraph.reembedAsSubgraph (selectedOuterContractGraph) …` (ConcreteRemnant.lean:90), whose
carrier data IS `o.contractedSourceGraph`'s `vertices`/`internalEdges`/`externalLegs` (reembed keeps data,
ConcreteRemnant.lean:45-47), and

```text
o.contractedSourceGraph = o.B.1.contractWithStars (D.starOf o.γ.1.tRFG o.B.1)   -- B re-contracted inside γ (RemnantScout)
```

So the remnant round-trip `HEq (remnantComponent recovered o) δ.1` (body-349) reduces — via body-343's
occurrence inversion `HEq (M.innerIdx z δ) o.B` (so `o.B = innerIdx z δ`) and body-341's `houter` (graph
alignment) — to the **re-contract section** at the DATA level:

```text
((M.innerIdx z δ).1.contractWithStars (D.starOf … )).vertices      = δ.1.vertices
                                       … .internalEdges            = δ.1.internalEdges
                                       … .externalLegs             = δ.1.externalLegs   -- via legLift.map_eq
```

i.e. re-contracting the de-contracted inner forest `innerIdx z δ` inside the parent `M.parent z δ` returns the
multi-star quotient component `δ` — the honest inverse of M's de-contraction (M1/M3).  Verdict: this re-contract
section is NOT yet proved; it is the genuine remnant datum (heavier than the survivor reembed, whose round-trip
was carrier-identity), with the external-leg leg closing through `ResolvedTouchedLegLiftDatum.map_eq`.  A
concrete multi-star `ResolvedConcreteRemnantReembedSupply` is likewise NOT yet built — body-349 must construct
it (its five support containments + CD) rather than wire `V.Remnant` for free.

Per the HALT: only the forest tag partition is proved (stage 1); the re-contract section + concrete remnant
provider (body-349) and the remnant collection HEq (body-350) are next; forward quotient / global forward
round-trip are NOT used, the six bridge gates do NOT fabricate exact-`B`, the occurrence-inversion datum
(body-343) is consumed explicitly.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

namespace ResolvedRegionTagValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-348 — the forest-choice components of the reconstruction are the forest region.**  Pure tag
characterization (`recoverChoiceValue` + `forest_tag`), the mirror of body-345. -/
theorem mem_forestComponents_iff (T : ResolvedRegionTagValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (T.Closure.unionOuterValue z).1.elements}) :
    γ ∈ ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageValue z)
      ↔ γ.1 ∈ (T.Closure.Assembly.Region.forestRecovered z).elements := by
  constructor
  · intro h
    rw [ResolvedCoassocSplitChoice.forestComponents] at h
    obtain ⟨B, hB⟩ := (Finset.mem_filter.mp h).2
    rcases (T.Closure.mem_unionOuterValue_iff z γ.1).mp γ.2 with hl | hr | hf
    · exact absurd (((T.choiceAt_recovered_eq' z γ).trans (T.left_tag z γ hl)).symm.trans hB)
        Sum.inl_ne_inr
    · exact absurd (((T.choiceAt_recovered_eq' z γ).trans (T.right_tag z γ hr)).symm.trans hB)
        Sum.inl_ne_inr
    · exact hf
  · intro h
    rw [ResolvedCoassocSplitChoice.forestComponents]
    refine Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ?_⟩
    obtain ⟨B, hB⟩ := T.forest_tag z γ h
    exact ⟨B, (T.choiceAt_recovered_eq' z γ).trans hB⟩

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
