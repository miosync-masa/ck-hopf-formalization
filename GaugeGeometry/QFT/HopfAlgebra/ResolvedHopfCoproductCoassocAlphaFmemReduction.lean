import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemnantCorrespondence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterIsProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueClosureMigration

/-!
# R-6c-body-496 — post-alpha residual purity audit + `Fmem` root reduction (PROVED)

Four-hundred-and-ninety-sixth genuine-body step — opening the residual-purification campaign.  With the body-495 closed
theorem's proof-leaf residual at ZERO, the remaining explicit inputs of `coassoc_gen_of_canonicalMultiStar_alpha_closed`
are audited field-by-field, and the shortest root — `Fmem : ResolvedSelectedOuterFilteredMemSupply W'.toData` — is
reduced to the `W'` membership criterion and CONSTRUCTED from the two connected-divergent leaves.

## Signature audit — the remaining inputs of `coassoc_gen_of_canonicalMultiStar_alpha_closed`

```text
field                            consumer                     existing source / reduction                     verdict
Fmem                             fwdMapFilteredAlphaValue(470) mem_canonicalUniqueSupportedCarrier_iff +        CANONICAL DERIVED — this body:
                                                              selectedOuterRaw_isProperForest(264)             constructed from (N, E) + W'
VBuild.Measure                   survivor / N / E / CD leaves  ResolvedMeasureLeafSupply                        CK STRUCTURAL / DIVERGENCE MODEL LAW
VBuild.survivorInj               summand agreement (259)       survivorSupply_of_measure Finset injectivity     CANONICAL DERIVED CANDIDATE
VBuild.survivorGen               summand agreement (259)       resolvedComponentGenTerm equality                CANONICAL DERIVED CANDIDATE
VBuild.Quotient.quotient_mem     V.quotientForestRaw (470)     filtered W' carrier closure (honest per 468)     CANONICAL DERIVED CANDIDATE (filtered)
VBuild.Quotient.quot_eq          summand agreement (259)       raw contraction/class geom + carrier typing +    CENTRAL OPEN — decomposition audit required
                                                              subtype lift  (NOT whole physics)
ValueGeometry.legComplete        parentCD leg-lift (445)       touched-leg boundary lifting                     CENTRAL OPEN — boundary/leg structural law
ValueGeometry.parentCD           forestComponentCD (341)       IsDivergencePreservedByAdmissibleForestContract  CK STRUCTURAL / DIVERGENCE MODEL LAW
                                                              + legComplete leg-lift
OccRaw.occurrence_inner_...raw   innerIdx_occurrence (343)     de-contraction inversion (contractWithStars)     CANONICAL DERIVED CANDIDATE
Split.survivor_avoids            rightDomain split (472)       survivor star-avoidance (star filter geom)       CANONICAL DERIVED CANDIDATE
Split.remnant_touches            forestDomain split (472)      remnant star-touch (star filter geom)            CANONICAL DERIVED CANDIDATE
rep / repCD / rep_gen            generator carrier (97)        model choice of generator representatives        CK STRUCTURAL (model input)
```

## `Fmem` reduction (this body) — the four ambient conditions are `W'`-derived

`mem_canonicalUniqueSupportedCarrier_iff` (body-442) splits carrier membership of `selectedOuterRawOf ⟨A,p⟩` into
`⟨ResolvedAmbientSupported G, G.forget.IsConnectedDivergent, G.EdgeIdsUnique, G.LegIdsUnique, IsProperForest⟩`.  The FIRST
FOUR are ambient facts about `G` — SHARED with `A`, so they come straight from `A.2` (the outer's own live membership); NO
`IsProperForest → membership` shortcut.  The fifth, `(selectedOuterRawOf ⟨A,p⟩).IsProperForest`, is the proved body-264
`selectedOuterRaw_isProperForest` — its five conjuncts: `IsNonempty` / `complementEdges.card > 0` need only `P` (`W'`),
while `HasNonemptyComponents` / `internalEdges.card > 0` / `HasPositiveInternalEdgesComponents` need the connected-divergent
leaves `N` (`cd_nonempty`) and `E` (`cd_positiveInternalEdges`) — the divergence-structure data (the SAME `VBuild.Measure`
already carries, via `toConnectedDivergentNonemptySupply`).

## Status

```text
Fmem                             CANONICAL CONSTRUCTED from (N, E)  (independent explicit input REMOVED — a function of the
                                 divergence leaves the model already supplies)
carrier / support / CD / IDs     ALL W'-derived (from A.2)
residual                         the two CD leaves N (cd_nonempty) / E (cd_positiveInternalEdges) — divergence-structure
next root                        Split (survivor_avoids / remnant_touches) — CANONICAL DERIVED CANDIDATE
```

Per the HALT/guards: the `toSelectedOuterFilteredMemSupply` PROJECTION is NOT used as a proof (this is a genuine
`selectedOuter_mem` proof); nothing is back-computed from the recovered round-trip / coassoc; the body-495 closed theorem is
NOT edited; `Split` / `VBuild` / `OccRaw` / `quot_eq` / `ValueGeometry` implementations are NOT entered; NO new typeclass /
model axiom; NO unconditional-coassoc claim; strict `StarProm` / `InnerStarRaw` stay ZERO.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **R-6c-body-496 ∎ — the canonical `W'` selected-outer filtered membership, CONSTRUCTED.**  The four ambient conditions
come from the outer's own live carrier membership `A.2` (`mem_canonicalUniqueSupportedCarrier_iff`); the selected-outer
properness is body-264's theorem fed the two connected-divergent leaves.  `Fmem` is thereby removed as an independent
explicit input — it is a function of the divergence leaves `(N, E)` the model already supplies. -/
noncomputable def canonicalUniqueSelectedOuterFilteredMemSupply
    (N : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply G)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G) :
    ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData where
  selectedOuter_mem := fun {G} A p hp => by
    obtain ⟨hAS, hCD, hEdge, hLeg, -⟩ := (mem_canonicalUniqueSupportedCarrier_iff A.1).mp A.2
    refine (mem_canonicalUniqueSupportedCarrier_iff _).mpr ⟨hAS, hCD, hEdge, hLeg, ?_⟩
    have hq : (⟨A, p⟩ : ForestBlockDomType canonicalUniqueSupportedCarrierProperSupply.toData G)
        ∈ forestBlockDomFinset G := by
      simp only [forestBlockDomFinset, Finset.mem_sigma]
      exact ⟨Finset.mem_attach _ _, hp⟩
    exact selectedOuterRaw_isProperForest (N G) (E G)
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider ⟨⟨A, p⟩, hq⟩

/-- **R-6c-body-496 — the same, from a measure leaf supply.**  The two connected-divergent leaves are `ResolvedMeasure
LeafSupply` projections, so `Fmem` reduces entirely to `VBuild.Measure`'s divergence data. -/
noncomputable def canonicalUniqueSelectedOuterFilteredMemSupply_of_measure
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G) :
    ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData :=
  canonicalUniqueSelectedOuterFilteredMemSupply
    (fun G => Measure.toConnectedDivergentNonemptySupply G) E

end GaugeGeometry.QFT.Combinatorial
