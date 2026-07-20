import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCrossAmbientCorrectingPerm

/-!
# R-6c-body-448 — ForestIdx `mapPerm` transport; corrected-remnant ownership feasibility audit (PROVED)

Four-hundred-and-forty-eighth genuine-body step — the feasibility audit that MUST precede building the consumer-specific
correcting permutations (body-449+).  The most expensive failure would be to build `ρ` and the corrected graph equalities
deeply, then discover the concrete `Concrete` remnant provider's hardcoded ownership cannot consume them.  So we first
(1) prove `ForestIdx` transports across `mapPerm` from `carrier_mapPerm` alone, and (2) read the remnant provider to
confirm the ownership change it needs is LOCAL.

## 1. `ForestIdx` `mapPerm` transport (banked, HEq-free)

`(D.supply G).ForestIdx = {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}` (`ResolvedHopfCoproductSupply:194`).  So
a `ForestIdx` transports by `A ↦ A.mapPerm σ`, its membership read straight off `carrier_mapPerm`'s `Finset.image` — NO
`forget` equality, NO `HEq`, NO exact graph equality.  This dissolves the "ForestIdx cannot be carried without exact
graph equality" worry: `canonicalForestIdxMapPerm` works for ANY `D` (in particular `W'`).

## 2. Remnant ownership audit (the concrete provider is LOCAL)

`ResolvedConcreteRemnantReembedSupply` (`ConcreteRemnant.lean`) HARDCODES
`remnantComponent := o.contractedSourceGraph.reembedAsSubgraph s.selectedOuterContractGraph …`, and its obligations are
exactly:

```text
remnant_vertices : o.contractedSourceGraph.vertices      ⊆ s.selectedOuterContractGraph.vertices
remnant_edges    : o.contractedSourceGraph.internalEdges ≤ s.selectedOuterContractGraph.internalEdges
remnant_legs     : o.contractedSourceGraph.externalLegs  ≤ s.selectedOuterContractGraph.externalLegs
  (+ endpoint / attachment support)
```

Every target is `s.selectedOuterContractGraph` — the QUOTIENT graph, NOT the whole ambient `G`.  So the reembed
obligation is LOCAL: it needs the (corrected) source to sit inside the quotient, and says NOTHING about unrelated `G`
survivor vertices.  `reembedAsSubgraph_toResolvedFeynmanGraph = rfl`, so the reembed is data-preserving.

## 3. The corrected-remnant socket (prototype — LOCAL obligations only)

Since the concrete provider hardcodes `reembedAsSubgraph`, the correcting permutation is NOT pushed into it; instead a
NEW provider carries `starPerm` and re-embeds the CORRECTED source `o.contractedSourceGraph.mapPerm (starPerm o)`.  Its
obligations are the SAME LOCAL shape (`⊆ / ≤ s.selectedOuterContractGraph`) on the corrected graph — again nothing about
global `G` survivors.  `ResolvedCorrectedRemnantReembedSupply` banks this shape (prototype, not yet consumed).

## 4. Verdict

```text
ForestIdx mapPerm transport                    THEOREM      (canonicalForestIdxMapPerm, from carrier_mapPerm; HEq-free)
corrected local graph carrier membership       W'-derivable (mapPerm ∈ carrier via carrier_mapPerm; same route)
existing Concrete rfl-wiring                    NO           (Concrete hardcodes the UNcorrected reembedAsSubgraph)
new corrected Concrete/VBuild constructor       YES          (the corrected-remnant provider — local obligations only)
body-358 round-trip alpha replacement           LOCALIZED    (only the remnant-provider boundary; count/geometry unchanged)
```

**The ForestIdx transport is available through `carrier_mapPerm`; the remaining ownership change is localized to the
remnant-provider / `Concrete` boundary and requires only LOCAL (quotient-internal) subset/le obligations — never fixing
an unrelated `G` survivor.**

Per the HALT/guards: no consumer-specific star permutation is built; no corrected graph equality is proved; nothing is
cast into the existing `Concrete`; strict `StarProm` / `InnerStarRaw` are not used; body-445 stays a valid conditional.
NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` /
singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

/-- **R-6c-body-448 ∎ — `ForestIdx` transports across `mapPerm`.**  A carrier forest relabels to a carrier forest of the
relabeled graph — the membership straight from `carrier_mapPerm`'s image, no `forget`/`HEq`/exact-graph-equality. -/
noncomputable def canonicalForestIdxMapPerm {D : ResolvedCoproductProperForestData}
    {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) (B : (D.supply G).ForestIdx) :
    (D.supply (G.mapPerm σ)).ForestIdx := by
  obtain ⟨A, hA⟩ := B
  refine ⟨A.mapPerm σ, ?_⟩
  rw [D.carrier_mapPerm]
  convert Finset.mem_image_of_mem (fun A' => A'.mapPerm σ) hA using 2

/-- **R-6c-body-448 — prototype: the corrected-remnant re-embed supply.**  Re-embeds the CORRECTED source
`o.contractedSourceGraph.mapPerm (starPerm o)` into the quotient graph; the obligations are the SAME local shape as the
concrete provider (`⊆ / ≤ s.selectedOuterContractGraph`), and say nothing about unrelated `G` survivors.  Prototype only
— NOT yet consumed; the concrete provider still hardcodes the uncorrected reembed. -/
structure ResolvedCorrectedRemnantReembedSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- The correcting star permutation per occurrence. -/
  starPerm : s.ForestChoiceOccurrence → Equiv.Perm VertexId
  /-- The corrected source forest's vertices sit in the quotient graph (LOCAL). -/
  corrected_vertices : ∀ o : s.ForestChoiceOccurrence,
    (o.contractedSourceGraph.mapPerm (starPerm o)).vertices ⊆ s.selectedOuterContractGraph.vertices
  /-- The corrected source forest's internal edges sit in the quotient graph (LOCAL). -/
  corrected_edges : ∀ o : s.ForestChoiceOccurrence,
    (o.contractedSourceGraph.mapPerm (starPerm o)).internalEdges
      ≤ s.selectedOuterContractGraph.internalEdges
  /-- The corrected source forest's external legs sit in the quotient graph (LOCAL). -/
  corrected_legs : ∀ o : s.ForestChoiceOccurrence,
    (o.contractedSourceGraph.mapPerm (starPerm o)).externalLegs
      ≤ s.selectedOuterContractGraph.externalLegs
  /-- The corrected source forest's edges are endpoint-supported. -/
  corrected_edges_supported : ∀ o : s.ForestChoiceOccurrence,
    ∀ e ∈ (o.contractedSourceGraph.mapPerm (starPerm o)).internalEdges,
      e.source ∈ (o.contractedSourceGraph.mapPerm (starPerm o)).vertices
        ∧ e.target ∈ (o.contractedSourceGraph.mapPerm (starPerm o)).vertices
  /-- The corrected source forest's legs are attachment-supported. -/
  corrected_legs_supported : ∀ o : s.ForestChoiceOccurrence,
    ∀ ℓ ∈ (o.contractedSourceGraph.mapPerm (starPerm o)).externalLegs,
      ℓ.attachedTo ∈ (o.contractedSourceGraph.mapPerm (starPerm o)).vertices

end GaugeGeometry.QFT.Combinatorial
