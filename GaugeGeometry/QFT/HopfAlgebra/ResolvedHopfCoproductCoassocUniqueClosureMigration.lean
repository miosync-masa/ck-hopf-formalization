import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRawClosureAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueIdSupportedW

/-!
# R-6c-body-443 — the carrier-closure chain migrated to `W'`; id-uniqueness becomes a membership projection (PROVED)

Four-hundred-and-forty-third genuine-body step — with `W'`'s membership carrying edge/leg id-uniqueness (body-442), the
`∀ G, EdgeIdsUnique` / `∀ G, LegIdsUnique` over-universals are no longer hypotheses: they are read off the LIVE carrier
membership.  The body-430–439 count geometry is NOT re-proved — only the ownership is migrated (`hId := live projection`).

* `edgeIdsUnique_of_subgraphGraph` / `legIdsUnique_of_subgraphGraph` — a subgraph-as-graph inherits the ambient's
  id-uniqueness (`γ.internalEdges_le` / `γ.externalLegs_le`);
* `canonicalUniqueSupportedCarrier_ambientSupported` / `_ambientCD` — the `W'` accessors; `canonicalUniqueStarFactsOfW'`
  — the `W'` canonical star facts (same allocator as body-426);
* `canonicalUniqueInnerRawCarrierClosureSupply` — `innerRaw_mem` over `W'`, its parent id-uniqueness inherited (step 1)
  from the outer block's own `z.1.2` membership;
* `canonicalUniqueMultiStarCarrierClosureBundleSupply` — the `W'` bundle: `recovered_raw_mem` recovers `G.EdgeIdsUnique`
  from `z.1.2` (`edgeIdsUnique_of_carrier_mem`) and feeds it to `regionRawUnion_count_lt` (body-439) — **NO `∀ G`
  id-uniqueness input**.

So the bundle over `W'` takes only the measure leaves (`Nne` / `Ppos`); id-uniqueness is entirely internalized as a
projection of live membership.  `hIdAll` / `hLegAll` disappear as bundle inputs.

Per the HALT/guards: `Ppos` is untouched; id-uniqueness is used ONLY as `EdgeIdsUnique` (never as `Nodup`); no arbitrary
`G` id-uniqueness is reintroduced; the count geometry (430–439) is reused verbatim (ownership migration only).  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {G : ResolvedFeynmanGraph}

/-! ### Step 1 — id-uniqueness inherits to a subgraph-as-graph. -/

/-- **R-6c-body-443 — a subgraph-as-graph inherits ambient edge-id uniqueness.** -/
theorem edgeIdsUnique_of_subgraphGraph (hG : G.EdgeIdsUnique) (γ : ResolvedFeynmanSubgraph G) :
    γ.toResolvedFeynmanGraph.EdgeIdsUnique :=
  fun e₁ h₁ e₂ h₂ hid =>
    hG e₁ (Multiset.mem_of_le γ.internalEdges_le h₁) e₂ (Multiset.mem_of_le γ.internalEdges_le h₂) hid

/-- **R-6c-body-443 — a subgraph-as-graph inherits ambient leg-id uniqueness.** -/
theorem legIdsUnique_of_subgraphGraph (hG : G.LegIdsUnique) (γ : ResolvedFeynmanSubgraph G) :
    γ.toResolvedFeynmanGraph.LegIdsUnique :=
  fun ℓ₁ h₁ ℓ₂ h₂ hid =>
    hG ℓ₁ (Multiset.mem_of_le γ.externalLegs_le h₁) ℓ₂ (Multiset.mem_of_le γ.externalLegs_le h₂) hid

/-! ### The `W'` accessors and star facts. -/

/-- **R-6c-body-443 — a `W'` carrier member's ambient is support-well-formed.** -/
theorem canonicalUniqueSupportedCarrier_ambientSupported {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier) :
    ResolvedAmbientSupported G :=
  ((mem_canonicalUniqueSupportedCarrier_iff A).mp hA).1

/-- **R-6c-body-443 — a `W'` carrier member's ambient is connected-divergent.** -/
theorem canonicalUniqueSupportedCarrier_ambientCD {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalUniqueSupportedCarrierProperSupply.index G).carrier) :
    G.forget.IsConnectedDivergent :=
  ((mem_canonicalUniqueSupportedCarrier_iff A).mp hA).2.1

/-- **R-6c-body-443 — `W'` supplies the canonical star facts** (same fresh allocator as body-426). -/
def canonicalUniqueStarFactsOfW' :
    ResolvedCanonicalStarFacts canonicalUniqueSupportedCarrierProperSupply.toData where
  starOf_fresh := fun G' A η _ => resolvedComponentFreshStar_not_mem_vertices G' A η
  starOf_injective := fun G' A => resolvedComponentFreshStar_injective_on_elements G' A

/-! ### Step 2 — the `W'` inner-raw carrier closure. -/

/-- **R-6c-body-443 — `innerRaw_mem` over `W'`.**  The parent's id-uniqueness is inherited (step 1) from the outer
block's own `z.1.2` membership; support (body-427), CD (`Core.parentCD`), and properness (body-378) as before. -/
noncomputable def canonicalUniqueInnerRawCarrierClosureSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalUniqueSupportedCarrierProperSupply.toData) :
    ResolvedMultiStarInnerRawCarrierClosureSupply Core where
  innerRaw_mem := fun z δ => by
    have hEdgeG := edgeIdsUnique_of_carrier_mem z.1.2
    have hLegG := legIdsUnique_of_carrier_mem z.1.2
    refine (mem_canonicalUniqueSupportedCarrier_iff _).mpr
      ⟨resolvedAmbientSupported_of_subgraphGraph (Core.parent z δ), ?_,
       edgeIdsUnique_of_subgraphGraph hEdgeG (Core.parent z δ),
       legIdsUnique_of_subgraphGraph hLegG (Core.parent z δ), ?_⟩
    · rw [← ResolvedFeynmanSubgraph.forget_toFeynmanGraph (Core.parent z δ)]
      exact (Core.parent z δ).forget.toFeynmanGraph_isConnectedDivergent (Core.parentCD z δ)
    · exact innerRaw_isProperForest
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider Core z δ

/-! ### Step 5 — the `W'` carrier-closure bundle, id-uniqueness internalized. -/

/-- **R-6c-body-443 ∎ — the `W'` carrier-closure bundle.**  Both carrier-membership fields are theorems, and — the point
of this body — `recovered_raw_mem` recovers `G`'s edge-id uniqueness from the outer block's live membership `z.1.2`
(`edgeIdsUnique_of_carrier_mem`), so NO `∀ G` id-uniqueness is an input.  The measure leaves (`Nne` / `Ppos`) remain. -/
noncomputable def canonicalUniqueMultiStarCarrierClosureBundleSupply
    (Nne : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentNonemptySupply G)
    (Ppos : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalUniqueSupportedCarrierProperSupply.toData) :
    ResolvedMultiStarCarrierClosureBundleSupply Core canonicalUniqueStarFactsOfW' where
  Closure := canonicalUniqueInnerRawCarrierClosureSupply Core
  recovered_raw_mem := fun {G} z => by
    have hEdgeG := edgeIdsUnique_of_carrier_mem z.1.2
    refine (mem_canonicalUniqueSupportedCarrier_iff _).mpr
      ⟨canonicalUniqueSupportedCarrier_ambientSupported z.1.2,
       canonicalUniqueSupportedCarrier_ambientCD z.1.2,
       hEdgeG, legIdsUnique_of_carrier_mem z.1.2, ?_⟩
    exact regionRawUnion_isProperForest_of_complement (Nne G) (Ppos G)
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core))
      canonicalUniqueStarFactsOfW' z
      (regionRawUnion_complementEdges_card_pos_of_count_lt
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core))
        canonicalUniqueStarFactsOfW' z
        (regionRawUnion_count_lt canonicalUniqueStarFactsOfW' hEdgeG
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core)) z))

end GaugeGeometry.QFT.Combinatorial
