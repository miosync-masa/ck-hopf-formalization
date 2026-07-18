import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentVerticesConcrete

/-!
# R-6c-body-390 — bank-3b: `parent_remnantComponent` demoted from datum to DERIVED THEOREM (PROVED)

Three-hundred-and-ninetieth genuine-body step — the pure assembly that closes culprit-D's parent-reconstruction socket.
With all three projections now THEOREMs (`internalEdges` 387, `externalLegs` 388, `vertices` 389), body-381's
`parent_remnantComponent_of_data` (`ResolvedFeynmanSubgraph.ext`) assembles them into the honest datum of body-370:
`Core.parent (fwd q) δ = o.γ.1`.  So `parent_remnantComponent` is no longer a supplied gate — it is a **derived
theorem**, and body-381's raw supply + body-370's forest bridge are rewired to consume it.

## Design guard — the ID uniqueness is `q`-local, NOT global

The projection theorems need `G.EdgeIdsUnique` / `G.LegIdsUnique`, but requiring `∀ G, G.EdgeIdsUnique` is stronger than
the live domain.  So the id-uniqueness is restricted to graphs that actually carry a `FilteredForestBlockDom D G`, via
`ResolvedFilteredForestBlockUniqueIdSupply` — a `q`-local canonical-unique-payload ownership gate, NOT new geometry.

* `ResolvedFilteredForestBlockUniqueIdSupply` — the `q`-local `EdgeIdsUnique` / `LegIdsUnique` gate;
* `parent_remnantComponent_of_multiStar_geometry` — the three projections assembled into `Core.parent = o.γ.1`;
* `resolvedParentRemnantSectionValue` — body-381's `ResolvedParentRemnantSectionValueSupply`, now a derived construction;
* `resolvedMultiStarForestBridgeOfGeometry` — body-370's forest bridge fed by the derived parent section.

Per the HALT: NO new geometry beyond the three projections; the ID uniqueness is the `q`-local base-model gate; `OccInv`
/ the forest-bridge circularity / the forward round-trip are NOT used in the value proof; the carrier `Closure` is used
ONLY in the final converters (never in the value proof).  This updates body-370's audit verdict:
`parent_remnantComponent` is a derived theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

/-- **R-6c-body-390 — the `q`-local ID-uniqueness gate.**  Edge/leg id uniqueness restricted to the graphs that
actually carry a live filtered forest-block domain — the canonical unique-payload ownership gate, weaker than the global
`∀ G, G.EdgeIdsUnique`. -/
structure ResolvedFilteredForestBlockUniqueIdSupply (D : ResolvedCoproductProperForestData) where
  /-- Edge ids are unique on any graph carrying a filtered forest-block domain element. -/
  edgeIdsUnique : ∀ {G : ResolvedFeynmanGraph}, FilteredForestBlockDom D G → G.EdgeIdsUnique
  /-- Leg ids are unique on any graph carrying a filtered forest-block domain element. -/
  legIdsUnique : ∀ {G : ResolvedFeynmanGraph}, FilteredForestBlockDom D G → G.LegIdsUnique

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-390 — the de-contracted parent equals the occurrence source outer** (assembled from the three
projections; body-370's datum, now a theorem). -/
theorem parent_remnantComponent_of_multiStar_geometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    Core.parent (fwdMapFilteredValue Fmem V q) δ = o.γ.1 :=
  parent_remnantComponent_of_data Core _ _ _
    (parent_remnantComponent_vertices Core CarrierProper Fstar StarProm Wiring
      (Ids.edgeIdsUnique q) q o δ hδ)
    (parent_remnantComponent_internalEdges Core Fstar StarProm Wiring
      (Ids.edgeIdsUnique q) q o δ hδ)
    (parent_remnantComponent_externalLegs Core Fstar StarProm Wiring
      (Ids.legIdsUnique q) q o δ hδ)

/-- **R-6c-body-390 — body-381's raw parent-section supply, now a derived construction.** -/
noncomputable def resolvedParentRemnantSectionValue
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete) :
    ResolvedParentRemnantSectionValueSupply Core Fmem V where
  parent_remnantComponent_raw := fun q o δ hδ =>
    parent_remnantComponent_of_multiStar_geometry Core CarrierProper Ids Fstar StarProm Wiring q o δ hδ

/-- **R-6c-body-390 — body-370's forest bridge, fed by the derived parent section.**  The
`parent_remnantComponent` gate is eliminated: the bridge now consumes the assembled geometry. -/
noncomputable def resolvedMultiStarForestBridgeOfGeometry
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (CarrierProper : ResolvedCarrierProperProvider D)
    (Ids : ResolvedFilteredForestBlockUniqueIdSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (Split : ResolvedValueQuotientRegionSplitSupply Fmem V) :
    ResolvedForestRegionValueCoreBridgeSupply Fmem V :=
  resolvedMultiStarForestBridge (Core.toDecontractionSupply Closure) Fstar Split
    (Core.toParentRemnantSection Closure
      (resolvedParentRemnantSectionValue Core CarrierProper Ids Fstar StarProm Wiring))

end GaugeGeometry.QFT.Combinatorial
