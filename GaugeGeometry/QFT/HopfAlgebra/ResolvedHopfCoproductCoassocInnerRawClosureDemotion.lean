import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedWMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawProper

/-!
# R-6c-body-427 — `innerRaw_mem` demoted to a theorem over `W` (PROVED)

Four-hundred-and-twenty-seventh genuine-body step — cashing in body-426's audit.  The inner-raw carrier-closure gate
`ResolvedMultiStarInnerRawCarrierClosureSupply` (body-377) was an honest residual: its single field `innerRaw_mem z δ :
Core.innerRaw z δ ∈ D.carrier (Core.parent z δ).toResolvedFeynmanGraph`.  Body-426's membership `iff` normalized any such
carrier membership (over `W`) to `ResolvedAmbientSupported ∧ forget.IsConnectedDivergent ∧ IsProperForest`.  All three
are now available at the parent, so — for a de-contraction core over `W.toData` — the closure supply is a **derived
construction**, not a supplied field.

* `resolvedAmbientSupported_of_subgraphGraph` — a subgraph-as-graph is ambient-supported straight from the subgraph's
  own `edges_supported` / `legs_supported` (NO circularity with any Core construction);
* `canonicalInnerRawCarrierClosureSupply` — `ResolvedMultiStarInnerRawCarrierClosureSupply Core`, built from the
  body-426 `iff`, `Core.parentCD` (the parent's connected-divergence, bridged subgraph→graph via `forget_toFeynmanGraph`
  + `toFeynmanGraph_isConnectedDivergent`), and `innerRaw_isProperForest` (body-378, off `W.toCarrierProperProvider`).

So `Closure` leaves the honest-residual list of body-400's `coassoc_gen_of_multiStar_constructions`: given a `Core` over
`W.toData`, `ResolvedMultiStarInnerRawCarrierClosureSupply Core` is constructed.

Per the HALT/guards: `Core.parentCD` is consumed as-is (NOT fed back into Core construction); `innerRaw_isProperForest`
does NOT alone yield membership (all three `iff` conjuncts are supplied); `W`'s carrier definition is not re-expanded
(only the body-426 `iff` is consumed); `recovered_raw_mem` is a SEPARATE ownership and untouched here.  No facade, no flat
term, no `forgetHopf`, no rep/perm, and NO strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-427 — a resolved subgraph, viewed as a standalone graph, is ambient-supported.**  Directly from the
subgraph's own endpoint-support fields; no Core, no de-contraction. -/
theorem resolvedAmbientSupported_of_subgraphGraph {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) :
    ResolvedAmbientSupported γ.toResolvedFeynmanGraph :=
  ⟨fun e he => γ.edges_supported e he, fun ℓ hℓ => γ.legs_supported ℓ hℓ⟩

/-- **R-6c-body-427 ∎ — the inner-raw carrier-closure supply, derived over `W`.**  For a de-contraction core over
`canonicalSupportedCarrierProperSupply.toData`, `innerRaw_mem` is a theorem: the body-426 `iff` reduces the parent-graph
membership to ambient support (parent subgraph) ∧ parent CD (`Core.parentCD`) ∧ inner-raw properness (body-378). -/
noncomputable def canonicalInnerRawCarrierClosureSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalSupportedCarrierProperSupply.toData) :
    ResolvedMultiStarInnerRawCarrierClosureSupply Core where
  innerRaw_mem := fun z δ => by
    refine (mem_canonicalSupportedCarrier_iff _).mpr
      ⟨resolvedAmbientSupported_of_subgraphGraph (Core.parent z δ), ?_, ?_⟩
    · rw [← ResolvedFeynmanSubgraph.forget_toFeynmanGraph (Core.parent z δ)]
      exact (Core.parent z δ).forget.toFeynmanGraph_isConnectedDivergent (Core.parentCD z δ)
    · exact innerRaw_isProperForest
        canonicalSupportedCarrierProperSupply.toCarrierProperProvider Core z δ

end GaugeGeometry.QFT.Combinatorial
