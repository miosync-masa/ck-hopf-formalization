import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRealSupportedW

/-!
# R-6c-body-426 — the supported `W` carrier membership API (PROVED)

Four-hundred-and-twenty-sixth genuine-body step — turning body-425's constructed inhabitant
`canonicalSupportedCarrierProperSupply` from "exists" into "usable downstream".  Its carrier is a two-stage emptying
(ambient support — body-413 — over ambient connected-divergence — body-418 — over the saturated `IsProperForest` index —
body-415).  This body exposes that stack as a single membership `iff`, so a `body-400`-chain consumer can read off the
three conditions without unfolding the emptyings.

* `mem_canonicalSupportedCarrier_iff` — `A ∈ (…index G).carrier ↔ ResolvedAmbientSupported G ∧
  G.forget.IsConnectedDivergent ∧ A.IsProperForest`;
* `canonicalSupportedCarrier_ambientSupported` / `canonicalSupportedCarrier_ambientCD` — the two `.mp` accessors that are
  NOT already an index projection (properness is already `(…index G).mem_proper`).

Per the HALT/guards: NO `IsProperForest → membership` shortcut (membership always also yields support + ambient CD); NO
strict `star_mapPerm`; NO global `Finset.univ` instance (the `letI` finiteness of body-415 is used, not registered); the
`DecidableEq` handling stays at `Finset.mem_filter` level.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-426 ∎ — the supported `W` carrier membership criterion.**  A forest is in the constructed canonical
carrier iff the ambient graph is support-well-formed AND connected-divergent AND the forest is proper — the two-stage
emptying (support · CD) over the saturated proper index, read off as one condition. -/
theorem mem_canonicalSupportedCarrier_iff {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) :
    A ∈ (canonicalSupportedCarrierProperSupply.index G).carrier
      ↔ ResolvedAmbientSupported G ∧ G.forget.IsConnectedDivergent ∧ A.IsProperForest := by
  show A ∈ (canonicalResolvedCarrierProperRawSupply.supportedIndex G).carrier ↔ _
  rw [ResolvedCanonicalCarrierProperRawSupply.supportedIndex_carrier]
  by_cases hs : ResolvedAmbientSupported G
  · rw [if_pos hs]
    show A ∈ (cdSupportedIndex G).carrier ↔ _
    rw [cdSupportedIndex_carrier]
    by_cases hcd : G.forget.IsConnectedDivergent
    · rw [if_pos hcd]
      simp only [saturatedProperForestIndex, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => ⟨hs, hcd, h⟩, fun h => h.2.2⟩
    · rw [if_neg hcd]
      simp only [Finset.notMem_empty, false_iff, not_and]
      exact fun _ h => absurd h hcd
  · rw [if_neg hs]
    simp only [Finset.notMem_empty, false_iff, not_and]
    exact fun h => absurd h hs

/-- **R-6c-body-426 — a carrier member's ambient graph is support-well-formed.** -/
theorem canonicalSupportedCarrier_ambientSupported {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalSupportedCarrierProperSupply.index G).carrier) :
    ResolvedAmbientSupported G :=
  ((mem_canonicalSupportedCarrier_iff A).mp hA).1

/-- **R-6c-body-426 — a carrier member's ambient graph is connected-divergent.** -/
theorem canonicalSupportedCarrier_ambientCD {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G}
    (hA : A ∈ (canonicalSupportedCarrierProperSupply.index G).carrier) :
    G.forget.IsConnectedDivergent :=
  ((mem_canonicalSupportedCarrier_iff A).mp hA).2.1

/-! ## What `W` supplies to the body-400 chain

Body-400's `coassoc_gen_of_multiStar_constructions` takes, among its inputs, `D`, `CarrierProper`, `Fstar`, and (inside
its `Core`/`Closure` bundles) a `ResolvedCarrierAmbientSupportSupply`.  All four are now `W`-derived: `D := W.toData`,
`CarrierProper := W.toCarrierProperProvider`, and the two below.  The remaining inputs (`VBuild`, `CoreBuild`, `Ids`,
`StarProm`, `StarRaw`, `OccRaw`, `Split`, `rep*`) are value-geometry / concrete-model obligations, NOT carrier-root
facts, and stay honest residuals. -/

/-- **R-6c-body-426 — `W` supplies the canonical star facts.**  `W.toData.starOf` is `resolvedComponentFreshStar`
(body-414), which is fresh and injective; NO strict `star_mapPerm`. -/
def canonicalStarFactsOfW :
    ResolvedCanonicalStarFacts canonicalSupportedCarrierProperSupply.toData where
  starOf_fresh := fun G' A η _ => resolvedComponentFreshStar_not_mem_vertices G' A η
  starOf_injective := fun G' A => resolvedComponentFreshStar_injective_on_elements G' A

/-- **R-6c-body-426 — `W` supplies the carrier-ambient support gate.**  Carrier membership yields
`ResolvedAmbientSupported`, whose conjuncts are the edge/leg support (this is the body-426 `iff` at work; it is NOT
reverse-engineered from properness). -/
def ambientSupportOfW :
    ResolvedCarrierAmbientSupportSupply canonicalSupportedCarrierProperSupply.toData where
  edges_supported_of_mem := fun hA => (canonicalSupportedCarrier_ambientSupported hA).1
  legs_supported_of_mem := fun hA => (canonicalSupportedCarrier_ambientSupported hA).2

end GaugeGeometry.QFT.Combinatorial
