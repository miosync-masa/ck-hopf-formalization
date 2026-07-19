import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSubgraphMapPermEquiv
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupportedCarrierEmptying

/-!
# R-6c-body-418 — ambient-CD emptying: the second orthogonal carrier filter (PROVED)

Four-hundred-and-eighteenth genuine-body step — the connected-divergence (CD) emptying, orthogonal to body-402's
ambient-SUPPORT emptying.  The raw-`W` `hCD` field needs the ambient graph to be connected-divergent; on a non-CD ambient
the carrier is emptied.  This body lands the CD-emptied index and its `mapPerm`-naturality, and — crucially — recovers the
ambient CD from carrier MEMBERSHIP (never from `IsProperForest`), keeping the two filters orthogonal.

The ambient-CD predicate is exactly the flat graph-level `G.forget.IsConnectedDivergent` — which BUNDLES
`WellFormed ∧ IsConnected ∧ IsOnePI ∧ IsDivergent`, precisely the three facts the flat forest-contraction CD derivation
(`admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation`) consumes — and it already carries a `mapPerm`-iff.

* `resolvedAmbientCD_mapPerm_iff` — `(G.mapPerm σ).forget.IsConnectedDivergent ↔ G.forget.IsConnectedDivergent`
  (`forget_mapPerm` + `FeynmanGraph.mapPerm_isConnectedDivergent_iff`);
* `cdSupportedIndex` — `saturatedProperForestIndex` on a CD ambient, `∅` otherwise;
* `ambientCD_of_mem_cdSupportedIndex` — membership recovers the ambient CD (the honest recovery for `hCD`);
* `cdSupportedIndex_carrier_mapPerm` — both `if`-branches synchronised (CD-branch via body-417, `∅`-branch via
  `image_empty`).

**HALT / the remaining obligation.**  The raw-`W` `hCD` field itself is NOT built here.  From `ambientCD_of_mem_…` the
ambient CD is in hand, but concluding `(A.contractWithStars (canonicalResolvedStarAllocator.starOf G A)).forget.toClass.
IsConnectedDivergent` requires MATCHING the RESOLVED star-contraction (body-414's fresh allocator) to the FLAT
`admissibleForestContractGraphWithStars (G.forget) (A.forget) (admissibleForestCanonicalStarOf …)` at the class level
(`forget_contractWithStars` + fresh-star interchange via `IsIsoInvariantDivergence` + `A.forget ∈
properDisjointAdmissibleDivergentSubgraphs` from `A.IsProperForest`).  That resolved↔flat matching is body-419; the RawW
record assembly + connection to bodies 414/413 (real supported `W`) follow it.  No facade, no flat term, no `forgetHopf`,
no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-418 — the ambient-CD predicate is `mapPerm`-invariant.** -/
theorem resolvedAmbientCD_mapPerm_iff {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) :
    (G.mapPerm σ).forget.IsConnectedDivergent ↔ G.forget.IsConnectedDivergent := by
  rw [ResolvedFeynmanGraph.forget_mapPerm]
  exact FeynmanGraph.mapPerm_isConnectedDivergent_iff σ G.forget

/-- **R-6c-body-418 — the connected-divergence-emptied index.**  `saturatedProperForestIndex` on a CD ambient, `∅`
otherwise (orthogonal to body-402's ambient-support emptying). -/
noncomputable def cdSupportedIndex (G : ResolvedFeynmanGraph) : ResolvedProperForestFiniteIndex G where
  carrier := if G.forget.IsConnectedDivergent then (saturatedProperForestIndex G).carrier else ∅
  mem_proper := by
    intro A hA
    by_cases h : G.forget.IsConnectedDivergent
    · rw [if_pos h] at hA; exact (saturatedProperForestIndex G).mem_proper A hA
    · rw [if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

@[simp] theorem cdSupportedIndex_carrier (G : ResolvedFeynmanGraph) :
    (cdSupportedIndex G).carrier
      = if G.forget.IsConnectedDivergent then (saturatedProperForestIndex G).carrier else ∅ := rfl

/-- **R-6c-body-418 — carrier membership recovers the ambient CD.**  The honest recovery for `hCD`: the ambient CD comes
from the `if`-branch, NOT reverse-engineered from `IsProperForest` (the two filters stay orthogonal). -/
theorem ambientCD_of_mem_cdSupportedIndex {G : ResolvedFeynmanGraph}
    {A : ResolvedAdmissibleSubgraph G} (hA : A ∈ (cdSupportedIndex G).carrier) :
    G.forget.IsConnectedDivergent := by
  by_cases h : G.forget.IsConnectedDivergent
  · exact h
  · rw [cdSupportedIndex_carrier, if_neg h] at hA; exact absurd hA (Finset.notMem_empty A)

/-- **R-6c-body-418 ∎ — the CD-emptied index is `mapPerm`-natural.**  Both `if`-branches synchronise: the CD-branch via
body-417's `saturatedProperForestIndex_carrier_mapPerm`, the `∅`-branch via `Finset.image_empty`. -/
theorem cdSupportedIndex_carrier_mapPerm {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId) :
    (cdSupportedIndex (G.mapPerm σ)).carrier
      = ((cdSupportedIndex G).carrier).image (fun A => A.mapPerm σ) := by
  rw [cdSupportedIndex_carrier, cdSupportedIndex_carrier]
  by_cases h : G.forget.IsConnectedDivergent
  · rw [if_pos ((resolvedAmbientCD_mapPerm_iff σ).mpr h), if_pos h]
    convert saturatedProperForestIndex_carrier_mapPerm σ using 2
  · rw [if_neg (fun hs => h ((resolvedAmbientCD_mapPerm_iff σ).mp hs)), if_neg h,
      Finset.image_empty]

end GaugeGeometry.QFT.Combinatorial
