import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocUniqueClosureMigration

/-!
# R-6c-body-444 — region-componentwise properness dispatch; `Ppos` and `Nne` eliminated; the pure carrier bundle (PROVED)

Four-hundred-and-forty-fourth genuine-body step — the second body-441 scope smell (the measure leaves) removed by
region-component dispatch.  Each component of the raw recovered-outer union is a left / right / forest component, and its
positivity / nonemptiness comes from the SOURCE proper forest (outer `z.1.1` or quotient `z.2.1`) plus containment — NOT
from a generic `cd_positiveInternalEdges` / `cd_nonempty` measure leaf.

* `regionRawUnion_hasPositiveInternalEdgesComponents` — left (outer properness), right (`rightReembed` data `rfl`,
  quotient properness), forest (a nonempty `touchedOuterComponents` witness `A` is outer-proper and — body-326 — its
  internal edges are contained in the parent, so the parent is positively edged);
* `regionRawUnion_hasNonemptyComponents` — the same dispatch on vertices (body-326 vertex containment);
* `regionRawUnion_isProperForest_of_complement_geom` — `IsProperForest` from ONLY the carrier-proper provider and the
  complement datum: conjuncts 1 (body-429) / 2 / 4 (this body) / 3 (derived) / 5 (`hCompl`) — no measure leaf;
* `canonicalUniquePureMultiStarCarrierClosureBundleSupply` — the `W'` carrier-closure bundle with **NO measure input**:
  `recovered_raw_mem` reads support / CD / id-uniqueness off the live block membership `z.1.2` and gets properness from
  the dispatch.  The bundle now takes only the value core.

So both body-441 scope smells are gone: id-uniqueness (body-443) and the measure leaves (this body) are all
`W'`-derived; the carrier bundle is a **pure geometry theorem**.

Per the HALT/guards: generic `cd_positiveInternalEdges` / `cd_nonempty` are NOT used; the forest parent's carrier
membership is NOT assumed; positivity/nonemptiness come only from source outer/quotient properness and body-326
containment; no forward identity / round-trip.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO strict
`star_mapPerm` / `promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-444 — componentwise positive internal edges, from source properness.** -/
theorem regionRawUnion_hasPositiveInternalEdgesComponents (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) :
    (regionRawUnion M F z).HasPositiveInternalEdgesComponents := by
  intro γ hγ
  simp only [regionRawUnion, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hγ
  rcases hγ with (hl | hr) | hf
  · exact ResolvedAdmissibleSubgraph.hasPositiveInternalEdgesComponents_of_isProperForest
      (P.carrier_isProperForest _ z.1.1 z.1.2) γ (leftRegion_elements_subset z hl)
  · rw [rightRegion_elements] at hr
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hr
    show 0 < δ.1.internalEdges.card
    exact ResolvedAdmissibleSubgraph.hasPositiveInternalEdgesComponents_of_isProperForest
      (P.carrier_isProperForest _ z.2.1 z.2.2) δ.1 (Finset.mem_filter.mp δ.2).1
  · rw [forestRegion_elements] at hf
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨A, hA⟩ := touchedOuterComponents_nonempty z (Finset.mem_filter.mp δ.2).2
    have hApos : 0 < A.internalEdges.card :=
      ResolvedAdmissibleSubgraph.hasPositiveInternalEdgesComponents_of_isProperForest
        (P.carrier_isProperForest _ z.1.1 z.1.2) A (mem_touchedOuterComponents.mp hA).1
    exact lt_of_lt_of_le hApos (Multiset.card_le_card
      (touchedLegs_component_internalEdges_le (datum := M.legLift z δ) (hE := M.hE z) (hL := M.hL z) hA))

/-- **R-6c-body-444 — componentwise nonemptiness, from source properness.** -/
theorem regionRawUnion_hasNonemptyComponents (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) :
    (regionRawUnion M F z).HasNonemptyComponents := by
  intro γ hγ
  simp only [regionRawUnion, recoveredRawUnion, ResolvedAdmissibleSubgraph.union_elements,
    Finset.mem_union] at hγ
  rcases hγ with (hl | hr) | hf
  · exact ResolvedAdmissibleSubgraph.hasNonemptyComponents_of_isProperForest
      (P.carrier_isProperForest _ z.1.1 z.1.2) γ (leftRegion_elements_subset z hl)
  · rw [rightRegion_elements] at hr
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hr
    show 0 < δ.1.vertices.card
    exact ResolvedAdmissibleSubgraph.hasNonemptyComponents_of_isProperForest
      (P.carrier_isProperForest _ z.2.1 z.2.2) δ.1 (Finset.mem_filter.mp δ.2).1
  · rw [forestRegion_elements] at hf
    obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨A, hA⟩ := touchedOuterComponents_nonempty z (Finset.mem_filter.mp δ.2).2
    have hAne : A.IsNonempty :=
      ResolvedAdmissibleSubgraph.hasNonemptyComponents_of_isProperForest
        (P.carrier_isProperForest _ z.1.1 z.1.2) A (mem_touchedOuterComponents.mp hA).1
    show 0 < (M.parent z δ).vertices.card
    exact lt_of_lt_of_le hAne (Finset.card_le_card
      (touchedLegs_component_vertices_subset (datum := M.legLift z δ) (hE := M.hE z) (hL := M.hL z) hA))

/-- **R-6c-body-444 — `IsProperForest` for the raw recovered-outer union, from the carrier provider alone.**  No measure
leaf: conjunct 1 (body-429), conjuncts 2 / 4 (this body), conjunct 3 (derived from 1 + 4), conjunct 5 (`hCompl`). -/
theorem regionRawUnion_isProperForest_of_complement_geom (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (hCompl : 0 < (regionRawUnion M F z).complementEdges.card) :
    (regionRawUnion M F z).IsProperForest :=
  ⟨regionRawUnion_isNonempty P M F z,
   regionRawUnion_hasNonemptyComponents P M F z,
   (regionRawUnion M F z).internalEdges_card_pos_of_isNonempty (regionRawUnion_isNonempty P M F z)
     (regionRawUnion_hasPositiveInternalEdgesComponents P M F z),
   regionRawUnion_hasPositiveInternalEdgesComponents P M F z,
   hCompl⟩

/-- **R-6c-body-444 ∎ — the pure `W'` carrier-closure bundle.**  No measure input: `recovered_raw_mem` reads support / CD
/ id-uniqueness off the live block membership `z.1.2` and gets properness from the region dispatch.  The bundle takes
only the de-contraction value core. -/
noncomputable def canonicalUniquePureMultiStarCarrierClosureBundleSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply
      canonicalUniqueSupportedCarrierProperSupply.toData) :
    ResolvedMultiStarCarrierClosureBundleSupply Core canonicalUniqueStarFactsOfW' where
  Closure := canonicalUniqueInnerRawCarrierClosureSupply Core
  recovered_raw_mem := fun {G} z => by
    refine (mem_canonicalUniqueSupportedCarrier_iff _).mpr
      ⟨canonicalUniqueSupportedCarrier_ambientSupported z.1.2,
       canonicalUniqueSupportedCarrier_ambientCD z.1.2,
       edgeIdsUnique_of_carrier_mem z.1.2, legIdsUnique_of_carrier_mem z.1.2, ?_⟩
    exact regionRawUnion_isProperForest_of_complement_geom
      canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
      (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core))
      canonicalUniqueStarFactsOfW' z
      (regionRawUnion_complementEdges_card_pos_of_count_lt
        canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
        (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core))
        canonicalUniqueStarFactsOfW' z
        (regionRawUnion_count_lt canonicalUniqueStarFactsOfW' (edgeIdsUnique_of_carrier_mem z.1.2)
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          (Core.toDecontractionSupply (canonicalUniqueInnerRawCarrierClosureSupply Core)) z))

end GaugeGeometry.QFT.Combinatorial
