import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedRemnantSupplyBuild
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor

/-!
# R-6c-body-467 — the corrected survivor/remnant cross-disjointness (`hcross` GEOMETRY → THEOREM) (PROVED)

Four-hundred-and-sixty-seventh genuine-body step — the right survivor and the corrected remnant are disjoint, and the
`ResolvedQuotientForestCrossSupply` assembled from it.  The component-level cross is UNCONDITIONAL — the V-level `hcross`'s
supplied `γ ≠ δ` is DISCARDED.

* `correctedRightSurvivor_remnant_disjoint` — a right-survivor component (vertices `r.1.1.vertices`) is disjoint from a
  corrected remnant component (`(o.γ.vertices \ o.B.vertices) ∪ promoted-star vertices`) via a two-way vertex split:
  the local-survivor case is `s.1.1.pairwiseDisjoint` (`r` is right-primitive, `o.γ` is a forest choice, so distinct
  components — `not_isForestChoice_of_isRightPrimitive`); the promoted-star case is `Fstar.starOf_fresh` (`∉ G.vertices`)
  against `r.1.1.vertices_subset`;
* `canonicalCorrectedQuotientForestCrossSupply` — `survivor := survivorSupply_of_measure`,
  `remnant := canonicalCorrectedRemnantComponentSupply`, `cross := ` the theorem (recovering `r` / the forest occurrence
  from `rightSurvivorForest_elements` / `remnantForest_elements`, discarding the supplied `≠`).

Ownership: the component-level cross geometry is `Measure + Fstar` ONLY; `CarrierProper` is used SOLELY to assemble the
`canonicalCorrectedRemnantComponentSupply` record; body-464's remnant/remnant disjointness is NOT reused for the cross.

Per the HALT/guards: `hRdisj` / `quotient_mem` / `quot_eq` are NOT touched — family quotient ownership stays a separate
front; strict `StarProm` / `InnerStarRaw` NOT used; body-445 stays a valid conditional.  NOT the unconditional theorem.
No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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
set_option maxHeartbeats 1600000

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  (Fstar : ResolvedCanonicalStarFacts D)

/-- **R-6c-body-467 ∎ — the corrected survivor/remnant component cross-disjointness** (UNCONDITIONAL). -/
theorem correctedRightSurvivor_remnant_disjoint
    (Measure : ResolvedMeasureLeafSupply D) (s : ResolvedCoassocSplitChoice D G)
    (r : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents})
    (o : s.ForestChoiceOccurrence) :
    ((survivorSupply_of_measure Measure G).survivorComponent s r).Disjoint
      ((canonicalCorrectedRemnantReembedSupply s Fstar).correctedRemnantComponent o) := by
  have hr : s.isRightPrimitive r.1 := (Finset.mem_filter.mp r.2).2
  have hne : r.1.1 ≠ o.γ.1 := fun h =>
    s.not_isForestChoice_of_isRightPrimitive hr
      (by rw [show r.1 = o.γ from Subtype.ext h]; exact ⟨o.B, o.hchoice⟩)
  rw [ResolvedFeynmanSubgraph.Disjoint, correctedRemnantComponent_vertices_eq_promoted s o Fstar,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices,
    ResolvedFeynmanSubgraph.toResolvedFeynmanGraph_vertices, Finset.disjoint_left]
  intro v hv hv'
  have hvr : v ∈ r.1.1.vertices := hv
  rw [Finset.mem_union] at hv'
  rcases hv' with hvL | hvR
  · rw [Finset.mem_sdiff] at hvL
    exact Finset.disjoint_left.mp (s.1.1.pairwiseDisjoint r.1.2 o.γ.2 hne) hvr hvL.1
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hvR
    obtain ⟨b, hb, rfl⟩ := hvR
    exact Fstar.starOf_fresh G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
      (o.γ.1.promote b) (promote_mem_selectedOuterRawOf_raw s o hb) (r.1.1.vertices_subset hvr)

/-- **R-6c-body-467 ∎ — the corrected quotient-forest cross supply.**  Survivor + corrected remnant + the unconditional
cross-disjointness (the supplied `≠` is discarded). -/
noncomputable def canonicalCorrectedQuotientForestCrossSupply
    (Measure : ResolvedMeasureLeafSupply D) (CarrierProper : ResolvedCarrierProperProvider D) :
    ResolvedQuotientForestCrossSupply D G where
  survivor := survivorSupply_of_measure Measure G
  remnant := canonicalCorrectedRemnantComponentSupply Fstar CarrierProper
  cross := fun s => by
    intro δ hδ δ' hδ' _
    rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hδ
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hδ'
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hδ
    obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ'
    exact correctedRightSurvivor_remnant_disjoint Fstar Measure s r (s.forestComponentOccurrence γ)

end GaugeGeometry.QFT.Combinatorial
