import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTOFPreimageAlignment
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarDecontraction

/-!
# R-6c-body-438 — the forest region count-exclusion (PROVED)

Four-hundred-and-thirty-eighth genuine-body step — pure `count` arithmetic now that body-437 folded the forest-specific
type/choice/alignment into a support-local `map_congr`.

* `quotientEdgePreimage_count_eq_whole` — the named preimage transport: `count e Q = count e_q δ.internalEdges`, in the
  fixed order `count e Q = count (wholeRetarget e) (Q.map wholeRetarget)` (body-436 domain-widened `InjOn`, with
  `e ∈ G.internalEdges` from body-431 and `Q ≤ G.internalEdges` from `quotientEdgePreimage_le`), `= count e_q (Q.map
  wholeRetarget)` (`quotientResidualEdgePreimage_spec`), `= count e_q δ.internalEdges` (body-437 `map_whole`).
* `forestRegion_component_count_lt` — the forest count-exclusion, assembled from body-435's backbone:
  ```text
  count e parent.internalEdges = count e TOF.internalEdges + count e Q                 (435 decomposition)
    = count e TOF.internalEdges + count e_q δ.internalEdges                             (transport above)
    ≤ count e outer.internalEdges + count e_q z.2.1.internalEdges                        (435 touched + δ ⊆ z.2.1)
    < count e outer.internalEdges + count e_q quotientAmbient.internalEdges              (431 quotient residual strict)
    = count e outer.internalEdges + count e outer.complementEdges                        (433 residual transport)
    = count e G.internalEdges                                                            (435 ledger)
  ```

Per the HALT/guards: everything stays in `count` (no `∉`); all `e_q` / `wholeRetarget e` / count expressions are
explicitly rewritten before `omega` so atoms unify (the body-434 key); the region counts are not added across regions
here (raw-owner classification is the final assembly).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-438 — the quotient-edge-preimage count transport.**  The whole-outer retarget carries the residual
preimage's count in `Q` onto `e_q`'s count in `δ`. -/
theorem quotientEdgePreimage_count_eq_whole (F : ResolvedCanonicalStarFacts D)
    (hId : G.EdgeIdsUnique) (P : ResolvedCarrierProperProvider D) (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1))) :
    Multiset.count (quotientResidualEdgePreimage P z)
        (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ))
      = Multiset.count (quotientResidualEdge P z) δ.internalEdges := by
  have hQG : quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
      ≤ G.internalEdges := by
    refine le_trans (quotientEdgePreimage_le _ _ _) ?_
    rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self
  rw [← count_map_eq_count_of_injOn_mem
      (S := {x : ResolvedFeynmanEdge | x ∈ G.internalEdges})
      (ResolvedAdmissibleSubgraph.retargetEdge_injOn_internalEdges hId z.1.1 (D.starOf G z.1.1))
      (fun a ha => Multiset.mem_of_le hQG ha)
      (ResolvedAdmissibleSubgraph.mem_internalEdges_of_mem_complementEdges
        (quotientResidualEdgePreimage_mem_complement P z)),
    quotientResidualEdgePreimage_spec P z, quotientEdgePreimage_map_whole F z δ]

/-- **R-6c-body-438 ∎ — the forest region count-exclusion.**  A `forestRegion` owner component carrying the body-430
residual preimage `e` counts it strictly less than the ambient `G` does. -/
theorem forestRegion_component_count_lt (F : ResolvedCanonicalStarFacts D)
    (hId : G.EdgeIdsUnique) (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (z : ForestBlockCodType D G)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (forestRegion M F z).elements)
    (he : quotientResidualEdgePreimage P z ∈ A.internalEdges) :
    Multiset.count (quotientResidualEdgePreimage P z) A.internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges := by
  rw [forestRegion_elements] at hA
  obtain ⟨δ, -, hδ_eq⟩ := Finset.mem_image.mp hA
  subst hδ_eq
  have hdec : Multiset.count (quotientResidualEdgePreimage P z) (M.parent z δ).internalEdges
      = Multiset.count (quotientResidualEdgePreimage P z) (touchedOuterForest z δ.1).internalEdges
        + Multiset.count (quotientResidualEdgePreimage P z)
            (quotientEdgePreimage (touchedOuterForest z δ.1) (D.starOf G z.1.1)
              (touchedLocalComponent z δ.1)) :=
    localizedParentWithTouchedLegs_count_internalEdges z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) _
  have h438a := quotientEdgePreimage_count_eq_whole F hId P z δ.1
  have h_touched := touchedOuterForest_count_internalEdges_le z δ.1 (quotientResidualEdgePreimage P z)
  have hδz21 : δ.1 ∈ z.2.1.elements := (Finset.mem_filter.mp δ.2).1
  have h_δcount : Multiset.count (quotientResidualEdge P z) δ.1.internalEdges
      ≤ Multiset.count (quotientResidualEdge P z) z.2.1.internalEdges :=
    Multiset.count_le_of_le _ (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hδz21)
  have h_strict := ResolvedAdmissibleSubgraph.count_lt_of_mem_complementEdges
    (quotientResidualEdge_mem_complement P z)
  have h_transport := ResolvedAdmissibleSubgraph.count_complementEdges_eq_count_contractWithStars hId z.1.1
    (D.starOf G z.1.1) (quotientResidualEdgePreimage_mem_complement P z)
  rw [quotientResidualEdgePreimage_spec P z] at h_transport
  have h_ledger := ResolvedAdmissibleSubgraph.count_internalEdges_add_complementEdges z.1.1
    (quotientResidualEdgePreimage P z)
  rw [hdec, h438a]
  omega

end GaugeGeometry.QFT.Combinatorial
