import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionRawNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedByTouched

/-!
# R-6c-body-430 — conjunct-5 witness pipeline, front half: quotient residual edge lifted to `G`; left exclusion (PROVED)

Four-hundred-and-thirtieth genuine-body step — banking the first half of the conjunct-5 (`0 < complementEdges.card`)
witness geometry for `regionRawUnion`, the LAST honest input of the carrier-closure bundle (body-429).  The key
correction (per the plan): **the quotient-side strict properness is NOT a new datum** — from
`P.carrier_isProperForest _ z.2.1 z.2.2` we already get `0 < z.2.1.complementEdges.card` as a theorem.  What remains is
pure separation geometry: lift that residual occurrence back to `G` and show the raw regions do not consume it.

The lift rides the definitional identity `contractWithStars_internalEdges` (a `rfl`):
`(z.1.1.contractWithStars (D.starOf G z.1.1)).internalEdges = z.1.1.complementEdges.map (z.1.1.retargetEdge …)`.

```text
0 < z.2.1.complementEdges.card                                        complementEdges_card_pos_of_isProperForest (already a theorem)
→ e_q ∈ z.2.1.complementEdges                                        quotientResidualEdge(_mem_complement)
→ e_q ∈ (z.1.1.contractWithStars …).internalEdges                    quotientResidualEdge_mem_ambient  (Multiset.sub_le)
   = z.1.1.complementEdges.map (z.1.1.retargetEdge …)                contractWithStars_internalEdges (rfl)
→ ∃ e ∈ z.1.1.complementEdges, retargetEdge e = e_q                   quotientResidualEdgePreimage(_mem_complement / _spec)  (Multiset.mem_map)
```

Front-half theorems banked:
* `quotientResidualEdge` / `quotientResidualEdge_mem_complement` / `quotientResidualEdge_mem_ambient` — the residual
  quotient edge `e_q`, from `z.2.1`'s own proper-forest complement positivity;
* `quotientResidualEdgePreimage` / `quotientResidualEdgePreimage_mem_complement` / `quotientResidualEdgePreimage_spec` —
  its `G`-level preimage `e ∈ z.1.1.complementEdges` with `retargetEdge e = e_q`.

Left exclusion primitive:
* `leftRegion_elements_subset` / `leftRegion_internalEdges_le` — `leftRegion` is a sub-forest of the outer `z.1.1`
  (`filterElements`), so its internal edges are a sub-multiset of `z.1.1.internalEdges`; since `e ∈ z.1.1.complementEdges
  = G.internalEdges - z.1.1.internalEdges`, the left region cannot over-consume `e`'s occurrence (assembled in body-431).

## Multiset guard (respected)

Per the plan, this body does NOT collapse to a bare `e ∉ raw.internalEdges`, which is false at duplicate occurrences.
The residual is carried as membership in the *difference* multiset `z.2.1.complementEdges` (= a `count`-positive fact),
and the left bound is a sub-multiset inequality `leftRegion.internalEdges ≤ z.1.1.internalEdges` — both `count`-safe.
The right/forest exclusions and the `count e raw < count e G → 0 < complementEdges.card` assembly are body-431.

Per the HALT/guards: the quotient strict properness is consumed as the already-proved
`complementEdges_card_pos_of_isProperForest`, NOT reintroduced as a datum; no bare `∉ internalEdges` is asserted (the
Multiset guard); q-local `EdgeIdsUnique` / retarget-injectivity are deferred to the right/forest exclusions (body-431) and
will be cited as the existing `Ids` gate, not a new datum.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
strict `star_mapPerm` / `promote_collapse` / singleton / floor-297.
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

/-! ### The residual quotient edge `e_q` (from `z.2.1`'s own proper-forest complement positivity). -/

/-- **R-6c-body-430 — the residual quotient edge.**  `z.2.1` is a proper forest of the quotient graph (carrier member
`z.2.2`), so its complement is nonempty; `e_q` is a chosen residual occurrence. -/
noncomputable def quotientResidualEdge (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) : ResolvedFeynmanEdge :=
  (Multiset.card_pos_iff_exists_mem.mp
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (P.carrier_isProperForest _ z.2.1 z.2.2))).choose

/-- **R-6c-body-430 — `e_q` lies in `z.2.1`'s (quotient) complement.** -/
theorem quotientResidualEdge_mem_complement (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) :
    quotientResidualEdge P z ∈ z.2.1.complementEdges :=
  (Multiset.card_pos_iff_exists_mem.mp
    (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest
      (P.carrier_isProperForest _ z.2.1 z.2.2))).choose_spec

/-- **R-6c-body-430 — `e_q` lies in the quotient ambient's internal edges.**  Its complement is a sub-multiset of the
ambient internal edges (`Multiset.sub_le`), so the residual occurrence is an ambient occurrence. -/
theorem quotientResidualEdge_mem_ambient (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) :
    quotientResidualEdge P z ∈ (z.1.1.contractWithStars (D.starOf G z.1.1)).internalEdges := by
  have h : quotientResidualEdge P z ∈
      (z.1.1.contractWithStars (D.starOf G z.1.1)).internalEdges - z.2.1.internalEdges :=
    quotientResidualEdge_mem_complement P z
  exact Multiset.mem_of_le tsub_le_self h

/-! ### The `G`-level preimage `e` of `e_q` (the retarget correspondence, `rfl`-backed). -/

/-- **R-6c-body-430 — `e_q` is a retarget image of an outer complement edge.**  The quotient internal edges are exactly
`z.1.1.complementEdges.map (retargetEdge …)` (`contractWithStars_internalEdges`, a `rfl`). -/
theorem quotientResidualEdge_mem_ambient_map (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) :
    quotientResidualEdge P z ∈
      z.1.1.complementEdges.map (z.1.1.retargetEdge (D.starOf G z.1.1)) := by
  have h := quotientResidualEdge_mem_ambient P z
  rwa [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at h

/-- **R-6c-body-430 — the `G`-level preimage `e` of the residual quotient edge.**  A chosen outer complement edge whose
retarget is `e_q`. -/
noncomputable def quotientResidualEdgePreimage (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) : ResolvedFeynmanEdge :=
  (Multiset.mem_map.mp (quotientResidualEdge_mem_ambient_map P z)).choose

/-- **R-6c-body-430 — the preimage lies in the outer complement.**  `e ∈ z.1.1.complementEdges`
(`= G.internalEdges - z.1.1.internalEdges`). -/
theorem quotientResidualEdgePreimage_mem_complement (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) :
    quotientResidualEdgePreimage P z ∈ z.1.1.complementEdges :=
  (Multiset.mem_map.mp (quotientResidualEdge_mem_ambient_map P z)).choose_spec.1

/-- **R-6c-body-430 — the preimage retargets to `e_q`.**  `retargetEdge e = e_q`. -/
theorem quotientResidualEdgePreimage_spec (P : ResolvedCarrierProperProvider D)
    (z : ForestBlockCodType D G) :
    z.1.1.retargetEdge (D.starOf G z.1.1) (quotientResidualEdgePreimage P z)
      = quotientResidualEdge P z :=
  (Multiset.mem_map.mp (quotientResidualEdge_mem_ambient_map P z)).choose_spec.2

/-! ### Left exclusion primitive (`leftRegion` is a sub-forest of the outer). -/

/-- **R-6c-body-430 — `leftRegion`'s components are outer components.**  `leftRegion = z.1.1.filterElements …`. -/
theorem leftRegion_elements_subset (z : ForestBlockCodType D G) :
    (leftRegion z).elements ⊆ z.1.1.elements := by
  show (z.1.1.filterElements (fun A => ¬ representedByTouched z A)).elements ⊆ z.1.1.elements
  rw [ResolvedAdmissibleSubgraph.filterElements_elements]
  exact Finset.filter_subset _ _

/-- **R-6c-body-430 — `leftRegion`'s internal edges are a sub-multiset of the outer's.**  So the left region cannot
over-consume `e`'s occurrence: `e ∈ z.1.1.complementEdges = G.internalEdges - z.1.1.internalEdges`, and
`leftRegion.internalEdges ≤ z.1.1.internalEdges` (assembled in body-431). -/
theorem leftRegion_internalEdges_le (z : ForestBlockCodType D G) :
    (leftRegion z).internalEdges ≤ z.1.1.internalEdges :=
  Finset.sum_le_sum_of_subset (leftRegion_elements_subset z)

end GaugeGeometry.QFT.Combinatorial
