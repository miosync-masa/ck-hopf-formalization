import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientResidualLift

/-!
# R-6c-body-431 — the count-safe complement backbone; conjunct-5 positivity reduced to one witness bound (PROVED)

Four-hundred-and-thirty-first genuine-body step — banking the generic, `count`-safe backbone for the conjunct-5
(`0 < regionRawUnion.complementEdges.card`) closure, and cashing it into a single remaining witness obligation.

## Why count-safe, not `∉`

The plan floated a `not_mem_of_mem_complement_of_unique` (`e ∈ A.complementEdges → e ∉ A.internalEdges`).  That form is
**false on a general multiset** and, crucially, is NOT recovered from `EdgeIdsUnique` alone: `EdgeIdsUnique G` says edges
with equal `edgeId` are equal, which does not bound the *multiplicity* of a single edge (two identical occurrences share
an id and satisfy the predicate vacuously).  So `EdgeIdsUnique` does not give `Nodup G.internalEdges`, and the `∉` form
needs a genuine nodup hypothesis that is not freely available.  The flat development already reflects this — it stays in
`count` land (`ContractionPreservation.count_lt_of_mem_complementEdges`).  This body ports that honest primitive to the
resolved carrier and keeps the whole closure `count`-based, exactly honouring the body-430 Multiset guard.

## Banked backbone (generic, any resolved admissible subgraph)

* `mem_internalEdges_of_mem_complementEdges` — `e ∈ A.complementEdges → e ∈ G.internalEdges` (`Multiset.sub_le`);
* `count_lt_of_mem_complementEdges` — `e ∈ A.complementEdges → count e A.internalEdges < count e G.internalEdges`
  (`Multiset.count_sub` + `tsub_pos_iff_lt`);  the honest count-positive fact.
* `complementEdges_card_pos_of_count_lt` — the reverse assembly: a single witness `e` with
  `count e A.internalEdges < count e G.internalEdges` forces `0 < A.complementEdges.card`.

## Closure reduced to one witness bound

* `regionRawUnion_complementEdges_card_pos_of_count_lt` — for the raw recovered-outer union, `0 < complementEdges.card`
  follows from `count e regionRawUnion.internalEdges < count e G.internalEdges` at the body-430 witness
  `e := quotientResidualEdgePreimage P z`.  Composed with body-429's `regionRawUnion_isProperForest_of_complement` and
  `regionRawUnion_mem_canonicalSupportedCarrier_of_complement`, the entire `recovered_raw_mem` closure is now reduced to
  the SINGLE geometric obligation:

  ```text
  count (quotientResidualEdgePreimage P z) (regionRawUnion M F z).internalEdges
    < count (quotientResidualEdgePreimage P z) G.internalEdges
  ```

  which decomposes (per the plan) into the three region count-exclusions:
  - **left**  `count e leftRegion.internalEdges ≤ count e z.1.1.internalEdges` and `e ∈ z.1.1.complementEdges`
              (body-430 `leftRegion_internalEdges_le` + `count_lt_of_mem_complementEdges`);
  - **right** `e ∈ rightReembed δ.internalEdges → retargetEdge e = e_q ∈ δ.internalEdges ≤ z.2.1.internalEdges`,
              contradicting `e_q ∈ z.2.1.complementEdges` (retarget injectivity, the existing `Ids` gate);
  - **forest** `parent`-internal edges split into touched (`≤ z.1.1.internalEdges`) + quotient-edge preimage
              (maps to `δ.internalEdges`), both excluded by the two facts above.

  These three region count-bounds are the dedicated next body; every lemma here is generic and `count`-safe, so no
  Multiset multiplicity trap is introduced.

Per the HALT/guards: no `∉`/nodup shortcut is asserted (the `count` form is the honest primitive); `EdgeIdsUnique`'s real
role is the *retarget injectivity* used in the right/forest exclusions, cited as the existing `Ids` gate, NOT a new
datum; no forward-outer, identity, or cover.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO strict
`star_mapPerm` / `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

namespace ResolvedAdmissibleSubgraph

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-body-431 — a complement edge is an ambient internal edge.** -/
theorem mem_internalEdges_of_mem_complementEdges {A : ResolvedAdmissibleSubgraph G}
    {e : ResolvedFeynmanEdge} (he : e ∈ A.complementEdges) : e ∈ G.internalEdges := by
  have h : e ∈ G.internalEdges - A.internalEdges := he
  exact Multiset.mem_of_le tsub_le_self h

/-- **R-6c-body-431 — complement membership is a strict count fact.**  The honest count-safe primitive (resolved port of
the flat `count_lt_of_mem_complementEdges`): the edge occurs strictly more often in the ambient than in the subgraph. -/
theorem count_lt_of_mem_complementEdges {A : ResolvedAdmissibleSubgraph G}
    {e : ResolvedFeynmanEdge} (he : e ∈ A.complementEdges) :
    Multiset.count e A.internalEdges < Multiset.count e G.internalEdges := by
  have h0 : 0 < Multiset.count e (G.internalEdges - A.internalEdges) := Multiset.count_pos.mpr he
  rwa [Multiset.count_sub, tsub_pos_iff_lt] at h0

/-- **R-6c-body-431 — positivity of the complement from a single strict-count witness.**  If some edge occurs strictly
more often in the ambient than in `A`, the complement is nonempty. -/
theorem complementEdges_card_pos_of_count_lt {A : ResolvedAdmissibleSubgraph G}
    {e : ResolvedFeynmanEdge}
    (h : Multiset.count e A.internalEdges < Multiset.count e G.internalEdges) :
    0 < A.complementEdges.card := by
  refine Multiset.card_pos_iff_exists_mem.mpr ⟨e, ?_⟩
  show e ∈ G.internalEdges - A.internalEdges
  rw [← Multiset.count_pos, Multiset.count_sub]
  omega

end ResolvedAdmissibleSubgraph

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-431 ∎ — conjunct-5 positivity for `regionRawUnion`, reduced to one witness count bound.**  Given that
the body-430 residual preimage `e` occurs strictly more often in the ambient `G` than in the raw recovered-outer union,
the union's complement is nonempty — the last honest input of `regionRawUnion_isProperForest_of_complement` (body-429).
The remaining obligation is precisely the strict-count hypothesis, discharged by the three region count-exclusions
(dedicated next body). -/
theorem regionRawUnion_complementEdges_card_pos_of_count_lt
    (P : ResolvedCarrierProperProvider D)
    (M : ResolvedMultiStarDecontractionSupply D) (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (h : Multiset.count (quotientResidualEdgePreimage P z) (regionRawUnion M F z).internalEdges
      < Multiset.count (quotientResidualEdgePreimage P z) G.internalEdges) :
    0 < (regionRawUnion M F z).complementEdges.card :=
  ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_count_lt h

end GaugeGeometry.QFT.Combinatorial
