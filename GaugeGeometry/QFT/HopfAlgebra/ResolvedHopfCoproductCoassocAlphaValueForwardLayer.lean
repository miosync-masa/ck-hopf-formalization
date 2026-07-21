import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaNativeFilteredValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocValueQuotientRegionSplit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientMemValue

/-!
# R-6c-body-472 — the parallel alpha value forward layer (first-layer PARALLEL MIGRATION)

Four-hundred-and-seventy-second genuine-body step — the FIRST downstream layer landed as a PARALLEL alpha declaration
(NOT an in-place retype of the 71-file chain, which would break everything at once).  Only the DIRECT-`q` consumers
(those taking a filtered `q` directly) are migrated; the boundary is the generic recovered `z` layer, which needs the
body-473 raw→filtered membership threading.

* `ResolvedForwardQuotientMemAlphaValueSupply` / `forwardQuotientMemAlphaValueOfValue` — the forward quotient membership,
  FREE (`Finset.mem_attach`), over the body-470 filtered `V` and `fwdMapFilteredAlphaValue`;
* `ResolvedAlphaValueQuotientRegionSplitSupply` — the survivor/remnant region split (`survivor_avoids` /
  `remnant_touches`) over the alpha `V`, with the quotient/region membership theorems (`mem_quotient_iff_alpha`,
  `rightDomain_value_mem_alpha`, `forestDomain_value_mem_alpha`) using `V.quotientForestRaw q` / `V.union_eq q` (NEVER
  restricted to `q.1`);
* `forwardQuotientMemAlphaValueOfValue_toFiltered` — the legacy `rfl` compatibility (the alpha membership over the
  body-471 legacy adapter agrees with the value forward map).

Recovered boundary (PINNED, OPEN): a generic `recoveredPreimageValue z : ResolvedCoassocSplitChoice D G` alone cannot feed
`V.quotientForestRaw` — that needs `⟨recoveredPreimageValue z, recoveredPreimageValue_mem z⟩ : FilteredForestBlockDom D G`,
a proof-threading landed in body-473 (NO fabricated choice / Classical membership here).

Per the HALT/guards: the `ForwardQuotientValueGeometry`-style recovered-preimage layer is NOT entered; old structures are
NOT edited in place; the 71-file migration is NOT started; NO new geometry, NO `quot_eq`, NO `W'` five conditions; strict
`StarProm` / `InnerStarRaw` NOT restored; body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-472 — the forward quotient membership over the alpha value root.** -/
structure ResolvedForwardQuotientMemAlphaValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- `fwdMapFilteredAlphaValue`'s quotient forest is a carrier forest of the quotient graph. -/
  quotient_mem : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (fwdMapFilteredAlphaValue F V q).2
      ∈ (D.supply ((fwdMapFilteredAlphaValue F V q).1.1.contractWithStars
          (D.starOf G (fwdMapFilteredAlphaValue F V q).1.1))).forestCarrier

/-- **R-6c-body-472 — the forward quotient membership, FREE.**  `Finset.mem_attach`. -/
noncomputable def forwardQuotientMemAlphaValueOfValue (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) :
    ResolvedForwardQuotientMemAlphaValueSupply F V where
  quotient_mem := fun {_G} q => Finset.mem_attach _ (fwdMapFilteredAlphaValue F V q).2

/-- **R-6c-body-472 — the alpha value quotient/region split supply.** -/
structure ResolvedAlphaValueQuotientRegionSplitSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedFilteredConcreteSummandValueSupply D) where
  /-- Every survivor component avoids the value outer star. -/
  survivor_avoids : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ∀ δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements,
      Disjoint δ.vertices (starOfZ (fwdMapFilteredAlphaValue F V q))
  /-- Every remnant component touches the value outer star. -/
  remnant_touches : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    ∀ δ ∈ (V.Remnant.remnant.remnantForest q.1).elements,
      ¬ Disjoint δ.vertices (starOfZ (fwdMapFilteredAlphaValue F V q))

namespace ResolvedAlphaValueQuotientRegionSplitSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-472 — the alpha quotient membership splits as survivor ∨ remnant** (from `V.union_eq q`). -/
theorem mem_quotient_iff_alpha {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ (fwdMapFilteredAlphaValue F V q).2.1.elements
      ↔ δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements
        ∨ δ ∈ (V.Remnant.remnant.remnantForest q.1).elements := by
  change δ ∈ (V.quotientForestRaw q).1.elements ↔ _
  rw [V.union_eq q, ResolvedAdmissibleSubgraph.union_elements]
  exact @Finset.mem_union _ (Classical.decEq _) _ _ _

/-- **R-6c-body-472 — `rightDomain` ↔ survivor** at the alpha value root. -/
theorem rightDomain_value_mem_alpha (P : ResolvedAlphaValueQuotientRegionSplitSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ rightDomain (fwdMapFilteredAlphaValue F V q) ↔
      δ ∈ (V.Survivor.survivor.rightSurvivorForest q.1).elements := by
  unfold rightDomain
  constructor
  · intro h
    obtain ⟨hmem, hdisj⟩ := Finset.mem_filter.mp h
    rcases (mem_quotient_iff_alpha q δ).mp hmem with hs | hr
    · exact hs
    · exact absurd hdisj (P.remnant_touches q δ hr)
  · intro hs
    exact Finset.mem_filter.mpr ⟨(mem_quotient_iff_alpha q δ).mpr (Or.inl hs), P.survivor_avoids q δ hs⟩

/-- **R-6c-body-472 ∎ — `forestDomain` ↔ remnant** at the alpha value root. -/
theorem forestDomain_value_mem_alpha (P : ResolvedAlphaValueQuotientRegionSplitSupply F V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (δ : ResolvedFeynmanSubgraph (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)) :
    δ ∈ forestDomain (fwdMapFilteredAlphaValue F V q) ↔
      δ ∈ (V.Remnant.remnant.remnantForest q.1).elements := by
  unfold forestDomain
  constructor
  · intro h
    obtain ⟨hmem, hdisj⟩ := Finset.mem_filter.mp h
    rcases (mem_quotient_iff_alpha q δ).mp hmem with hs | hr
    · exact absurd (P.survivor_avoids q δ hs) hdisj
    · exact hr
  · intro hr
    exact Finset.mem_filter.mpr ⟨(mem_quotient_iff_alpha q δ).mpr (Or.inr hr), P.remnant_touches q δ hr⟩

end ResolvedAlphaValueQuotientRegionSplitSupply

/-- **R-6c-body-472 — the legacy `rfl` compatibility.**  The alpha forward-quotient membership over the body-471 legacy
adapter is `Finset.mem_attach` on the value forward map — the same regression anchor. -/
theorem forwardQuotientMemAlphaValueOfValue_toFiltered (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom D G) :
    (forwardQuotientMemAlphaValueOfValue F V.toFiltered).quotient_mem q
      = Finset.mem_attach _ (fwdMapFilteredValue F V q).2 :=
  rfl

end GaugeGeometry.QFT.Combinatorial
