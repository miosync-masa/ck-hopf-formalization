import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaContractTwiceFieldAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPermExtensionConcrete

/-!
# R-6c-body-513 — canonical corrected whole-vertex correspondence + global `σ` (once) (PROVED)

Five-hundred-and-thirteenth genuine-body step — building body-512's global `starPerm` as the ONE finite extension of a
completed whole-vertex correspondence, NOT as a composition of per-remnant local permutations.  The three whole-graph
field equalities are deferred to the next body.

## The whole-vertex correspondence socket

`ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E` — per filtered `q`, the whole-vertex bijection
`ResolvedContractTwiceVertexCorrespondence G₁ G₂` between `G₁ := q`'s outer contract-with-stars (`branchRightGraph q.1`,
`rfl`) and `G₂ := ` the corrected quotient's contract-with-stars (`imageInnerRightGraph`, the body-512 socket's `G₂`).
This is the SOLE residual: its three cases (surviving vertices → identity, right-survivor stars → the right route,
corrected-remnant stars → the corrected family + body-464 disjointness/injectivity) — bodyied next.

## The global `σ`, once (this body)

`globalPermExtension` / `contractStarPerm` — the completed correspondence extended ONCE to a full `Equiv.Perm VertexId`
by the body-18 generic engine (`finsetSubtypePermExtension … |>.toVertexPermExtension`): its action off `G₁ ∪ G₂` is
irrelevant, and its orientation is `σ w = corr.invFun ⟨w, hw⟩` on `G₂.vertices`, `σ.symm v = corr.toFun ⟨v, hv⟩` on
`G₁.vertices`.  No local permutations are composed; the local `promotedStarCorrectingPerm o` is used only inside the
per-case correspondence proofs (the residual), never as a global factor.

This `contractStarPerm` is exactly body-512's `ResolvedCanonicalFilteredContractTwiceFieldSupply.starPerm`; the three
whole-graph field equalities (via the correspondence's `on_vertices` / `inv_on_vertices`) complete that socket — the
body-514 target.

Per the HALT/guards: `promotedStarCorrectingPerm` is NOT composed in Finset order; local perms' supports are NOT assumed
disjoint without proof; no equality between distinct local permutations is required; no `corrected = uncorrected` graph
equality; the field equalities are NOT co-resident here; `membership` / `quot_eq` / `ValueGeometry` are NOT entered; the
un-built correspondence is the named residual (NOT claimed derived); strict `StarProm` / `InnerStarRaw` stay ZERO; NO
unconditional-coassoc claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton
/ floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-- **R-6c-body-513 — the whole-vertex correspondence socket** (the SOLE residual of the global `σ`). -/
structure ResolvedCanonicalFilteredContractCorrespondenceSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The whole-vertex bijection between `q`'s outer contract-with-stars and the corrected quotient's. -/
  correspondence : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    ResolvedContractTwiceVertexCorrespondence
      (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1))
      ((canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1)))

namespace ResolvedCanonicalFilteredContractCorrespondenceSupply

variable {Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}

/-- **R-6c-body-513 — the global permutation extension, built ONCE from the correspondence** (body-18 generic engine). -/
noncomputable def globalPermExtension (C : ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    VertexPermExtension (C.correspondence q) :=
  (finsetSubtypePermExtension _ _ (C.correspondence q).toEquiv).toVertexPermExtension (C.correspondence q)

/-- **R-6c-body-513 ∎ — the global star permutation** (= body-512's `starPerm`). -/
noncomputable def contractStarPerm (C : ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    Equiv.Perm VertexId :=
  (C.globalPermExtension q).starPerm

/-- **R-6c-body-513 — orientation on `G₂.vertices`** (`σ w = corr.invFun ⟨w, hw⟩`). -/
theorem contractStarPerm_on_vertices (C : ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (w : VertexId)
    (hw : w ∈ ((canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).contractWithStars
        (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
          (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
          (canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1))).vertices) :
    C.contractStarPerm q w = ((C.correspondence q).invFun ⟨w, hw⟩).1 :=
  (C.globalPermExtension q).on_vertices w hw

/-- **R-6c-body-513 — inverse orientation on `G₁.vertices`** (`σ.symm v = corr.toFun ⟨v, hv⟩`). -/
theorem contractStarPerm_inv_on_vertices (C : ResolvedCanonicalFilteredContractCorrespondenceSupply Measure E)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (v : VertexId)
    (hv : v ∈ (q.1.1.1.contractWithStars
      (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices) :
    (C.contractStarPerm q).symm v = ((C.correspondence q).toFun ⟨v, hv⟩).1 :=
  (C.globalPermExtension q).inv_on_vertices v hv

end ResolvedCanonicalFilteredContractCorrespondenceSupply

end GaugeGeometry.QFT.Combinatorial
