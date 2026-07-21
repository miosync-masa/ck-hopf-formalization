import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaThreeRouteInverse
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocVertexSetEq
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientSupportScopeRepair

/-!
# R-6c-body-524 — field-equality scope repair + faithful q-local socket (PROVED)

Five-hundred-and-twenty-fourth genuine-body step — a body-519-grade scope trap catch.  The three whole-graph field
equalities of body-512 would, if pushed through an UNRESTRICTED `retargetVertex_eq` (`∀ v`), re-require
`targetLeftStar = sourceLeftStar` (the body-446/519 non-existence certificate): for `v := targetLeftStar q i`, the input
retarget fixes `v ∉ G.vertices`, the quotient retarget fixes it as a left survivor, but the global `σ` sends it to
`sourceLeftStar q i`.  Since all edge/leg endpoints live in `G.vertices`, only the ON-`G` retarget equation is needed.

## The scope repair

* `canonicalCorrectedContract_vertices_eq` — the vertices field is FREE from the correspondence
  (`vertices_eq_of_perm_extension`);
* `selectedOuterVertexDomain` — the intermediate one-step domain map (`selectedOuterRawOf.retargetVertex`);
* `ResolvedCanonicalFilteredContractRetargetDomainSupply` — the faithful residual socket with EXACTLY two fields:
  `retargetVertex_eq_on_G` (`∀ v ∈ G.vertices`, NOT `∀ v`) and `internalEdges_domain`;
* leg domain is derived (`selectedOuter_leg_domain_eq`, definitional via `contractWithStars_externalLegs`);
* endpoint lifts (`retargetEdge_eq_of_mem_complement` / `retargetLeg_eq`) transport the on-`G` equation to edges/legs, using
  the ambient-support gate (`ResolvedCarrierAmbientSupportSupply`, model law — NOT a `∀ G` claim) for the endpoints;
* the whole edge/leg field equalities are derived (`internalEdges_eq` / `externalLegs_eq`);
* `toContractTwiceFieldSupply` — the body-512 `ResolvedCanonicalFilteredContractTwiceFieldSupply` adapter.

So the "three field equalities" reduce to: vertices FREE, legs FREE from the retarget, ONE edge-domain sheet — and strict
left-star equality is never reintroduced.

Per the HALT/guards: the `∀ v` field is NOT introduced; `retargetVertex_eq_on_G` / `internalEdges_domain` are NOT proved
(the SOLE residual, named); the socket inhabitant is NOT built; `sourceLeftStar = targetLeftStar` is NOT required; global
`σ`'s three fields are only assembled generically; strict `StarProm` / `InnerStarRaw` stay ZERO; NO unconditional-coassoc
claim.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Step 1 — the vertices field, FREE -/

/-- **R-6c-body-524 ∎ — the whole-graph vertices field equality**, straight from the correspondence. -/
theorem canonicalCorrectedContract_vertices_eq
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).vertices
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm
        ((canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q)).vertices :=
  vertices_eq_of_perm_extension ((canonicalCorrectedContractCorrespondenceSupply Measure E).globalPermExtension q)

/-! ## Step 2 — the intermediate domain map -/

/-- **R-6c-body-524 — the intermediate one-step vertex domain** (`selectedOuterRawOf.retargetVertex`). -/
noncomputable def selectedOuterVertexDomain
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) (v : VertexId) : VertexId :=
  ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf
      q.1).retargetVertex
    (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G
      ((resolvedConcreteForestPromoteSupply canonicalUniqueSupportedCarrierProperSupply.toData G).selectedOuterRawOf q.1))
    v

/-! ## Step 3 — the faithful residual socket (EXACTLY two fields) -/

/-- **R-6c-body-524 — the faithful field-domain residual socket.**  ONLY the on-`G` retarget-vertex equation and the
edge-domain transport — NO `∀ v` field (which would re-require `targetLeftStar = sourceLeftStar`). -/
structure ResolvedCanonicalFilteredContractRetargetDomainSupply
    (Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H) where
  /-- The single-step contraction of an on-`G` vertex equals the relabeled two-step contraction. -/
  retargetVertex_eq_on_G : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) {v : VertexId},
    v ∈ G.vertices →
    q.1.1.1.retargetVertex (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) v
      = (canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q
        ((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).retargetVertex
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))
          (selectedOuterVertexDomain q v))
  /-- The input-outer complement edges, domain-transported, are the corrected quotient's complement edges. -/
  internalEdges_domain : ∀ {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G),
    q.1.1.1.complementEdges.map (fun e => e.retarget (selectedOuterVertexDomain q))
      = (canonicalCorrectedQuotientRaw Measure
          canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
          canonicalUniqueStarFactsOfW' q.1).complementEdges

/-! ## Step 4 — the leg domain, derived (definitional) -/

/-- **R-6c-body-524 — the leg domain is definitional** (`contractWithStars_externalLegs`). -/
theorem selectedOuter_leg_domain_eq
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    G.externalLegs.map (fun ℓ => ℓ.retarget (selectedOuterVertexDomain q))
      = (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1).externalLegs := by
  rw [ResolvedCoassocSplitChoice.selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  rfl

/-! ## Step 5 — the endpoint lifts -/

variable {Measure : ResolvedMeasureLeafSupply canonicalUniqueSupportedCarrierProperSupply.toData}
  {E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H}

/-- **R-6c-body-524 — the complement-edge endpoint lift** (on-`G` equation on both endpoints). -/
theorem retargetEdge_eq_of_mem_complement
    (F : ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E)
    (Amb : ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    {e : ResolvedFeynmanEdge} (he : e ∈ q.1.1.1.complementEdges) :
    q.1.1.1.retargetEdge (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) e
      = ResolvedFeynmanEdge.map ((canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q)
        ((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).retargetEdge
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))
          (e.retarget (selectedOuterVertexDomain q))) := by
  obtain ⟨hs, ht⟩ := Amb.edges_supported_of_mem q.1.1.2 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)
  simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.retarget]
  rw [F.retargetVertex_eq_on_G q hs, F.retargetVertex_eq_on_G q ht]

/-- **R-6c-body-524 — the external-leg endpoint lift** (on-`G` equation on the attachment). -/
theorem retargetLeg_eq
    (F : ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E)
    (Amb : ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ G.externalLegs) :
    q.1.1.1.retargetExternalLeg (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1) ℓ
      = ResolvedExternalLeg.map ((canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q)
        ((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).retargetExternalLeg
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))
          (ℓ.retarget (selectedOuterVertexDomain q))) := by
  have ha := Amb.legs_supported_of_mem q.1.1.2 ℓ hℓ
  simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedExternalLeg.map, ResolvedExternalLeg.retarget]
  rw [F.retargetVertex_eq_on_G q ha]

/-! ## Step 6 — the whole edge/leg field equalities, derived -/

/-- **R-6c-body-524 — the whole-graph internal-edges field equality**, from the edge domain + the endpoint lift. -/
theorem canonicalCorrectedContract_internalEdges_eq
    (F : ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E)
    (Amb : ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).internalEdges
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm
        ((canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q)).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  show q.1.1.1.complementEdges.map (q.1.1.1.retargetEdge _)
      = ((_ : ResolvedAdmissibleSubgraph _).complementEdges.map (_ : ResolvedFeynmanEdge → ResolvedFeynmanEdge)).map
        (ResolvedFeynmanEdge.map _)
  rw [← F.internalEdges_domain q, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun e he => retargetEdge_eq_of_mem_complement F Amb q he)

/-- **R-6c-body-524 — the whole-graph external-legs field equality**, from the leg domain + the endpoint lift. -/
theorem canonicalCorrectedContract_externalLegs_eq
    (F : ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E)
    (Amb : ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G) :
    (q.1.1.1.contractWithStars (canonicalUniqueSupportedCarrierProperSupply.toData.starOf G q.1.1.1)).externalLegs
      = (((canonicalCorrectedQuotientRaw Measure
            canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
            canonicalUniqueStarFactsOfW' q.1).contractWithStars
          (canonicalUniqueSupportedCarrierProperSupply.toData.starOf
            (ResolvedCoassocSplitChoice.selectedOuterContractGraph q.1)
            (canonicalCorrectedQuotientRaw Measure
              canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
              canonicalUniqueStarFactsOfW' q.1))).mapPerm
        ((canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q)).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  simp only [ResolvedFeynmanGraph.mapPerm]
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, ← selectedOuter_leg_domain_eq q,
    Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ hℓ => retargetLeg_eq F Amb q hℓ)

/-! ## Step 7 — the body-512 field-supply adapter -/

/-- **R-6c-body-524 ∎ — the faithful domain socket → body-512's contract-twice FIELD supply.**  Vertices FREE (Step 1),
edges/legs derived (Step 6) from the two residual fields + the ambient-support gate. -/
noncomputable def ResolvedCanonicalFilteredContractRetargetDomainSupply.toContractTwiceFieldSupply
    (F : ResolvedCanonicalFilteredContractRetargetDomainSupply Measure E)
    (Amb : ResolvedCarrierAmbientSupportSupply canonicalUniqueSupportedCarrierProperSupply.toData) :
    ResolvedCanonicalFilteredContractTwiceFieldSupply Measure E where
  starPerm := fun q => (canonicalCorrectedContractCorrespondenceSupply Measure E).contractStarPerm q
  vertices_eq := fun q => canonicalCorrectedContract_vertices_eq Measure E q
  internalEdges_eq := fun q => canonicalCorrectedContract_internalEdges_eq F Amb q
  externalLegs_eq := fun q => canonicalCorrectedContract_externalLegs_eq F Amb q

end GaugeGeometry.QFT.Combinatorial
