import GaugeGeometry.QFT.HopfAlgebra.ResolvedUniquePayloadModel

/-!
# Payload-level boundary repair certificates (Track R-4-superfull, Steps 4–5)

The resolved boundary repair theorems — `externalLegs_lift_unique` (the resolved
counterpart of the flat `PromotedExternalLegsLiftableModel` facade) and
`parent_eq_of_remainder_eq` (the counterpart of `ForestGraphInsertionUniquenessModel`)
— require `LegIdsUnique` / `EdgeIdsUnique` of the ambient graph.  The unique-id
payload family (`ResolvedHopfPayloadFamilyWithUniqueIds`) supplies exactly those
hypotheses for every generator, so the repairs apply *directly* to the inhabited
payload.

This file packages that: a `ResolvedBoundaryRepairCertificate` bundling both repairs
over the whole family, proved for the canonical id-unique family.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-- **Resolved promotion monotonicity (containment kernel).**  Retargeting
(`promotion`) preserves leg containment: this is the carrier-level inequality the
flat `promoted_externalLegs_le_plus` facade ultimately asserts.  Crucially it needs
*no* identity-uniqueness — in the resolved layer the containment is structural; the
flat facade was forced only because flat retarget collapse destroys the leg-tracking
needed to construct the σ-cover at all. -/
theorem retargetExternalLeg_le_of_le {G : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {η source : Multiset ResolvedExternalLeg} (h : η ≤ source) :
    η.map (A.retargetExternalLeg starOf) ≤ source.map (A.retargetExternalLeg starOf) :=
  Multiset.map_le_map h

/-- **Payload-level repair certificate.**  For an id-unique payload family, both
resolved boundary repairs hold on every payload graph:
* `external_leg_lift_unique` — promoted external legs lift uniquely (the resolved
  replacement for `PromotedExternalLegsLiftableModel`);
* `insertion_unique` — a forest's parent subgraph is determined by its
  quotient/remainder (the resolved replacement for
  `ForestGraphInsertionUniquenessModel`). -/
structure ResolvedBoundaryRepairCertificate
    (PFU : ResolvedHopfPayloadFamilyWithUniqueIds) : Prop where
  /-- External-leg lift uniqueness on every payload graph. -/
  external_leg_lift_unique :
    ∀ (g : HopfGen) (A : ResolvedAdmissibleSubgraph (PFU.payload g).G)
      (starOf : ResolvedFeynmanSubgraph (PFU.payload g).G → VertexId)
      {L : Multiset ResolvedExternalLeg}, L ≤ (PFU.payload g).G.externalLegs →
      ∀ L', L' ≤ (PFU.payload g).G.externalLegs →
        L'.map (A.retargetExternalLeg starOf) = L.map (A.retargetExternalLeg starOf) →
        L' = L
  /-- Forest insertion uniqueness on every payload graph. -/
  insertion_unique :
    ∀ (g : HopfGen) (A : ResolvedAdmissibleSubgraph (PFU.payload g).G)
      (starOf : ResolvedFeynmanSubgraph (PFU.payload g).G → VertexId)
      {γ₁ γ₂ : ResolvedFeynmanSubgraph (PFU.payload g).G},
      γ₁.vertices = γ₂.vertices →
      A.internalEdges ≤ γ₁.internalEdges → A.internalEdges ≤ γ₂.internalEdges →
      A.quotientRemainderSubgraph starOf γ₁ = A.quotientRemainderSubgraph starOf γ₂ →
      γ₁ = γ₂
  /-- Promotion (retarget) preserves leg containment on every payload graph — the
  structural kernel of the flat `promoted_externalLegs_le_plus` consumer. -/
  promoted_externalLegs_containment :
    ∀ (g : HopfGen) (A : ResolvedAdmissibleSubgraph (PFU.payload g).G)
      (starOf : ResolvedFeynmanSubgraph (PFU.payload g).G → VertexId)
      {η source : Multiset ResolvedExternalLeg}, η ≤ source →
      η.map (A.retargetExternalLeg starOf) ≤ source.map (A.retargetExternalLeg starOf)

/-- **The repair certificate holds** for any id-unique payload family: each repair is
the corresponding resolved theorem fed the family's per-generator id-uniqueness. -/
theorem resolvedBoundaryRepairCertificate_holds
    (PFU : ResolvedHopfPayloadFamilyWithUniqueIds) :
    ResolvedBoundaryRepairCertificate PFU := by
  constructor
  · intro g A starOf L hL L' hL' hmap
    exact A.externalLegs_lift_unique (PFU.legIdsUnique g) starOf hL L' hL' hmap
  · intro g A starOf γ₁ γ₂ hV hA₁ hA₂ hRem
    exact A.parent_eq_of_remainder_eq (PFU.edgeIdsUnique g) (PFU.legIdsUnique g)
      starOf hV hA₁ hA₂ hRem
  · intro g A starOf η source h
    exact retargetExternalLeg_le_of_le A starOf h

/-- **R-4-superfull Steps 4–5 headline.**  An inhabited id-unique payload family
carrying both boundary repair certificates exists. -/
theorem exists_resolvedBoundaryRepairCertificate :
    ∃ PFU : ResolvedHopfPayloadFamilyWithUniqueIds,
      ResolvedBoundaryRepairCertificate PFU :=
  ⟨canonicalResolvedHopfPayloadFamilyWithUniqueIds,
    resolvedBoundaryRepairCertificate_holds _⟩

end GaugeGeometry.QFT.Combinatorial
