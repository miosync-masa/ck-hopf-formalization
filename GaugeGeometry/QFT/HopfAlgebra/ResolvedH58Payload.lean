import GaugeGeometry.QFT.HopfAlgebra.ResolvedSigmaSaturation

/-!
# Resolved H5.8 payload interface (Track R-4-superfull, Step 7A)

The generator-level data package the resolved H5.8 reindexing needs, and the proof
that it supplies the two resolved replacements for the flat false facades:

* **insertion injectivity** (`resolvedParentRemnant` injOn) — replaces
  `ForestGraphInsertionUniquenessModel`;
* **promoted external-leg containment** — replaces
  `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`.

We do **not** port the H5.8 proof here.  We pin the data interface and close
`data package → local replacements`, so the remaining work is purely wiring these
into the H5.8 skeleton.  The flat H5.8 carries σ-cover data *per* branch index
`r : forestQuotientForestSigma g`, so `ResolvedH58Payload` carries an abstract
`SigmaIndex` with pointwise cover data.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-! ## Step 7A-1 — local replacements from one cover datum -/

/-- The two resolved boundary replacements, as a `Prop` bundle over one σ-cover datum. -/
structure ResolvedH58LocalReplacements {G : ResolvedFeynmanGraph}
    (D : ResolvedSigmaCoverData G) : Prop where
  /-- Insertion injectivity (replaces `ForestGraphInsertionUniquenessModel`). -/
  insertion_inj : Set.InjOn (resolvedParentRemnant D.Aout D.starOf) ↑D.parents
  /-- Promoted external-leg containment (replaces the cover-side leg facade). -/
  promoted_legs : ∀ γ ∈ D.parents,
    ∀ η ∈ resolvedPromotedComponentsOfRemnant D.Aout D.starOf γ,
      η.externalLegs ≤ resolvedSourceExactPlusExternalLegs D.Aout D.starOf
        (resolvedParentRemnant D.Aout D.starOf γ).vertices

/-- **The cover datum supplies both replacements.** -/
theorem ResolvedSigmaCoverData.localReplacements {G : ResolvedFeynmanGraph}
    (D : ResolvedSigmaCoverData G) (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    ResolvedH58LocalReplacements D where
  insertion_inj := D.parentRemnant_injOn hEdgeId hLegId
  promoted_legs := fun γ _ _ hη =>
    promoted_externalLegs_le_plus_of_parent_set D.Aout D.starOf γ hη

/-! ## Step 7A-2 — generator-level payload -/

/-- **Resolved H5.8 payload** for a generator `g`: an id-unique payload family plus, per
branch index, the σ-cover datum.  (Finiteness/index laws are deferred — this is the data
interface, matching the flat per-`r` cover structure.) -/
structure ResolvedH58Payload (g : HopfGen) where
  /-- The id-unique payload family (supplies `EdgeIdsUnique`/`LegIdsUnique`). -/
  PFU : ResolvedHopfPayloadFamilyWithUniqueIds
  /-- The branch index (abstract — flat uses `forestQuotientForestSigma g`). -/
  SigmaIndex : Type
  /-- Per-branch σ-cover data on the payload carrier. -/
  sigmaCover : SigmaIndex → ResolvedSigmaCoverData (PFU.payload g).G

/-- **Pointwise local replacements** on every branch of an H5.8 payload, fed the
payload's per-generator identity-uniqueness. -/
theorem ResolvedH58Payload.localReplacements {g : HopfGen}
    (P : ResolvedH58Payload g) (r : P.SigmaIndex) :
    ResolvedH58LocalReplacements (P.sigmaCover r) :=
  (P.sigmaCover r).localReplacements (P.PFU.edgeIdsUnique g) (P.PFU.legIdsUnique g)

end GaugeGeometry.QFT.Combinatorial
