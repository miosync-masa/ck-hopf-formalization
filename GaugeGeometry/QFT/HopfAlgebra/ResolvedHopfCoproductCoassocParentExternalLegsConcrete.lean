import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentInternalEdgesConcrete

/-!
# R-6c-body-388 — bank-3b: the parent-section external-legs projection, recovered as a THEOREM (PROVED)

Three-hundred-and-eighty-eighth genuine-body step — the SECOND parent/remnant projection, taken BEFORE `vertices`
(dependency correction: the custom parent's vertex filter reads `datum.legs`'s attachments, so the vertex equality needs
the legs pinned first).  Like `internalEdges` (body-387), `externalLegs` falls to a THEOREM under `hLegId`:
`(Core.parent (fwd q) δ).externalLegs = o.γ.1.externalLegs`.

* `promoted_retargetExternalLeg_eq_inner` — the leg retarget bridge, an immediate endpoint corollary of body-387's
  vertex bridge `promoted_retargetVertex_eq_inner`;
* `parent_remnantComponent_externalLegs` — the projection, straight through `retarget_residual_legs_injective`:
  `Core.parent.externalLegs = (Core.legLift z δ).legs`, and both `(legLift).legs` and `o.γ.1.externalLegs` are
  submultisets of `G.externalLegs` (`legs_le` / `externalLegs_le`) whose touched retarget images coincide
  (`legLift.map_eq` → `δ.externalLegs`; the leg bridge + `hδ`/`Wiring` → `contractedSourceGraph.externalLegs = δ.externalLegs`).

Per the HALT: NO new occurrence-specific leg datum — only `Core.legLift`'s existing `map_eq` / `legs_le`; `hLegId :
G.LegIdsUnique` is surfaced as the explicit base-model canonical-unique-payload gate; `OccInv` / the parent equality /
the forest bridge / the forward round-trip are NOT used; the sole geometric datum is `promoted_star_agrees` (via the
retarget bridge).  This updates the body-382 `externalLegs` verdict from TBC to THEOREM.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-388 — the leg retarget bridge** (endpoint corollary of the vertex bridge). -/
theorem promoted_retargetExternalLeg_eq_inner
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (ℓ : ResolvedExternalLeg) :
    (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).retargetExternalLeg
        (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) ℓ
      = o.B.1.retargetExternalLeg (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) ℓ := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
  rw [promoted_retargetVertex_eq_inner StarProm q o δ he]

/-- **R-6c-body-388 — the external-legs projection (THEOREM, updating the body-382 verdict).**  The de-contracted
parent's external legs are the occurrence source outer's. -/
theorem parent_remnantComponent_externalLegs
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (hLegId : G.LegIdsUnique) (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (Core.parent (fwdMapFilteredValue Fmem V q) δ).externalLegs = o.γ.1.externalLegs := by
  have he := touchedOuterComponents_of_occurrence_wired Fstar Wiring StarProm q o δ hδ
  have hcr : (Concrete q.1).remnantComponent o = δ.1 :=
    eq_of_heq (remnantComponent_heq_toConcrete Wiring q o δ hδ)
  have hδleg : δ.1.externalLegs = o.contractedSourceGraph.externalLegs := by rw [← hcr]; rfl
  show (Core.legLift (fwdMapFilteredValue Fmem V q) δ).legs = o.γ.1.externalLegs
  refine (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).retarget_residual_legs_injective
    hLegId (D.starOf G (fwdMapFilteredValue Fmem V q).1.1)
    (Core.legLift (fwdMapFilteredValue Fmem V q) δ).legs_le o.γ.1.externalLegs_le ?_
  rw [(Core.legLift (fwdMapFilteredValue Fmem V q) δ).map_eq, touchedLocalComponent_externalLegs,
    Multiset.map_congr rfl (fun ℓ _ => promoted_retargetExternalLeg_eq_inner StarProm q o δ he ℓ)]
  exact hδleg

end GaugeGeometry.QFT.Combinatorial
