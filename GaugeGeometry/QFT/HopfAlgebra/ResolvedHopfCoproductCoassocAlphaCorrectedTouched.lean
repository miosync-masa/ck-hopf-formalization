import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalAlphaWrapper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentExternalLegsConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedFamilyDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedRetargetAgreement

/-!
# R-6c-body-484 — the corrected touched collection + corrected retarget bridge (StarProm's core two layers) (PROVED)

Four-hundred-and-eighty-fourth genuine-body step — the JUDGMENT point of the body-445 migration campaign.  It closes the
two layers that strict `StarProm` (`promoted_star_agrees`) was standing in for, WITHOUT any strict cross-ambient equality:

1. `touchedOuterComponents_of_corrected_occurrence_alpha` — the corrected touched collection theorem, over the canonical
   alpha `VBuild`'s corrected remnant.  The remnant's vertices are the PROMOTED-star contraction's (body-464), so the
   touched-outer star classification bottoms out on the DEFINITIONAL `promotedOccurrenceStar s o b = D.starOf G
   (selectedOuterRawOf s) (o.γ.1.promote b)` — `promoted_star_agrees` is NEVER invoked.
2. `promoted_retargetVertex_eq_inner_alpha` / `_retargetEdge_` / `_retargetExternalLeg_` — the corrected retarget bridge,
   body-387/388 mirrored to the COMMON promoted-star representation: the touched-outer retarget (over `G`) agrees pointwise
   with the inner-forest retarget over `promotedOccurrenceStar q.1 o` (NOT the strict inner star), by componentAt
   uniqueness (body-387) + the same definitional star identity.  No per-star strict equality, no permutation equality.

**Verdict.**  Both close with ZERO strict `StarProm`.  So the residual `StarProm` was not an honest model datum: it was
derived corrected geometry mistakenly expressed as a strict cross-ambient equality.

Per the HALT/guards: the internal/external/vertices projections are NOT entered; parent equality / the forest bridge are
NOT assembled; the body-461 recovered-side round-trip is NOT mixed in; the inner correcting permutation and the promoted
permutation are NOT compared; strict `StarProm` is NOT reintroduced as a parameter; strict `InnerStarRaw` NOT restored;
body-445 stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
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

/-! ## Layer 2 — the corrected retarget bridge (generic in `V`, over the common promoted star) -/

variable {D : ResolvedCoproductProperForestData}
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D}
  {V : ResolvedFilteredConcreteSummandValueSupply D}

/-- **R-6c-body-484 — the alpha vertex retarget bridge.**  Under the occurrence's touched-collection equality `he`, the
touched-outer retarget (over `G` / `selectedOuterRawOf`) agrees POINTWISE with the inner-forest retarget over the COMMON
promoted star `promotedOccurrenceStar q.1 o` — body-387's componentAt uniqueness, with the star step now DEFINITIONAL
(`promotedOccurrenceStar q.1 o b = D.starOf G (selectedOuterRawOf q.1) (o.γ.1.promote b)`), NO `promoted_star_agrees`. -/
theorem promoted_retargetVertex_eq_inner_alpha
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredAlphaValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (v : VertexId) :
    (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).retargetVertex
        (D.starOf G (fwdMapFilteredAlphaValue Fmem V q).1.1) v
      = o.B.1.retargetVertex (promotedOccurrenceStar q.1 o) v := by
  have hev : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).vertices = o.B.1.vertices := by
    apply Finset.ext
    intro w
    constructor
    · intro hw
      obtain ⟨γc, hγc, hwγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hw
      rw [touchedOuterForest_elements, he] at hγc
      simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image] at hγc
      obtain ⟨b, hb, rfl⟩ := hγc
      rw [ResolvedFeynmanSubgraph.promote_vertices] at hwγ
      exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨b, hb, hwγ⟩
    · intro hw
      obtain ⟨b, hb, hwb⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hw
      refine ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨o.γ.1.promote b, ?_, ?_⟩
      · rw [touchedOuterForest_elements, he]
        simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
        exact ⟨b, hb, rfl⟩
      · rw [ResolvedFeynmanSubgraph.promote_vertices]; exact hwb
  by_cases hv : v ∈ o.B.1.vertices
  · have hv' : v ∈ (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).vertices := by
      rw [hev]; exact hv
    have hcomp : (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).componentAt hv'
        = o.γ.1.promote (o.B.1.componentAt hv) := by
      have hmem_t : o.γ.1.promote (o.B.1.componentAt hv)
          ∈ (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).elements := by
        rw [touchedOuterForest_elements, he]
        simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
        exact ⟨o.B.1.componentAt hv, o.B.1.componentAt_mem hv, rfl⟩
      have hv_in : v ∈ (o.γ.1.promote (o.B.1.componentAt hv)).vertices := by
        rw [ResolvedFeynmanSubgraph.promote_vertices]; exact o.B.1.componentAt_vertex_mem hv
      by_contra hne
      exact Finset.disjoint_left.mp
        ((touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).pairwiseDisjoint hmem_t
          ((touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).componentAt_mem hv')
          (fun h => hne h.symm))
        hv_in ((touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).componentAt_vertex_mem hv')
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv',
      ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv]
    show D.starOf G (fwdMapFilteredAlphaValue Fmem V q).1.1
        ((touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).componentAt hv')
      = promotedOccurrenceStar q.1 o (o.B.1.componentAt hv)
    rw [hcomp]
    rfl
  · have hv' : v ∉ (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).vertices := by
      rw [hev]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv',
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv]

/-- **R-6c-body-484 — the alpha edge retarget bridge** (endpoint corollary). -/
theorem promoted_retargetEdge_eq_inner_alpha
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredAlphaValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (e : ResolvedFeynmanEdge) :
    (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).retargetEdge
        (D.starOf G (fwdMapFilteredAlphaValue Fmem V q).1.1) e
      = o.B.1.retargetEdge (promotedOccurrenceStar q.1 o) e := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [promoted_retargetVertex_eq_inner_alpha q o δ he,
    promoted_retargetVertex_eq_inner_alpha q o δ he]

/-- **R-6c-body-484 — the alpha leg retarget bridge** (endpoint corollary). -/
theorem promoted_retargetExternalLeg_eq_inner_alpha
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredAlphaValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (ℓ : ResolvedExternalLeg) :
    (touchedOuterForest (fwdMapFilteredAlphaValue Fmem V q) δ.1).retargetExternalLeg
        (D.starOf G (fwdMapFilteredAlphaValue Fmem V q).1.1) ℓ
      = o.B.1.retargetExternalLeg (promotedOccurrenceStar q.1 o) ℓ := by
  unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
  rw [promoted_retargetVertex_eq_inner_alpha q o δ he]

/-! ## Layer 1 — the corrected touched collection (canonical alpha `VBuild`, NO `StarProm`) -/

/-- **R-6c-body-484 ∎ — the corrected touched-collection theorem.**  Over the canonical alpha `VBuild`'s corrected remnant
`δ`, the forward-selected outer's touched collection inside `δ` is the occurrence's `o.B`-promoted collection — proved with
ZERO strict `StarProm`, the star classification bottoming out on the definitional promoted star. -/
theorem touchedOuterComponents_of_corrected_occurrence_alpha
    {Fmem : ResolvedSelectedOuterFilteredMemSupply canonicalUniqueSupportedCarrierProperSupply.toData}
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    {G : ResolvedFeynmanGraph}
    (q : FilteredForestBlockDom canonicalUniqueSupportedCarrierProperSupply.toData G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q)})
    (hδ : HEq (VBuild.toCanonicalFilteredValue.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    touchedOuterComponents (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements := by
  -- `δ` is the corrected remnant; its vertices are the PROMOTED-star contraction's (body-464).
  have hcr : (canonicalCorrectedRemnantReembedSupply q.1 canonicalUniqueStarFactsOfW').correctedRemnantComponent o
      = δ.1 := eq_of_heq hδ
  have hδv : δ.1.vertices
      = (o.γ.1.toResolvedFeynmanGraph.vertices \ o.B.1.vertices)
        ∪ o.B.1.starVertices (promotedOccurrenceStar q.1 o) := by
    rw [← hcr, correctedRemnantComponent_vertices_eq_promoted q.1 o canonicalUniqueStarFactsOfW',
      ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  apply Finset.ext
  intro A
  simp only [mem_touchedOuterComponents, ResolvedAdmissibleSubgraph.promote_elements,
    Finset.mem_image]
  constructor
  · -- touched ⊆ promoted: the promoted star IS the global star of the promoted component, so `starOf_injective` closes.
    rintro ⟨hAmem, hstar⟩
    rw [hδv] at hstar
    rcases Finset.mem_union.mp hstar with hout | hstarv
    · exfalso
      rw [Finset.mem_sdiff] at hout
      exact canonicalUniqueStarFactsOfW'.starOf_fresh G _ A hAmem (o.γ.1.vertices_subset hout.1)
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstarv
      obtain ⟨b, hb, hbstar⟩ := hstarv
      have hpmem : o.γ.1.promote b
          ∈ (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1.elements :=
        promote_mem_selectedOuterRawOf_raw q.1 o hb
      exact ⟨b, hb, canonicalUniqueStarFactsOfW'.starOf_injective G _ hpmem hAmem hbstar⟩
  · -- promoted ⊆ touched: the star of the promoted component is the promoted star, by definition.
    rintro ⟨b, hb, rfl⟩
    have hpmem : o.γ.1.promote b
        ∈ (fwdMapFilteredAlphaValue Fmem VBuild.toCanonicalFilteredValue q).1.1.elements :=
      promote_mem_selectedOuterRawOf_raw q.1 o hb
    refine ⟨hpmem, ?_⟩
    rw [hδv]
    exact Finset.mem_union.mpr
      (Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb, rfl⟩))

end GaugeGeometry.QFT.Combinatorial
