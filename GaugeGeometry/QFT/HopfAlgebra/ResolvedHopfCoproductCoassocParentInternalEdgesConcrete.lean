import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOccurrenceValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarValueCore
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedLocalComponent

/-!
# R-6c-body-387 — bank-3b: the parent-section internal-edges projection, recovered as a THEOREM (PROVED)

Three-hundred-and-eighty-seventh genuine-body step — the first of the three parent/remnant projections, formally
recovered per the body-382 verdict: `(Core.parent (fwd q) δ).internalEdges = o.γ.1.internalEdges`.  Collection equality
alone (body-385/386) does NOT reach edge-preimage uniqueness — it needs the RETARGET BRIDGE that identifies the two
retarget maps.  Four stages:

1. **Promote aggregate** `promote_internalEdges_eq` — `(promote γ B).internalEdges = B.internalEdges`
   (`promote_elements` + `Finset.sum_image` with `promote_injective`).
2. **Retarget bridge** `promoted_retargetVertex_eq_inner` / `promoted_retargetEdge_eq_inner` — the touched-outer retarget
   equals the inner-forest retarget POINTWISE (body-352-style inside/outside split; the star values agree by
   `promoted_star_agrees`).  This is the true crux.
3. **Edge-preimage uniqueness** `quotientEdgePreimage_eq_occurrence_complement` — both `quotientEdgePreimage` and
   `o.B.1.complementEdges` map through the touched retarget to `δ.1.internalEdges` (LHS by `quotientEdgePreimage_map`;
   RHS by the retarget bridge + `contractWithStars_internalEdges` + `hδ`/`Wiring`), so
   `retarget_residual_edges_injective` (under the base-model `hEdgeId : G.EdgeIdsUnique`) forces them equal.
4. **Projection** `parent_remnantComponent_internalEdges` — `Core.parent.internalEdges = touched.internalEdges +
   quotientEdgePreimage = o.B.internalEdges + o.B.complementEdges = o.γ.internalEdges` (`add_tsub_cancel_of_le`).

Per the HALT: `OccInv`, the parent equality, the forest bridge, and the forward round-trip are NOT used; the external-leg
datum is NOT used; the sole geometric datum is `promoted_star_agrees` (via body-385/386); ownership is the body-384
`Wiring`; `hEdgeId` is surfaced as the explicit base-model canonical-unique-payload gate.  No facade, no flat term, no
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

/-! ## Stage 1 — the promote aggregate -/

/-- **R-6c-body-387 — subgraph promote is injective** (it keeps the data). -/
theorem promote_injective {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G) :
    Function.Injective (γ.promote) := by
  intro x y h
  apply ResolvedFeynmanSubgraph.ext
  · have := congrArg ResolvedFeynmanSubgraph.vertices h
    rwa [ResolvedFeynmanSubgraph.promote_vertices, ResolvedFeynmanSubgraph.promote_vertices] at this
  · have := congrArg ResolvedFeynmanSubgraph.internalEdges h
    rwa [ResolvedFeynmanSubgraph.promote_internalEdges,
      ResolvedFeynmanSubgraph.promote_internalEdges] at this
  · have := congrArg ResolvedFeynmanSubgraph.externalLegs h
    rwa [ResolvedFeynmanSubgraph.promote_externalLegs,
      ResolvedFeynmanSubgraph.promote_externalLegs] at this

/-- **R-6c-body-387 — the promote aggregate.**  Promoting an admissible forest keeps its aggregate internal edges. -/
theorem promote_internalEdges_eq {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (B : ResolvedAdmissibleSubgraph γ.toResolvedFeynmanGraph) :
    (ResolvedAdmissibleSubgraph.promote γ B).internalEdges = B.internalEdges := by
  classical
  unfold ResolvedAdmissibleSubgraph.internalEdges
  symm
  refine Finset.sum_bij (fun b _ => γ.promote b) ?_ ?_ ?_ ?_
  · intro b hb
    rw [ResolvedAdmissibleSubgraph.promote_elements]
    simp only [Finset.mem_image]
    exact ⟨b, hb, rfl⟩
  · intro b₁ _ b₂ _ h; exact promote_injective γ h
  · intro ε hε
    rw [ResolvedAdmissibleSubgraph.promote_elements] at hε
    simp only [Finset.mem_image] at hε
    obtain ⟨b, hb, rfl⟩ := hε
    exact ⟨b, hb, rfl⟩
  · intro b _; exact (ResolvedFeynmanSubgraph.promote_internalEdges γ b).symm

/-! ## Stage 2 — the retarget bridge (the crux) -/

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-387 — the vertex retarget bridge.**  Under the occurrence's collection equality `he`, the touched-outer
retarget (over `G`/`selectedOuterRawOf`) agrees POINTWISE with the inner-forest retarget (over `o.γ.1.tRFG`/`o.B.1`).
Inside: `promoted_star_agrees`; outside: both identity. -/
theorem promoted_retargetVertex_eq_inner
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (v : VertexId) :
    (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).retargetVertex
        (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) v
      = o.B.1.retargetVertex (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) v := by
  have hev : (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).vertices = o.B.1.vertices := by
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
  · have hv' : v ∈ (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).vertices := by
      rw [hev]; exact hv
    have hcomp : (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).componentAt hv'
        = o.γ.1.promote (o.B.1.componentAt hv) := by
      have hmem_t : o.γ.1.promote (o.B.1.componentAt hv)
          ∈ (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).elements := by
        rw [touchedOuterForest_elements, he]
        simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
        exact ⟨o.B.1.componentAt hv, o.B.1.componentAt_mem hv, rfl⟩
      have hv_in : v ∈ (o.γ.1.promote (o.B.1.componentAt hv)).vertices := by
        rw [ResolvedFeynmanSubgraph.promote_vertices]; exact o.B.1.componentAt_vertex_mem hv
      by_contra hne
      exact Finset.disjoint_left.mp
        ((touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).pairwiseDisjoint hmem_t
          ((touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).componentAt_mem hv')
          (fun h => hne h.symm))
        hv_in ((touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).componentAt_vertex_mem hv')
    rw [ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv',
      ResolvedAdmissibleSubgraph.retargetVertex,
      ResolvedAdmissibleSubgraph.componentAt?_of_mem _ hv]
    show D.starOf G (fwdMapFilteredValue Fmem V q).1.1
        ((touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).componentAt hv')
      = D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1 (o.B.1.componentAt hv)
    rw [hcomp]
    exact StarProm.promoted_star_agrees q o (o.B.1.componentAt hv) (o.B.1.componentAt_mem hv)
  · have hv' : v ∉ (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).vertices := by
      rw [hev]; exact hv
    rw [ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv',
      ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hv]

/-- **R-6c-body-387 — the edge retarget bridge** (endpoint corollary of the vertex bridge). -/
theorem promoted_retargetEdge_eq_inner
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (he : touchedOuterComponents (fwdMapFilteredValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements)
    (e : ResolvedFeynmanEdge) :
    (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).retargetEdge
        (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) e
      = o.B.1.retargetEdge (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) e := by
  unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
  rw [promoted_retargetVertex_eq_inner StarProm q o δ he,
    promoted_retargetVertex_eq_inner StarProm q o δ he]

/-! ## Stage 3 — edge-preimage uniqueness -/

/-- **R-6c-body-387 — the edge preimage is the occurrence's complement edges.**  Both retarget through the touched map to
`δ.1.internalEdges`, so `retarget_residual_edges_injective` (under `hEdgeId`) equates them. -/
theorem quotientEdgePreimage_eq_occurrence_complement
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (hEdgeId : G.EdgeIdsUnique) (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    quotientEdgePreimage (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1)
        (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) (touchedLocalComponent (fwdMapFilteredValue Fmem V q) δ.1)
      = o.B.1.complementEdges := by
  have he := touchedOuterComponents_of_occurrence_wired Fstar Wiring StarProm q o δ hδ
  have hcr : (Concrete q.1).remnantComponent o = δ.1 :=
    eq_of_heq (remnantComponent_heq_toConcrete Wiring q o δ hδ)
  have hδint : δ.1.internalEdges = o.contractedSourceGraph.internalEdges := by rw [← hcr]; rfl
  have hM₁ : quotientEdgePreimage (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1)
        (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) (touchedLocalComponent (fwdMapFilteredValue Fmem V q) δ.1)
      ≤ G.internalEdges := by
    refine le_trans (quotientEdgePreimage_le _ _ _) ?_
    rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self
  have hM₂ : o.B.1.complementEdges ≤ G.internalEdges := by
    rw [ResolvedAdmissibleSubgraph.complementEdges]
    exact le_trans tsub_le_self o.γ.1.internalEdges_le
  refine (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).retarget_residual_edges_injective
    hEdgeId (D.starOf G (fwdMapFilteredValue Fmem V q).1.1) hM₁ hM₂ ?_
  rw [quotientEdgePreimage_map, touchedLocalComponent_internalEdges,
    Multiset.map_congr rfl (fun e _ => promoted_retargetEdge_eq_inner StarProm q o δ he e),
    ← ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  exact hδint

/-! ## Stage 4 — the projection -/

/-- **R-6c-body-387 — the internal-edges projection (THEOREM, per body-382).**  The de-contracted parent's internal edges
are the occurrence source outer's. -/
theorem parent_remnantComponent_internalEdges
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Fstar : ResolvedCanonicalStarFacts D)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (hEdgeId : G.EdgeIdsUnique) (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    (Core.parent (fwdMapFilteredValue Fmem V q) δ).internalEdges = o.γ.1.internalEdges := by
  have he := touchedOuterComponents_of_occurrence_wired Fstar Wiring StarProm q o δ hδ
  show (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).internalEdges
      + quotientEdgePreimage (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1)
          (D.starOf G (fwdMapFilteredValue Fmem V q).1.1)
          (touchedLocalComponent (fwdMapFilteredValue Fmem V q) δ.1)
      = o.γ.1.internalEdges
  rw [quotientEdgePreimage_eq_occurrence_complement Fstar StarProm Wiring hEdgeId q o δ hδ]
  have ht : (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).internalEdges = o.B.1.internalEdges := by
    have h1 : (touchedOuterForest (fwdMapFilteredValue Fmem V q) δ.1).internalEdges
        = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).internalEdges := by
      unfold ResolvedAdmissibleSubgraph.internalEdges
      rw [touchedOuterForest_elements, he]
    rw [h1, promote_internalEdges_eq]
  rw [ht, ResolvedAdmissibleSubgraph.complementEdges]
  exact add_tsub_cancel_of_le
    (resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise o.B.1 o.B.1.isPairwiseDisjoint)

end GaugeGeometry.QFT.Combinatorial
