import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeSelectedOuter
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbed

/-!
# QFT-R1-body-603 — root-coordinate quotient ambient + right-survivor

Body-602 assembled the `selectedOuter` admissible forest of a W‴ filtered split choice and landed it back
in the fifth-axis index.  This body opens the **quotient ambient** obtained by star-contracting that
`selectedOuter`, and shows that every **right-primitive** component of the split choice survives the
contraction φ⁴-family-natively by RE-EMBEDDING (not decontraction — that is the remnant, body-604) into the
quotient graph, with an EXPLICIT φ⁴ connected-divergence proved by a degree calculation
(`physicalExternalLegCount survivor = physicalExternalLegCount source`), NOT by any ambient-invariance
class.

## HALT compliance / clean re-derivation

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only).  ZERO forbidden divergence classes in ANY
declaration's type.  An audit showed that the pre-existing survivor-embed helpers
(`survivorReembed(OfDisjoint)`, `reembed_*_contractWithStars`, `internalEdges_le_complementEdges_of_disjoint`,
`resolvedComponentGen(_reembed)`) all carry the forbidden `IsPermInvariantDivergence` /
`IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` section binders in their **types**, so they are
NOT consumed.  Only the genuinely clean `ResolvedFeynmanSubgraph.reembed` (instance-free) and the core
`contractWithStars` / `retargetVertex` lemmas are used; the three support facts + the edge-complement bound
are **re-derived clean** here.  The source-generator anchor for body-605 is the clean
`phi4WTriplePrime_survivor_toResolvedFeynmanGraph` (`resolvedComponentGen` is forbidden-class-polluted, so
the generator equality is deferred to a clean re-derivation in body-605 from this intrinsic-graph equality).
Divergence is proved by EXPLICIT degree calculation, never by an `Is*InvariantDivergence` class.  No
`sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 1600000

/-- The concrete φ⁴ divergence measure family, registered as a file-local instance so that the
`ResolvedAdmissibleSubgraph` machinery resolves in signatures (this is the providable
`[(H : FeynmanGraph) → DivergenceMeasure H] := phi4DivergenceMeasureFamily`; NO forbidden class). -/
noncomputable local instance phi4Inst : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — clean re-derivation of the three survivor support facts + the edge-complement bound -/

/-- **body-603 (Step 0) — survivor vertices support** (clean re-derivation). -/
theorem phi4WTriplePrime_reembed_vertices_subset (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.vertices ⊆ (A.contractWithStars starOf).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  intro v hv
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨γ.vertices_subset hv,
    Finset.disjoint_left.mp hdisj hv⟩)

/-- **body-603 (Step 0) — an edge of an admissible subgraph has its source in its vertices** (clean). -/
theorem phi4WTriplePrime_source_mem_vertices (A : ResolvedAdmissibleSubgraph G)
    {e : ResolvedFeynmanEdge} (he : e ∈ A.internalEdges) : e.source ∈ A.vertices := by
  simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
  obtain ⟨δ, hδ, heδ⟩ := he
  exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, (δ.edges_supported e heδ).1⟩

/-- **body-603 (Step 0) — survivor edge-complement bound from vertex disjointness** (clean). -/
theorem phi4WTriplePrime_internalEdges_le_complementEdges (A : ResolvedAdmissibleSubgraph G)
    (γ : ResolvedFeynmanSubgraph G) (hdisj : Disjoint γ.vertices A.vertices) :
    γ.internalEdges ≤ A.complementEdges := by
  have hdisj_edges : ∀ e, e ∈ γ.internalEdges → e ∈ A.internalEdges → False :=
    fun e heγ heA => Finset.disjoint_left.mp hdisj (γ.edges_supported e heγ).1
      (phi4WTriplePrime_source_mem_vertices A heA)
  have hsub_eq : γ.internalEdges - A.internalEdges = γ.internalEdges := by
    refine Multiset.ext.mpr (fun e => ?_)
    rw [Multiset.count_sub]
    rcases eq_or_ne (Multiset.count e γ.internalEdges) 0 with h0 | h0
    · omega
    · have hA0 : Multiset.count e A.internalEdges = 0 := by
        by_contra hA0
        exact hdisj_edges e (Multiset.count_pos.mp (Nat.pos_of_ne_zero h0))
          (Multiset.count_pos.mp (Nat.pos_of_ne_zero hA0))
      omega
  rw [← hsub_eq]
  exact A.sub_internalEdges_le_complementEdges γ

/-- **body-603 (Step 0) — survivor internal-edges support** (clean re-derivation). -/
theorem phi4WTriplePrime_reembed_internalEdges_le (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.internalEdges ≤ (A.contractWithStars starOf).internalEdges := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  have hmapid : γ.internalEdges.map (A.retargetEdge starOf) = γ.internalEdges := by
    conv_rhs => rw [← Multiset.map_id γ.internalEdges]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hs),
      A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj ht)]
    rfl
  rw [← hmapid]
  exact Multiset.map_le_map (phi4WTriplePrime_internalEdges_le_complementEdges A γ hdisj)

/-- **body-603 (Step 0) — survivor external-legs support** (clean re-derivation). -/
theorem phi4WTriplePrime_reembed_externalLegs_le (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.externalLegs ≤ (A.contractWithStars starOf).externalLegs := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  have hmapid : γ.externalLegs.map (A.retargetExternalLeg starOf) = γ.externalLegs := by
    conv_rhs => rw [← Multiset.map_id γ.externalLegs]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj (γ.legs_supported ℓ hℓ))]
    rfl
  rw [← hmapid]
  exact Multiset.map_le_map γ.externalLegs_le

/-! ## Step 1 — the quotient ambient + the right-component index -/

/-- **body-603 (Step 1) — the quotient ambient of a W‴ split choice.**  The `selectedOuter` forest
star-contracted to its canonical stars. -/
noncomputable def phi4WTriplePrime_selectedOuterContractGraph
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) : ResolvedFeynmanGraph :=
  (phi4WTriplePrime_selectedOuter s).contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s))

/-- **body-603 (Step 1) — a component is RIGHT-chosen** (its split choice is `Sum.inl false`). -/
def phi4WTriplePrime_isRightComponent (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
    s.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inl false

/-- **body-603 (Step 1) — the right-component set.** -/
noncomputable def phi4WTriplePrime_rightComponents
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    Finset (ResolvedFeynmanSubgraph G) :=
  s.outer.elements.filter (phi4WTriplePrime_isRightComponent s)

theorem phi4WTriplePrime_mem_rightComponents
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G} :
    γ ∈ phi4WTriplePrime_rightComponents s ↔
      γ ∈ s.outer.elements ∧ phi4WTriplePrime_isRightComponent s γ := by
  simp only [phi4WTriplePrime_rightComponents, Finset.mem_filter]

/-! ## Step 2 — a right primitive avoids `selectedOuter` -/

/-- **body-603 (Step 2) — a right-primitive component is disjoint from the contracted forest.** -/
theorem phi4WTriplePrime_rightComponent_disjoint_selectedOuter
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    Disjoint γ.vertices (phi4WTriplePrime_selectedOuter s).vertices := by
  obtain ⟨h, hchoice⟩ := hγR
  rw [ResolvedAdmissibleSubgraph.vertices, Finset.disjoint_biUnion_right]
  intro c hc
  rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, hcleft⟩ | hP
  · obtain ⟨h', hc_true⟩ := hcleft
    have hne : γ ≠ c := by
      rintro rfl
      have hcontra := hchoice.symm.trans hc_true
      simp at hcontra
    exact s.outer.pairwiseDisjoint h hcmem hne
  · obtain ⟨γ', hγ', B, hchoice', δ, hδ, rfl⟩ := hP
    have hne : γ ≠ γ' := by
      rintro rfl
      have hcontra := hchoice.symm.trans hchoice'
      simp at hcontra
    have hdd : γ.Disjoint γ' := s.outer.pairwiseDisjoint h hγ' hne
    exact Finset.disjoint_of_subset_right
      (phi4WTriplePrime_rootRelativeInner_vertices_subset γ' δ) hdd

/-! ## Step 3 — the clean survivor re-embedding -/

/-- **body-603 (Step 3) — the concrete right survivor** in the quotient ambient, built directly from the
instance-free `ResolvedFeynmanSubgraph.reembed` and the clean Step-0 support facts. -/
noncomputable def phi4WTriplePrime_survivor (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {γ : ResolvedFeynmanSubgraph G} (hγR : phi4WTriplePrime_isRightComponent s γ) :
    ResolvedFeynmanSubgraph (phi4WTriplePrime_selectedOuterContractGraph s) :=
  γ.reembed
    (phi4WTriplePrime_reembed_vertices_subset (phi4WTriplePrime_selectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) γ
      (phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR))
    (phi4WTriplePrime_reembed_internalEdges_le (phi4WTriplePrime_selectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) γ
      (phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR))
    (phi4WTriplePrime_reembed_externalLegs_le (phi4WTriplePrime_selectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) γ
      (phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR))

@[simp] theorem phi4WTriplePrime_survivor_vertices
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).vertices = γ.vertices := rfl

@[simp] theorem phi4WTriplePrime_survivor_internalEdges
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).internalEdges = γ.internalEdges := rfl

@[simp] theorem phi4WTriplePrime_survivor_externalLegs
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).externalLegs = γ.externalLegs := rfl

/-- **body-603 (Step 3) — the survivor carries `γ`'s intrinsic resolved graph** (the clean
generator-data anchor for body-605, standing in for the forbidden-class `resolvedComponentGen`). -/
@[simp] theorem phi4WTriplePrime_survivor_toResolvedFeynmanGraph
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).toResolvedFeynmanGraph = γ.toResolvedFeynmanGraph := rfl

/-! ## Step 4 — the retarget fixes γ-membership (shared engine of the degree calc) -/

/-- **body-603 (Step 4) — the canonical star of `selectedOuter` is fresh** (outside `G`). -/
theorem phi4WTriplePrime_selectedOuter_star_not_mem_vertices
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ (phi4WTriplePrime_selectedOuter s).elements) :
    phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s) δ ∉ G.vertices := by
  have hpf := phi4WTriplePrime_selectedOuter_isProperForest s
  have hEq : phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s) δ
      = cleanStarOf phi4DivergenceMeasureFamily (phi4WTriplePrime_selectedOuter s) hpf δ := by
    show cleanStarOfTotal phi4DivergenceMeasureFamily G (phi4WTriplePrime_selectedOuter s) δ = _
    unfold cleanStarOfTotal
    rw [dif_pos hpf]
  rw [hEq]
  exact cleanStarOf_not_mem_vertices _ hpf hδ

/-- **body-603 (Step 4) — the `selectedOuter` retarget fixes `γ`-membership.** -/
theorem phi4WTriplePrime_retargetVertex_mem_iff
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hdisj : Disjoint γ.vertices (phi4WTriplePrime_selectedOuter s).vertices) (v : VertexId) :
    (phi4WTriplePrime_selectedOuter s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) v ∈ γ.vertices
      ↔ v ∈ γ.vertices := by
  set A := phi4WTriplePrime_selectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  by_cases hvA : v ∈ A.vertices
  · have hval : A.retargetVertex starOf v = starOf (A.componentAt hvA) := by
      simp only [ResolvedAdmissibleSubgraph.retargetVertex, A.componentAt?_of_mem hvA]
    rw [hval]
    constructor
    · intro hmem
      exact absurd (γ.vertices_subset hmem)
        (phi4WTriplePrime_selectedOuter_star_not_mem_vertices s (A.componentAt_mem hvA))
    · intro hmem
      exact absurd hmem (Finset.disjoint_right.mp hdisj hvA)
  · rw [A.retargetVertex_of_not_mem starOf hvA]

/-! ## Step 4 — the boundary-edge count preservation (the load-bearing lemma) -/

/-- **body-603 (Step 4, CRUX) — the survivor's induced boundary count equals `γ`'s.**  Since `γ` is
disjoint from `A`, retargeting fixes every `γ`-endpoint (and sends `A`-endpoints to fresh stars outside
`γ`), so an edge is a `γ`-boundary edge after retargeting iff it was before — and the retarget is a
cardinality-preserving `map`.  Hence the boundary counts agree. -/
theorem phi4WTriplePrime_survivor_boundaryEdgeCount_eq
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).forget.boundaryEdgeCount = γ.forget.boundaryEdgeCount := by
  set A := phi4WTriplePrime_selectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  set r := A.retargetEdge starOf with hr
  have hdisj : Disjoint γ.vertices A.vertices :=
    phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR
  set Bd : FeynmanEdge → Prop := γ.forget.IsBoundaryEdge with hBd
  -- γ-internal edges (both endpoints inside γ) fail Bd
  have hγfail : (γ.internalEdges.map ResolvedFeynmanEdge.forget).filter Bd = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    simp only [hBd, FeynmanSubgraph.IsBoundaryEdge, ResolvedFeynmanSubgraph.forget_vertices,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h ht
    · exact h hs
  -- A-internal edges (both endpoints inside A, hence outside γ) fail Bd
  have hAfail : (A.internalEdges.filter (fun e => Bd e.forget)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨hsA, htA⟩ : e.source ∈ A.vertices ∧ e.target ∈ A.vertices := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
      obtain ⟨δ, hδ, heδ⟩ := he
      obtain ⟨hsδ, htδ⟩ := δ.edges_supported e heδ
      exact ⟨ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, hsδ⟩,
        ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, htδ⟩⟩
    have hsγ : e.source ∉ γ.vertices := Finset.disjoint_right.mp hdisj hsA
    have htγ : e.target ∉ γ.vertices := Finset.disjoint_right.mp hdisj htA
    simp only [hBd, FeynmanSubgraph.IsBoundaryEdge, ResolvedFeynmanSubgraph.forget_vertices,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hsγ h
    · exact htγ h
  -- `γ` boundary edges = the `Bd`-filter of the ambient internal edges
  have hγbd : γ.forget.boundaryEdges = (G.internalEdges.map ResolvedFeynmanEdge.forget).filter Bd := by
    show (G.forget.internalEdges - γ.forget.internalEdges).filter Bd = _
    simp only [ResolvedFeynmanGraph.forget_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    rw [Multiset.filter_sub, hγfail, Multiset.sub_zero]
  -- the survivor boundary edges = the `Bd`-filter of the retargeted ambient internal edges
  have hsbd : (phi4WTriplePrime_survivor s hγR).forget.boundaryEdges
      = ((A.complementEdges.map r).map ResolvedFeynmanEdge.forget).filter Bd := by
    show ((phi4WTriplePrime_selectedOuterContractGraph s).forget.internalEdges
        - (γ.internalEdges.map ResolvedFeynmanEdge.forget)).filter Bd = _
    simp only [phi4WTriplePrime_selectedOuterContractGraph, ResolvedFeynmanGraph.forget_internalEdges,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
    rw [Multiset.filter_sub, hγfail, Multiset.sub_zero]
  -- assemble the counts
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [hsbd, hγbd, Multiset.map_map, Multiset.filter_map, Multiset.filter_map,
    Multiset.card_map, Multiset.card_map]
  simp only [Function.comp]
  -- retarget preserves γ-boundary-ness on the complement edges
  have hpred : ∀ e ∈ A.complementEdges, Bd (r e).forget ↔ Bd e.forget := by
    intro e _
    have hs := phi4WTriplePrime_retargetVertex_mem_iff s hdisj e.source
    have ht := phi4WTriplePrime_retargetVertex_mem_iff s hdisj e.target
    simp only [hBd, hr, ResolvedAdmissibleSubgraph.retargetEdge, FeynmanSubgraph.IsBoundaryEdge,
      ResolvedFeynmanSubgraph.forget_vertices, ResolvedFeynmanEdge.forget_retarget,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  congr 1
  show (G.internalEdges - A.internalEdges).filter (fun e => Bd e.forget) = _
  rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]

/-- **body-603 (Step 4) — the survivor's φ⁴ physical external valence equals `γ`'s.** -/
theorem phi4WTriplePrime_survivor_physicalExternalLegCount_eq
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).forget.physicalExternalLegCount
      = γ.forget.physicalExternalLegCount := by
  have hleg : (phi4WTriplePrime_survivor s hγR).forget.externalLegs.card
      = γ.forget.externalLegs.card := rfl
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [phi4WTriplePrime_survivor_boundaryEdgeCount_eq s hγR, hleg]

/-- **body-603 (Step 4, VICTORY) — the right survivor is φ⁴ connected-divergent** on the quotient ambient.
Connectivity and 1PI transport definitionally (shared intrinsic graph); divergence transports through the
degree equality via the explicit φ⁴ criterion — NO ambient-invariance class. -/
theorem phi4WTriplePrime_survivor_isConnectedDivergent
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    (phi4WTriplePrime_survivor s hγR).forget.IsConnectedDivergent := by
  have h : γ ∈ s.outer.elements := hγR.choose
  have hCDγ : γ.forget.IsConnectedDivergent := s.outer.isConnectedDivergent γ h
  refine ⟨hCDγ.1, hCDγ.2.1, ?_⟩
  have hpelc := phi4WTriplePrime_survivor_physicalExternalLegCount_eq s hγR
  have hdivγ : γ.forget.physicalExternalLegCount ≤ 4 := (phi4_isDivergent_iff γ.forget).mp hCDγ.2.2
  exact (phi4_isDivergent_iff _).mpr (by rw [hpelc]; exact hdivγ)

/-- **body-603 (Step 4) — the survivor is externally-leg saturated on the quotient ambient.** -/
theorem phi4WTriplePrime_survivor_saturated
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    ResolvedExternalLegSaturated (phi4WTriplePrime_selectedOuterContractGraph s)
      (phi4WTriplePrime_survivor s hγR) := by
  set A := phi4WTriplePrime_selectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  have hdisj : Disjoint γ.vertices A.vertices :=
    phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR
  have h : γ ∈ s.outer.elements := hγR.choose
  have hγsat : ResolvedExternalLegSaturated G γ :=
    (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.1) γ h
  show (phi4WTriplePrime_selectedOuterContractGraph s).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ (phi4WTriplePrime_survivor s hγR).vertices)
      ≤ (phi4WTriplePrime_survivor s hγR).externalLegs
  simp only [phi4WTriplePrime_survivor_vertices, phi4WTriplePrime_survivor_externalLegs,
    phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  rw [Multiset.filter_map]
  simp only [Function.comp]
  have hpred : ∀ ℓ ∈ G.externalLegs,
      (A.retargetExternalLeg starOf ℓ).attachedTo ∈ γ.vertices ↔ ℓ.attachedTo ∈ γ.vertices := by
    intro ℓ _
    show A.retargetVertex starOf ℓ.attachedTo ∈ γ.vertices ↔ ℓ.attachedTo ∈ γ.vertices
    exact phi4WTriplePrime_retargetVertex_mem_iff s hdisj ℓ.attachedTo
  rw [Multiset.filter_congr hpred]
  have hmapid : (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γ.vertices)).map
      (A.retargetExternalLeg starOf)
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γ.vertices) := by
    conv_rhs => rw [← Multiset.map_id (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γ.vertices))]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hℓγ : ℓ.attachedTo ∈ γ.vertices := (Multiset.mem_filter.mp hℓ).2
    show A.retargetExternalLeg starOf ℓ = id ℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hℓγ)]
    rfl
  rw [hmapid]
  exact hγsat

/-- **body-603 (Step 4) — the survivor is internal-edge complete on the quotient ambient.** -/
theorem phi4WTriplePrime_survivor_edgeComplete
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G}
    (hγR : phi4WTriplePrime_isRightComponent s γ) :
    ResolvedInternalEdgeComplete (phi4WTriplePrime_survivor s hγR) := by
  set A := phi4WTriplePrime_selectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  set r := A.retargetEdge starOf with hr
  have hdisj : Disjoint γ.vertices A.vertices :=
    phi4WTriplePrime_rightComponent_disjoint_selectedOuter s hγR
  have h : γ ∈ s.outer.elements := hγR.choose
  have hγEC : ResolvedInternalEdgeComplete γ := phi4EdgeCompleteSplitChoice_forestEdgeComplete s γ h
  show (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges.filter
      (fun e => e.source ∈ (phi4WTriplePrime_survivor s hγR).vertices
        ∧ e.target ∈ (phi4WTriplePrime_survivor s hγR).vertices)
      ≤ (phi4WTriplePrime_survivor s hγR).internalEdges
  simp only [phi4WTriplePrime_survivor_vertices, phi4WTriplePrime_survivor_internalEdges,
    phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  set P : ResolvedFeynmanEdge → Prop := fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices with hP
  rw [Multiset.filter_map]
  simp only [Function.comp]
  have hpred : ∀ e ∈ A.complementEdges, P (r e) ↔ P e := by
    intro e _
    have hs := phi4WTriplePrime_retargetVertex_mem_iff s hdisj e.source
    have ht := phi4WTriplePrime_retargetVertex_mem_iff s hdisj e.target
    simp only [hP, hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  have hmapid : (A.complementEdges.filter P).map r = A.complementEdges.filter P := by
    conv_rhs => rw [← Multiset.map_id (A.complementEdges.filter P)]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hsγ, htγ⟩ : P e := (Multiset.mem_filter.mp he).2
    show r e = id e
    simp only [hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hsγ),
      A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj htγ)]
    rfl
  rw [hmapid]
  exact le_trans (Multiset.filter_le_filter P (Multiset.sub_le_self G.internalEdges A.internalEdges)) hγEC

/-! ## Step 5 — the right-survivor forest -/

/-- **body-603 (Step 5) — the survivor map is injective on right components.** -/
theorem phi4WTriplePrime_survivor_injOn
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {γ₁ : ResolvedFeynmanSubgraph G} (hγ₁ : phi4WTriplePrime_isRightComponent s γ₁)
    {γ₂ : ResolvedFeynmanSubgraph G} (hγ₂ : phi4WTriplePrime_isRightComponent s γ₂)
    (h : phi4WTriplePrime_survivor s hγ₁ = phi4WTriplePrime_survivor s hγ₂) : γ₁ = γ₂ := by
  apply ResolvedFeynmanSubgraph.ext
  · have := congrArg ResolvedFeynmanSubgraph.vertices h
    simpa only [phi4WTriplePrime_survivor_vertices] using this
  · have := congrArg ResolvedFeynmanSubgraph.internalEdges h
    simpa only [phi4WTriplePrime_survivor_internalEdges] using this
  · have := congrArg ResolvedFeynmanSubgraph.externalLegs h
    simpa only [phi4WTriplePrime_survivor_externalLegs] using this

/-- **body-603 (Step 5) — the right-survivor forest** in the quotient ambient. -/
noncomputable def phi4WTriplePrime_rightSurvivorForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedAdmissibleSubgraph (phi4WTriplePrime_selectedOuterContractGraph s) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_rightComponents s).attach.image
      (fun γR => phi4WTriplePrime_survivor s
        ((phi4WTriplePrime_mem_rightComponents s).mp γR.2).2))
    (by
      intro δ hδ
      obtain ⟨γR, -, rfl⟩ := Finset.mem_image.mp hδ
      exact phi4WTriplePrime_survivor_isConnectedDivergent s _)
    (by
      intro δ hδ δ' hδ' hne
      obtain ⟨γR₁, -, rfl⟩ := Finset.mem_image.mp hδ
      obtain ⟨γR₂, -, rfl⟩ := Finset.mem_image.mp hδ'
      have hγ₁ := ((phi4WTriplePrime_mem_rightComponents s).mp γR₁.2)
      have hγ₂ := ((phi4WTriplePrime_mem_rightComponents s).mp γR₂.2)
      have hγne : γR₁.1 ≠ γR₂.1 := fun heq => hne (by rw [Subtype.ext heq])
      show _root_.Disjoint (phi4WTriplePrime_survivor s hγ₁.2).vertices
        (phi4WTriplePrime_survivor s hγ₂.2).vertices
      simp only [phi4WTriplePrime_survivor_vertices]
      exact s.outer.pairwiseDisjoint hγ₁.1 hγ₂.1 hγne)

@[simp] theorem phi4WTriplePrime_rightSurvivorForest_elements
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_rightSurvivorForest s).elements
      = (phi4WTriplePrime_rightComponents s).attach.image
          (fun γR => phi4WTriplePrime_survivor s
            ((phi4WTriplePrime_mem_rightComponents s).mp γR.2).2) := rfl

end GaugeGeometry.QFT.Combinatorial
