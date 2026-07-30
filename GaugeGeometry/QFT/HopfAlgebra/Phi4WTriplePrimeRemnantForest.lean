import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRemnantComponent

/-!
# QFT-R1-body-605 — remnant closure + generator transport + remnantForest

Body-604 proved the contract-twice raw equality
`(remnantComponent o).boundaryCompletedResolvedGraph = (localContractGraph o).mapPerm (remnantTau o)`.
This body PROJECTS that decontraction theorem onto every consumer:

* **CD** — the decompleted remnant is φ⁴ connected-divergent on the quotient ambient `Q`
  (`phi4WTriplePrime_remnant_isConnectedDivergent`), by an EXPLICIT boundary-completion degree recovery
  (`physicalExternalLegCount` matching via body-561 `self_physicalExternalLegCount` + body-589
  `resolvedBoundaryEdges_forget` / `boundaryCompletedResolvedExternalLegs_card`), never by any
  ambient-invariance class.
* **sixth axis** — external-leg saturation (`phi4WTriplePrime_remnant_saturated`), directly `le_of_eq`.
* **seventh axis** — internal-edge completeness (`phi4WTriplePrime_remnant_edgeComplete`), count-safe.
* **generator** — the clean `rightTerm` equality (`phi4WTriplePrime_remnant_rightTerm_eq`), via
  `Subtype.ext` on the `toResolvedHopfGenFor` class components (NO polluted `resolvedComponentGen`).

It then assembles the remnant region into a concrete admissible forest `phi4WTriplePrime_remnantForest`.

HALT compliance: axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); ZERO forbidden divergence
classes in any declaration's type (the survivor-embed stack and `resolvedComponentGen` are NOT consumed).
No `sorry` / `admit` / `native_decide`.  We do NOT claim `remnantForest.elements.Nonempty`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst605 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — CD transport (boundary-completion degree recovery) -/

/-- **body-605 (Step 1) — the decompleted remnant is φ⁴ connected-divergent on the quotient ambient `Q`.**
Path: the inner W‴ CD of `localContractGraph` at the class level, transported through the correcting
permutation `τ` (`toResolvedClass_mapPerm`) and the body-604 HEADLINE to the boundary-completed remnant's
class, then landed as its SELF-CD via `isConnectedDivergentFor_toResolvedClass`.  Connectivity / 1PI transport
through body-568's `boundaryCompletedGraph_is{SupportConnected,OnePI}_iff`; divergence through the EXPLICIT
degree recovery `physicalExternalLegCount(remnant) = (completed-self).externalLegs.card` (body-561 + 589),
never by an ambient-invariance class. -/
theorem phi4WTriplePrime_remnant_isConnectedDivergent
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).forget.IsConnectedDivergent := by
  -- 1. class CD of localContractGraph (inner W‴ CD source)
  have hCDloc : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (phi4WTriplePrime_localContractGraph o).toResolvedClass :=
    phi4WTriplePrimeCanonicalSupply.hCD o.γ.1.boundaryCompletedResolvedGraph o.B.1 o.B.2
  -- 2+3. the τ vanishes at the class level; the HEADLINE reconstructs the completed remnant
  have hcls : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.toResolvedClass
      = (phi4WTriplePrime_localContractGraph o).toResolvedClass := by
    rw [phi4WTriplePrime_remnant_contractTwice o, ResolvedFeynmanGraph.toResolvedClass_mapPerm]
  have hCDbc : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.toResolvedClass := by
    rw [hcls]; exact hCDloc
  -- 4. self-CD of the boundary-completed remnant graph
  obtain ⟨hWF, hself⟩ := (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph).mp hCDbc
  -- the forgotten completed graph is the flat boundary completion of `remnant.forget`
  have hforget : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget
      = (phi4WTriplePrime_remnantComponent o).forget.boundaryCompletedGraph :=
    boundaryCompletedResolvedGraph_forget _
  -- 5. degree recovery: physicalExternalLegCount(remnant) = (completed-self).externalLegs.card
  have hRfcard : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget.externalLegs.card
      = (phi4WTriplePrime_remnantComponent o).externalLegs.card
        + (phi4WTriplePrime_remnantComponent o).resolvedBoundaryEdges.card := by
    rw [ResolvedFeynmanGraph.forget_externalLegs, Multiset.card_map,
      boundaryCompletedResolvedGraph_externalLegs, boundaryCompletedResolvedExternalLegs_card]
  have hdeg : (phi4WTriplePrime_remnantComponent o).forget.physicalExternalLegCount
      = (phi4WTriplePrime_remnantComponent o).externalLegs.card
        + (phi4WTriplePrime_remnantComponent o).resolvedBoundaryEdges.card := by
    unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
      FeynmanSubgraph.boundaryEdgeCount
    rw [ResolvedFeynmanSubgraph.forget_externalLegs, Multiset.card_map,
      ← resolvedBoundaryEdges_forget, Multiset.card_map]
  -- transport the divergence numerically (strips the dependent `self`)
  have hle : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget.externalLegs.card
      ≤ 4 := by
    have h3 := (phi4_isDivergent_iff (FeynmanSubgraph.self
      (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget hWF)).mp hself.2.2
    rwa [FeynmanSubgraph.self_physicalExternalLegCount hWF] at h3
  refine ⟨?_, ?_, ?_⟩
  · -- IsConnected
    have hc : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget.IsSupportConnected :=
      hself.1
    rw [hforget] at hc
    exact (FeynmanSubgraph.boundaryCompletedGraph_isSupportConnected_iff _).mp hc
  · -- IsOnePI
    have ho : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget.IsOnePI :=
      hself.2.1
    rw [hforget] at ho
    exact (FeynmanSubgraph.boundaryCompletedGraph_isOnePI_iff _).mp ho
  · -- IsDivergent, via the degree recovery
    refine (phi4_isDivergent_iff _).mpr ?_
    rw [hdeg, ← hRfcard]
    exact hle

/-! ## Step 2 — quotient-ambient closure (sixth + seventh axes) -/

/-- **body-605 (Step 2, sixth axis) — the decompleted remnant is externally-leg saturated on `Q`.**
Its external legs are already the DECOMPLETED ambient filter over its vertices, so this is `le_refl`. -/
theorem phi4WTriplePrime_remnant_saturated
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ResolvedExternalLegSaturated (phi4WTriplePrime_selectedOuterContractGraph s)
      (phi4WTriplePrime_remnantComponent o) := by
  show (phi4WTriplePrime_selectedOuterContractGraph s).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ (phi4WTriplePrime_remnantComponent o).vertices)
      ≤ (phi4WTriplePrime_remnantComponent o).externalLegs
  rw [phi4WTriplePrime_remnantComponent_vertices, phi4WTriplePrime_remnantComponent_externalLegs]

/-- **body-605 (Step 2) — the inner forest's internal edges embed (with multiplicity) into `selectedOuter`'s.**
The promoted components carry `B.1`'s internal edges and sit inside `selectedOuter`, so the sub-sum is `≤`
the full sum. -/
theorem phi4WTriplePrime_inner_internalEdges_le
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    o.B.1.internalEdges ≤ (phi4WTriplePrime_selectedOuter s).internalEdges := by
  have hPsub : ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        o.γ.1.boundaryCompletedResolvedGraph o.B.1).image (rootRelativeInner o.γ.1))
      ⊆ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
          (phi4WTriplePrime_selectedOuter s) := by
    rw [Finset.image_subset_iff]
    intro δ hδ
    exact phi4WTriplePrime_remnant_promoted_mem o hδ
  have hPsum : ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        o.γ.1.boundaryCompletedResolvedGraph o.B.1).image (rootRelativeInner o.γ.1)).sum
        (fun c => c.internalEdges) = o.B.1.internalEdges := by
    rw [Finset.sum_image
      (fun δ₁ h₁ δ₂ h₂ h => phi4WTriplePrime_rootRelativeInner_injOn o h₁ h₂ h)]
    show (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1).sum
          (fun δ => (rootRelativeInner o.γ.1 δ).internalEdges)
        = o.B.1.internalEdges
    exact Finset.sum_congr rfl (fun δ _ => rootRelativeInner_internalEdges o.γ.1 δ)
  calc o.B.1.internalEdges
      = ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
          o.γ.1.boundaryCompletedResolvedGraph o.B.1).image (rootRelativeInner o.γ.1)).sum
          (fun c => c.internalEdges) := hPsum.symm
    _ ≤ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
          (phi4WTriplePrime_selectedOuter s)).sum (fun c => c.internalEdges) :=
        Finset.sum_le_sum_of_subset hPsub
    _ = (phi4WTriplePrime_selectedOuter s).internalEdges := rfl

/-- **body-605 (Step 2, seventh axis) — the decompleted remnant is internal-edge complete on `Q`.**  A
`Q`-edge with both endpoints in the remnant region descends (KEY membership iff) to a `γ`-doubly-inside
ambient edge; `γ`'s own edge-completeness (`count G ≤ count γ`) and `B.1.internalEdges ≤ selectedOuter`
close the count inequality on the shared retarget image. -/
theorem phi4WTriplePrime_remnant_edgeComplete
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    ResolvedInternalEdgeComplete (phi4WTriplePrime_remnantComponent o) := by
  show (phi4WTriplePrime_selectedOuterContractGraph s).internalEdges.filter
      (fun e => e.source ∈ (phi4WTriplePrime_remnantComponent o).vertices
        ∧ e.target ∈ (phi4WTriplePrime_remnantComponent o).vertices)
      ≤ (phi4WTriplePrime_remnantComponent o).internalEdges
  rw [phi4WTriplePrime_remnantComponent_vertices, phi4WTriplePrime_remnantComponent_internalEdges,
    phi4WTriplePrime_remnant_internalEdges_eq o, phi4WTriplePrime_selectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.filter_map]
  simp only [Function.comp]
  apply Multiset.map_le_map
  -- goal: selectedOuter.complementEdges.filter (P ∘ r_Q) ≤ B.1.complementEdges
  have hpred : ∀ e ∈ (phi4WTriplePrime_selectedOuter s).complementEdges,
      (((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e).source
        ∈ ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices
      ∧ ((phi4WTriplePrime_selectedOuter s).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)) e).target
        ∈ ((phi4WTriplePrime_localContractGraph o).mapPerm (phi4WTriplePrime_remnantTau o)).vertices)
      ↔ (e.source ∈ o.γ.1.vertices ∧ e.target ∈ o.γ.1.vertices) := by
    intro e he
    have hsG : e.source ∈ G.vertices :=
      ((phi4WTriplePrime_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
    have htG : e.target ∈ G.vertices :=
      ((phi4WTriplePrime_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
    have hs := phi4WTriplePrime_phi_mem_Ltau_iff o hsG
    have ht := phi4WTriplePrime_phi_mem_Ltau_iff o htG
    simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  -- count-safe: selectedOuter.complementEdges.filter Pγ ≤ B.1.complementEdges
  rw [Multiset.le_iff_count]
  intro e
  by_cases hP : e.source ∈ o.γ.1.vertices ∧ e.target ∈ o.γ.1.vertices
  · rw [Multiset.count_filter, if_pos hP]
    -- count e selectedOuter.complementEdges ≤ count e B.1.complementEdges
    have hcompSel : Multiset.count e (phi4WTriplePrime_selectedOuter s).complementEdges
        = Multiset.count e G.internalEdges
          - Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges := by
      show Multiset.count e (G.internalEdges - (phi4WTriplePrime_selectedOuter s).internalEdges) = _
      rw [Multiset.count_sub]
    have hcompB : Multiset.count e o.B.1.complementEdges
        = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
      show Multiset.count e ((o.γ.1.boundaryCompletedResolvedGraph).internalEdges
            - o.B.1.internalEdges) = _
      rw [Multiset.count_sub, boundaryCompletedResolvedGraph_internalEdges]
    rw [hcompSel, hcompB]
    -- γ edge-complete: count e G.I ≤ count e γ.I
    have hEC : ResolvedInternalEdgeComplete o.γ.1 :=
      phi4EdgeCompleteSplitChoice_forestEdgeComplete s o.γ.1 o.γ.2
    have hi : Multiset.count e G.internalEdges ≤ Multiset.count e o.γ.1.internalEdges := by
      have hcnt := Multiset.le_iff_count.mp hEC e
      rwa [Multiset.count_filter, if_pos hP] at hcnt
    -- inner ≤ selectedOuter
    have hii : Multiset.count e o.B.1.internalEdges
        ≤ Multiset.count e (phi4WTriplePrime_selectedOuter s).internalEdges :=
      Multiset.count_le_of_le e (phi4WTriplePrime_inner_internalEdges_le o)
    omega
  · rw [Multiset.count_filter, if_neg hP]
    exact Nat.zero_le _

/-! ## Step 3 — clean rightTerm / generator equality (no polluted `resolvedComponentGen`) -/

/-- **body-605 (Step 3) — the completed remnant carries the local contracted class.**  From the body-604
HEADLINE, the correcting permutation `τ` vanishes at the class level. -/
theorem phi4WTriplePrime_remnant_completed_class_eq
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.toResolvedClass
      = (phi4WTriplePrime_localContractGraph o).toResolvedClass := by
  rw [phi4WTriplePrime_remnant_contractTwice o, ResolvedFeynmanGraph.toResolvedClass_mapPerm]

/-- **body-605 (Step 3) — the clean generator/rightTerm equality.**  The owner-summand right term of the
inner forest `B` equals `X` of the boundary-completed remnant's family generator.  Both sides are `X` of a
`ResolvedHopfGenFor` subtype whose `.val` is the respective `toResolvedClass`; the classes agree (Step 3
`_class_eq`) and the CD witnesses enter proof-irrelevantly (`Subtype.ext`).  `resolvedComponentGen` (forbidden
class-polluted) is NOT consumed. -/
theorem phi4WTriplePrime_remnant_rightTerm_eq
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    (hCD : ∃ hWF : (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily
          (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self
          (phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.forget hWF)) :
    (phi4WTriplePrimeCanonicalSupply.summandSupply o.γ.1.boundaryCompletedResolvedGraph).rightTerm o.B
      = MvPolynomial.X ((phi4WTriplePrime_remnantComponent o).boundaryCompletedResolvedGraph.toResolvedHopfGenFor
          phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily hCD) := by
  show resolvedForestRightTermFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      o.B.1 (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1)
      (phi4WTriplePrimeCanonicalSupply.hCD o.γ.1.boundaryCompletedResolvedGraph o.B.1 o.B.2) = _
  unfold resolvedForestRightTermFor
  refine congrArg MvPolynomial.X (Subtype.ext ?_)
  rw [ResolvedFeynmanGraph.toResolvedHopfGenFor_val, ResolvedFeynmanGraph.toResolvedHopfGenFor_val]
  exact (phi4WTriplePrime_remnant_completed_class_eq o).symm

/-! ## Step 4 — occurrence index + nonempty / disjoint / injective -/

/-- A component of `s.outer` is FOREST-chosen (its split choice lands in the `Sum.inr` forest carrier). -/
def phi4WTriplePrime_isForestComponent (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
    ∃ B : (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx,
      s.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inr B

/-- **body-605 (Step 4) — the forest-component set.** -/
noncomputable def phi4WTriplePrime_forestComponents
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) : Finset (ResolvedFeynmanSubgraph G) :=
  s.outer.elements.filter (phi4WTriplePrime_isForestComponent s)

theorem phi4WTriplePrime_mem_forestComponents
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) {γ : ResolvedFeynmanSubgraph G} :
    γ ∈ phi4WTriplePrime_forestComponents s ↔
      γ ∈ s.outer.elements ∧ phi4WTriplePrime_isForestComponent s γ := by
  simp only [phi4WTriplePrime_forestComponents, Finset.mem_filter]

/-- **body-605 (Step 4) — the forest-choice occurrence of a forest component.**  `Classical.choose` the
witnessing membership and inner forest `B` off the `isForestComponent` existential. -/
noncomputable def phi4WTriplePrime_forestComponentOccurrence
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (γF : {x // x ∈ phi4WTriplePrime_forestComponents s}) :
    Phi4WTriplePrime_ForestChoiceOccurrence s :=
  let hForest := ((phi4WTriplePrime_mem_forestComponents s).mp γF.2).2
  { γ := ⟨γF.1, hForest.choose⟩
    B := hForest.choose_spec.choose
    hchoice := hForest.choose_spec.choose_spec }

@[simp] theorem phi4WTriplePrime_forestComponentOccurrence_owner
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (γF : {x // x ∈ phi4WTriplePrime_forestComponents s}) :
    (phi4WTriplePrime_forestComponentOccurrence γF).γ.1 = γF.1 := rfl

/-- **body-605 (Step 4) — the decompleted remnant is vertex-nonempty.**  A contracted-star witness of an
inner component lives in the remnant vertex set (inner properness gives a component; NOT derived from CD). -/
theorem phi4WTriplePrime_remnant_isNonempty
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_remnantComponent o).IsNonempty := by
  obtain ⟨δ₀, hδ₀⟩ := (phi4WTriplePrime_occ_B_isProperForest o).1
  show 0 < (phi4WTriplePrime_remnantComponent o).vertices.card
  rw [phi4WTriplePrime_remnantComponent_vertices]
  apply Finset.card_pos.mpr
  refine ⟨phi4WTriplePrime_remnantTau o
    (phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 δ₀), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨phi4WTriplePrimeCanonicalSupply.starOf o.γ.1.boundaryCompletedResolvedGraph o.B.1 δ₀, ?_, rfl⟩
  rw [phi4WTriplePrime_localContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  exact Finset.mem_union_right _
    (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δ₀, hδ₀, rfl⟩)

/-- **body-605 (Step 4) — remnant-vertex origin cases.**  Each remnant vertex is either a `γ`-vertex (`τ`
fixes it) or a global star of a promoted inner component. -/
theorem phi4WTriplePrime_remnant_vertex_mem_cases
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) {w : VertexId}
    (hw : w ∈ (phi4WTriplePrime_remnantComponent o).vertices) :
    w ∈ o.γ.1.vertices ∨
      ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        o.γ.1.boundaryCompletedResolvedGraph o.B.1,
        w = phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
          (rootRelativeInner o.γ.1 δ) := by
  rw [phi4WTriplePrime_remnantComponent_vertices] at hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [phi4WTriplePrime_localContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
  rcases hx with hxsdiff | hxstar
  · rw [Finset.mem_sdiff, boundaryCompletedResolvedGraph_vertices] at hxsdiff
    rw [phi4WTriplePrime_remnantTau_fix o (Finset.mem_sdiff.mpr hxsdiff)]
    exact Or.inl hxsdiff.1
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
    obtain ⟨δ₀, hδ₀, rfl⟩ := hxstar
    rw [phi4WTriplePrime_remnantTau_map o ⟨δ₀, hδ₀⟩]
    exact Or.inr ⟨δ₀, hδ₀, rfl⟩

/-- **body-605 (Step 4) — remnants of distinct-owner occurrences are vertex-disjoint.**  `γ`-vertices are
disjoint (`s.outer.pairwiseDisjoint`); `γ`-vertices vs promoted stars are separated by freshness; two
promoted stars coincide only if their promoted components coincide, forcing a shared component vertex into
`γ₁ ∩ γ₂ = ∅` (components are nonempty). -/
theorem phi4WTriplePrime_remnant_disjoint
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o₁ o₂ : Phi4WTriplePrime_ForestChoiceOccurrence s) (hne : o₁.γ.1 ≠ o₂.γ.1) :
    _root_.Disjoint (phi4WTriplePrime_remnantComponent o₁).vertices
      (phi4WTriplePrime_remnantComponent o₂).vertices := by
  have hpfSel := phi4WTriplePrime_selectedOuter_isProperForest s
  have hdd : o₁.γ.1.Disjoint o₂.γ.1 := s.outer.pairwiseDisjoint o₁.γ.2 o₂.γ.2 hne
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rcases phi4WTriplePrime_remnant_vertex_mem_cases o₁ hw1 with hγ1 | ⟨δ1, hδ1, hs1⟩
  · rcases phi4WTriplePrime_remnant_vertex_mem_cases o₂ hw2 with hγ2 | ⟨δ2, hδ2, hs2⟩
    · exact Finset.disjoint_left.mp hdd hγ1 hγ2
    · exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s) hpfSel
        (phi4WTriplePrime_remnant_promoted_mem o₂ hδ2) (hs2 ▸ o₁.γ.1.vertices_subset hγ1)
  · rcases phi4WTriplePrime_remnant_vertex_mem_cases o₂ hw2 with hγ2 | ⟨δ2, hδ2, hs2⟩
    · exact phi4WTriplePrime_gen_star_not_mem (phi4WTriplePrime_selectedOuter s) hpfSel
        (phi4WTriplePrime_remnant_promoted_mem o₁ hδ1) (hs1 ▸ o₂.γ.1.vertices_subset hγ2)
    · have hstar : phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
          (rootRelativeInner o₁.γ.1 δ1)
          = phi4WTriplePrimeCanonicalSupply.starOf G (phi4WTriplePrime_selectedOuter s)
              (rootRelativeInner o₂.γ.1 δ2) := hs1 ▸ hs2
      have hc12 := phi4WTriplePrime_gen_star_injOn (phi4WTriplePrime_selectedOuter s) hpfSel
        (phi4WTriplePrime_remnant_promoted_mem o₁ hδ1)
        (phi4WTriplePrime_remnant_promoted_mem o₂ hδ2) hstar
      obtain ⟨u, hu⟩ := Finset.card_pos.mp
        ((phi4WTriplePrime_occ_B_isProperForest o₁).2.1 δ1 hδ1)
      have huR1 : u ∈ (rootRelativeInner o₁.γ.1 δ1).vertices := by
        rw [rootRelativeInner_vertices]; exact hu
      have hu1 : u ∈ o₁.γ.1.vertices :=
        phi4WTriplePrime_rootRelativeInner_vertices_subset o₁.γ.1 δ1 huR1
      have huR2 : u ∈ (rootRelativeInner o₂.γ.1 δ2).vertices := hc12 ▸ huR1
      have hu2 : u ∈ o₂.γ.1.vertices :=
        phi4WTriplePrime_rootRelativeInner_vertices_subset o₂.γ.1 δ2 huR2
      exact Finset.disjoint_left.mp hdd hu1 hu2

/-- **body-605 (Step 4) — the occurrence→remnant map is injective on distinct owners.**  Distinct owners give
vertex-disjoint (hence distinct nonempty) remnants. -/
theorem phi4WTriplePrime_remnant_injOn
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}
    (o₁ o₂ : Phi4WTriplePrime_ForestChoiceOccurrence s) (hne : o₁.γ.1 ≠ o₂.γ.1) :
    phi4WTriplePrime_remnantComponent o₁ ≠ phi4WTriplePrime_remnantComponent o₂ := by
  intro heq
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (phi4WTriplePrime_remnant_isNonempty o₁)
  have hw2 : w ∈ (phi4WTriplePrime_remnantComponent o₂).vertices := by
    rw [← congrArg ResolvedFeynmanSubgraph.vertices heq]; exact hw
  exact Finset.disjoint_left.mp (phi4WTriplePrime_remnant_disjoint o₁ o₂ hne) hw hw2

/-! ## Step 5 — remnantForest assembly -/

/-- **body-605 (Step 5) — the decompleted-remnant forest** in the quotient ambient `Q`.  One remnant per
forest-choice occurrence, admissible via Step 1 (CD) + Step 4 (pairwise disjointness).  We do NOT claim
`elements.Nonempty` (a mixed left/right choice may yield an empty remnant). -/
noncomputable def phi4WTriplePrime_remnantForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (phi4WTriplePrime_selectedOuterContractGraph s) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_forestComponents s).attach.image
      (fun γF => phi4WTriplePrime_remnantComponent (phi4WTriplePrime_forestComponentOccurrence γF)))
    (by
      intro δ hδ
      obtain ⟨γF, -, rfl⟩ := Finset.mem_image.mp hδ
      exact phi4WTriplePrime_remnant_isConnectedDivergent _)
    (by
      intro δ hδ δ' hδ' hne
      obtain ⟨γF₁, -, rfl⟩ := Finset.mem_image.mp hδ
      obtain ⟨γF₂, -, rfl⟩ := Finset.mem_image.mp hδ'
      have hγRne : γF₁ ≠ γF₂ := fun h => hne (by rw [h])
      show _root_.Disjoint
        (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_forestComponentOccurrence γF₁)).vertices
        (phi4WTriplePrime_remnantComponent (phi4WTriplePrime_forestComponentOccurrence γF₂)).vertices
      exact phi4WTriplePrime_remnant_disjoint _ _ (fun h => hγRne (Subtype.ext h)))

@[simp] theorem phi4WTriplePrime_remnantForest_elements
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (phi4WTriplePrime_remnantForest s).elements
      = (phi4WTriplePrime_forestComponents s).attach.image
          (fun γF => phi4WTriplePrime_remnantComponent
            (phi4WTriplePrime_forestComponentOccurrence γF)) := rfl

/-- **body-605 (Step 5) — origin recovery.**  Every remnant-forest element is `remnantComponent o` for a
concrete forest-choice occurrence `o`. -/
theorem phi4WTriplePrime_remnantForest_element_origin
    {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G} {δ : ResolvedFeynmanSubgraph
      (phi4WTriplePrime_selectedOuterContractGraph s)}
    (hδ : δ ∈ (phi4WTriplePrime_remnantForest s).elements) :
    ∃ o : Phi4WTriplePrime_ForestChoiceOccurrence s, δ = phi4WTriplePrime_remnantComponent o := by
  rw [phi4WTriplePrime_remnantForest_elements] at hδ
  obtain ⟨γF, -, rfl⟩ := Finset.mem_image.mp hδ
  exact ⟨phi4WTriplePrime_forestComponentOccurrence γF, rfl⟩

/-- **body-605 (Step 5) — the remnant forest is externally-leg saturated** (sixth axis, componentwise). -/
theorem phi4WTriplePrime_remnantForest_forestSaturated
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestExternalLegSaturated (phi4WTriplePrime_remnantForest s) := by
  intro δ hδ
  obtain ⟨o, rfl⟩ := phi4WTriplePrime_remnantForest_element_origin hδ
  exact phi4WTriplePrime_remnant_saturated o

/-- **body-605 (Step 5) — the remnant forest is internal-edge complete** (seventh axis, componentwise). -/
theorem phi4WTriplePrime_remnantForest_forestEdgeComplete
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (phi4WTriplePrime_remnantForest s) := by
  intro γ hγ
  obtain ⟨o, rfl⟩ := phi4WTriplePrime_remnantForest_element_origin hγ
  exact phi4WTriplePrime_remnant_edgeComplete o

end GaugeGeometry.QFT.Combinatorial
