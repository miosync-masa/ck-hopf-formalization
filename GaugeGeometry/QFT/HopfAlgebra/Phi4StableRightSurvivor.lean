import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRightFactorQuotientAudit

/-!
# QFT-R1-body-634 — the STABLE RIGHT-survivor forest (stable-native RIGHT primitive)

Body-633 delivered the stable local RIGHT factor and the stable algebraic root, and NAMED the stable
quotient-geometry frontiers (634 right-survivor forest ; 635 remnant+quotient forest ; 636 right-factor
aggregate ; 637 two-stage `quot_eq` ; 638 summand agreement).  This body opens the **stable quotient
ambient** `stableSelectedOuterContractGraph` (star-contract the stable `selectedOuter`) and shows that every
**RIGHT-primitive** component of a stable split choice survives the contraction φ⁴-family-natively by
RE-EMBEDDING (`ResolvedFeynmanSubgraph.reembed`, the genuinely instance-free helper) into the quotient graph —
the STABLE mirror of body-603, but on the STABLE carrier `stableLocalBoundaryCompletedGraph`.

## Steps

* **Step 0 — clean re-derivation of the reembed support facts.**  The generic `reembed` support helpers are
  re-derived CLEAN under stable names (they are instance-free / forbidden-class-free, but body-603's file is not
  in this import branch, so re-derive rather than consume).
* **Step 1 — the stable quotient ambient.**  `stableSelectedOuterContractGraph` + `_stableIds` (consumes
  body-629 `stableResolvedBoundaryIds_contractWithStars` directly).
* **Step 2 — the RIGHT-component index.**  `stableIsRightComponent` / `stableRightComponents` (+ mem iff), and
  `stableRightComponent_disjoint_selectedOuter` (body-632 origin dichotomy + RIGHT-tag exclusivity + outer
  pairwise-disjointness).
* **Step 3 — the clean survivor reembedding.**  `stableRightSurvivor` + raw STRICT anchors (vertices /
  internalEdges / externalLegs / toResolvedFeynmanGraph, all `= γ`).
* **Step 4 (HEADLINE 1) — the load-bearing stable completion equality (IDs, not just counts).**
  `stableRightSurvivor_boundaryExternalLeg_retarget` (retarget fixes the RIGHT component's inside endpoint and
  never touches `edgeId`/sector), `stableRightSurvivor_resolvedBoundaryEdges_map`, and
  `stableRightSurvivor_localCompletion_eq : stableLocalBoundaryCompletedGraph (survivor) =
  stableLocalBoundaryCompletedGraph γ` — a raw `ResolvedFeynmanGraph` equality (inherited legs VERBATIM,
  boundary leg IDs and multiplicity preserved).
* **Step 5 — physics + closure.**  `_boundaryEdgeCount_eq` / `_physicalExternalLegCount_eq` /
  `_isConnectedDivergent` (φ⁴ degree computation, NO ambient-invariance class) / `_saturated` / `_edgeComplete`
  / `_injOn`.
* **Step 6 (HEADLINE 2) — the generator anchor + the forest.**
  `stableLocalRightFactor_right_eq_survivorGen` (closes by HEADLINE 1 + body-629
  `toStableResolvedPhi4HopfGen_class_eq`); `stableRightSurvivorForest` + `_elements` / `_element_origin` /
  `_forestSaturated` / `_forestEdgeComplete`.

## HALT / red lines
Body-625's no-go and bodies 629-633 are UNEDITED; the OLD carrier / coproduct / split choice are FROZEN.  NO
global correcting permutation; NO frozen `phi4WTriplePrime_rightSurvivor*` owner consumed; NO old-choice adapter
/ naive `γ.boundaryCompletedResolvedGraph`; NO `survivorReembed*` polluted stack.  The stable remnant / quotient
forest (635), the right-factor aggregate / `quot_eq` (636/637), and summand agreement (638) are NOT entered.  NO
survivor-forest `Nonempty` / `IsProperForest` / W‴-membership claim.  ZERO new `structure` / `class` / permanent
`instance` (one file-local `local instance` for the φ⁴ family); ZERO forbidden divergence class in any
declaration TYPE; ZERO `sorry` / `admit` / `native_decide`; NO public `HEq` / `cast` / graph-data `▸`; NO
`toFinset` / dedup / orbit quotient.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 1600000

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family (mirrors body-629/632/633), so
the resolved admissible-subgraph / contraction / carrier plumbing elaborates against the φ⁴ family. -/
local instance instPhi4DivergenceMeasureFamily634 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — clean re-derivation of the reembed support facts (instance-free) -/

/-- **body-634 (Step 0) — survivor vertices support** (clean re-derivation). -/
theorem stableRight_reembed_vertices_subset (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (γ : ResolvedFeynmanSubgraph G)
    (hdisj : Disjoint γ.vertices A.vertices) :
    γ.vertices ⊆ (A.contractWithStars starOf).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  intro v hv
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨γ.vertices_subset hv,
    Finset.disjoint_left.mp hdisj hv⟩)

/-- **body-634 (Step 0) — an edge of an admissible subgraph has its source in its vertices** (clean). -/
theorem stableRight_source_mem_vertices (A : ResolvedAdmissibleSubgraph G)
    {e : ResolvedFeynmanEdge} (he : e ∈ A.internalEdges) : e.source ∈ A.vertices := by
  simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
  obtain ⟨δ, hδ, heδ⟩ := he
  exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ, hδ, (δ.edges_supported e heδ).1⟩

/-- **body-634 (Step 0) — survivor edge-complement bound from vertex disjointness** (clean). -/
theorem stableRight_internalEdges_le_complementEdges (A : ResolvedAdmissibleSubgraph G)
    (γ : ResolvedFeynmanSubgraph G) (hdisj : Disjoint γ.vertices A.vertices) :
    γ.internalEdges ≤ A.complementEdges := by
  have hdisj_edges : ∀ e, e ∈ γ.internalEdges → e ∈ A.internalEdges → False :=
    fun e heγ heA => Finset.disjoint_left.mp hdisj (γ.edges_supported e heγ).1
      (stableRight_source_mem_vertices A heA)
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

/-- **body-634 (Step 0) — survivor internal-edges support** (clean re-derivation). -/
theorem stableRight_reembed_internalEdges_le (A : ResolvedAdmissibleSubgraph G)
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
  exact Multiset.map_le_map (stableRight_internalEdges_le_complementEdges A γ hdisj)

/-- **body-634 (Step 0) — survivor external-legs support** (clean re-derivation). -/
theorem stableRight_reembed_externalLegs_le (A : ResolvedAdmissibleSubgraph G)
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

/-! ## Step 1 — the stable quotient ambient + the RIGHT-component index -/

/-- **body-634 (Step 1) — the stable quotient ambient of a stable split choice.**  The `stableSelectedOuter`
forest star-contracted to its canonical stars. -/
noncomputable def stableSelectedOuterContractGraph {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) : ResolvedFeynmanGraph :=
  (stableSelectedOuter s).contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s))

/-- **body-634 (Step 1) — the stable quotient ambient OWNS the stable boundary-ID certificate** (consuming
body-629's contraction closure directly). -/
theorem stableSelectedOuterContractGraph_stableIds {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    StableResolvedBoundaryIds (stableSelectedOuterContractGraph s) :=
  stableResolvedBoundaryIds_contractWithStars (stableSelectedOuter s)
    (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) hSt

/-- **body-634 (Step 2) — a component is RIGHT-chosen** (its stable split choice is `Sum.inl false`). -/
def stableIsRightComponent {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
    s.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inl false

/-- **body-634 (Step 2) — the RIGHT-component set. -/
noncomputable def stableRightComponents {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) : Finset (ResolvedFeynmanSubgraph G) :=
  s.outer.elements.filter (stableIsRightComponent s)

theorem stableMem_rightComponents {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G} :
    γ ∈ stableRightComponents s ↔
      γ ∈ s.outer.elements ∧ stableIsRightComponent s γ := by
  simp only [stableRightComponents, Finset.mem_filter]

/-! ## Step 2 — a RIGHT primitive avoids `stableSelectedOuter` -/

/-- **body-634 (Step 2) — a RIGHT-primitive component is disjoint from the contracted stable forest.** -/
theorem stableRightComponent_disjoint_selectedOuter {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    Disjoint γ.vertices (stableSelectedOuter s).vertices := by
  obtain ⟨h, hchoice⟩ := hγR
  rw [ResolvedAdmissibleSubgraph.vertices, Finset.disjoint_biUnion_right]
  intro c hc
  rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, hcleft⟩ | hP
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
      (stableRootRelativeInner_vertices_subset γ' δ) hdd

/-! ## Step 3 — the clean survivor re-embedding -/

/-- **body-634 (Step 3) — the concrete RIGHT survivor** in the stable quotient ambient, built directly from
the instance-free `ResolvedFeynmanSubgraph.reembed` and the clean Step-0 support facts. -/
noncomputable def stableRightSurvivor {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s) :=
  γ.reembed
    (stableRight_reembed_vertices_subset (stableSelectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) γ
      (stableRightComponent_disjoint_selectedOuter s hγR))
    (stableRight_reembed_internalEdges_le (stableSelectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) γ
      (stableRightComponent_disjoint_selectedOuter s hγR))
    (stableRight_reembed_externalLegs_le (stableSelectedOuter s)
      (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) γ
      (stableRightComponent_disjoint_selectedOuter s hγR))

@[simp] theorem stableRightSurvivor_vertices {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).vertices = γ.vertices := rfl

@[simp] theorem stableRightSurvivor_internalEdges {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).internalEdges = γ.internalEdges := rfl

@[simp] theorem stableRightSurvivor_externalLegs {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).externalLegs = γ.externalLegs := rfl

/-- **body-634 (Step 3) — the survivor carries `γ`'s intrinsic resolved graph** (the clean generator-data
anchor). -/
@[simp] theorem stableRightSurvivor_toResolvedFeynmanGraph {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).toResolvedFeynmanGraph = γ.toResolvedFeynmanGraph := rfl

/-! ## Step 4 — the retarget fixes γ-membership (shared engine) + HEADLINE 1 -/

/-- **body-634 (Step 4) — the canonical star of `stableSelectedOuter` is fresh** (outside `G`). -/
theorem stableSelectedOuter_star_not_mem_vertices {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ (stableSelectedOuter s).elements) :
    phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s) δ ∉ G.vertices := by
  have hpf := stableSelectedOuter_isProperForest s
  have hEq : phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s) δ
      = cleanStarOf phi4DivergenceMeasureFamily (stableSelectedOuter s) hpf δ := by
    show cleanStarOfTotal phi4DivergenceMeasureFamily G (stableSelectedOuter s) δ = _
    unfold cleanStarOfTotal
    rw [dif_pos hpf]
  rw [hEq]
  exact cleanStarOf_not_mem_vertices _ hpf hδ

/-- **body-634 (Step 4) — the `stableSelectedOuter` retarget fixes `γ`-membership.** -/
theorem stableRetargetVertex_mem_iff {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hdisj : Disjoint γ.vertices (stableSelectedOuter s).vertices) (v : VertexId) :
    (stableSelectedOuter s).retargetVertex
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) v ∈ γ.vertices
      ↔ v ∈ γ.vertices := by
  set A := stableSelectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  by_cases hvA : v ∈ A.vertices
  · have hval : A.retargetVertex starOf v = starOf (A.componentAt hvA) := by
      simp only [ResolvedAdmissibleSubgraph.retargetVertex, A.componentAt?_of_mem hvA]
    rw [hval]
    constructor
    · intro hmem
      exact absurd (γ.vertices_subset hmem)
        (stableSelectedOuter_star_not_mem_vertices s (A.componentAt_mem hvA))
    · intro hmem
      exact absurd hmem (Finset.disjoint_right.mp hdisj hvA)
  · rw [A.retargetVertex_of_not_mem starOf hvA]

/-- **body-634 (Step 4) — the retarget of a `γ`-boundary edge induces the SAME boundary leg.**  The
`edgeId` (hence the ODD `boundaryLegId`) and the `sector` are carried through retarget verbatim; the inside
endpoint sits in `γ` and is fixed by the retarget.  This is the ID-preserving heart of HEADLINE 1. -/
theorem stableRightSurvivor_boundaryExternalLeg_retarget {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hdisj : Disjoint γ.vertices (stableSelectedOuter s).vertices)
    {e : ResolvedFeynmanEdge} (hbe : γ.resolvedIsBoundaryEdge e) :
    γ.boundaryExternalLeg ((stableSelectedOuter s).retargetEdge
        (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s)) e)
      = γ.boundaryExternalLeg e := by
  set A := stableSelectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  have hattach : γ.resolvedInsideEndpoint (A.retargetEdge starOf e)
      = γ.resolvedInsideEndpoint e := by
    unfold resolvedInsideEndpoint ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    simp only
    have hsrc := stableRetargetVertex_mem_iff s hdisj e.source
    have htgt := stableRetargetVertex_mem_iff s hdisj e.target
    by_cases hs : e.source ∈ γ.vertices
    · rw [if_pos (hsrc.mpr hs), if_pos hs,
        A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hs)]
    · rw [if_neg (fun hc => hs (hsrc.mp hc)), if_neg hs]
      have ht : e.target ∈ γ.vertices := by
        rcases hbe with ⟨hs', _⟩ | ⟨_, ht⟩
        · exact absurd hs' hs
        · exact ht
      rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj ht)]
  unfold boundaryExternalLeg
  exact congr (congr (congrArg ResolvedExternalLeg.mk rfl) hattach) rfl

/-- **body-634 (Step 4, CRUX) — the survivor's induced boundary legs are `γ`'s, IDs and multiplicity.**
The survivor's boundary edges are the `γ`-boundary complement edges retargeted (endpoints only); each induces
the same `boundaryExternalLeg`, and the `A`-internal edges fail the `γ`-boundary predicate, so the whole
inherited boundary-leg multiset matches `γ`'s verbatim. -/
theorem stableRightSurvivor_resolvedBoundaryEdges_map {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).resolvedBoundaryEdges.map (stableRightSurvivor s hγR).boundaryExternalLeg
      = γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg := by
  set A := stableSelectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  set r := A.retargetEdge starOf with hr
  have hdisj : Disjoint γ.vertices A.vertices :=
    stableRightComponent_disjoint_selectedOuter s hγR
  set P : ResolvedFeynmanEdge → Prop := γ.resolvedIsBoundaryEdge with hP
  -- the survivor boundary edges (over the quotient ambient's internal edges, defeq γ-predicate/leg)
  have hLHS : (stableRightSurvivor s hγR).resolvedBoundaryEdges.map
        (stableRightSurvivor s hγR).boundaryExternalLeg
      = ((A.complementEdges.map r).filter P).map γ.boundaryExternalLeg := by
    show ((stableSelectedOuterContractGraph s).internalEdges.filter P).map γ.boundaryExternalLeg = _
    rfl
  have hRHS : γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg
      = (G.internalEdges.filter P).map γ.boundaryExternalLeg := rfl
  rw [hLHS, hRHS]
  -- A-internal edges fail the γ-boundary predicate
  have hAfail : A.internalEdges.filter P = 0 := by
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
    simp only [hP, resolvedIsBoundaryEdge]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hsγ h
    · exact htγ h
  -- the RHS filter collapses onto the complement edges
  have hGfilter : G.internalEdges.filter P = A.complementEdges.filter P := by
    unfold ResolvedAdmissibleSubgraph.complementEdges
    rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]
  rw [hGfilter, Multiset.filter_map]
  simp only [Multiset.map_map]
  -- retarget preserves γ-boundary-ness on complement edges
  have hpred : ∀ e ∈ A.complementEdges, (P ∘ r) e ↔ P e := by
    intro e _
    simp only [Function.comp_apply]
    have hsrc := stableRetargetVertex_mem_iff s hdisj e.source
    have htgt := stableRetargetVertex_mem_iff s hdisj e.target
    simp only [hP, hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
      resolvedIsBoundaryEdge]
    rw [hsrc, htgt]
  rw [Multiset.filter_congr hpred]
  -- on γ-boundary complement edges the boundary leg is retarget-invariant
  apply Multiset.map_congr rfl
  intro e he
  have hbe : P e := (Multiset.mem_filter.mp he).2
  show γ.boundaryExternalLeg (r e) = γ.boundaryExternalLeg e
  exact stableRightSurvivor_boundaryExternalLeg_retarget s hdisj hbe

/-- **body-634 (Step 4, HEADLINE 1) — the load-bearing stable completion equality.**  The survivor's stable
local boundary completion equals the source `γ`'s: same vertices / internal edges (verbatim), inherited legs
VERBATIM, and induced boundary legs matched by IDs and multiplicity (Step 4 CRUX).  A raw
`ResolvedFeynmanGraph` equality — NOT weakened to a class equality or a card-only shortcut. -/
theorem stableRightSurvivor_localCompletion_eq {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    stableLocalBoundaryCompletedGraph (stableRightSurvivor s hγR)
      = stableLocalBoundaryCompletedGraph γ := by
  have hlegs : (stableRightSurvivor s hγR).externalLegs
        + (stableRightSurvivor s hγR).resolvedBoundaryEdges.map
            (stableRightSurvivor s hγR).boundaryExternalLeg
      = γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg := by
    rw [stableRightSurvivor_externalLegs, stableRightSurvivor_resolvedBoundaryEdges_map]
  show (⟨(stableRightSurvivor s hγR).vertices, (stableRightSurvivor s hγR).internalEdges,
      (stableRightSurvivor s hγR).externalLegs
        + (stableRightSurvivor s hγR).resolvedBoundaryEdges.map
            (stableRightSurvivor s hγR).boundaryExternalLeg⟩ : ResolvedFeynmanGraph)
    = ⟨γ.vertices, γ.internalEdges, γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg⟩
  exact congr (congr (congrArg ResolvedFeynmanGraph.mk rfl) rfl) hlegs

/-! ## Step 5 — physics + closure -/

/-- **body-634 (Step 5) — the survivor's induced boundary count equals `γ`'s** (from HEADLINE 1). -/
theorem stableRightSurvivor_boundaryEdgeCount_eq {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).forget.boundaryEdgeCount = γ.forget.boundaryEdgeCount := by
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget,
    ← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget γ, Multiset.card_map, Multiset.card_map]
  have := stableRightSurvivor_resolvedBoundaryEdges_map s hγR
  have hcard := congrArg Multiset.card this
  rwa [Multiset.card_map, Multiset.card_map] at hcard

/-- **body-634 (Step 5) — the survivor's φ⁴ physical external valence equals `γ`'s.** -/
theorem stableRightSurvivor_physicalExternalLegCount_eq {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).forget.physicalExternalLegCount
      = γ.forget.physicalExternalLegCount := by
  have hleg : (stableRightSurvivor s hγR).forget.externalLegs.card
      = γ.forget.externalLegs.card := rfl
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [stableRightSurvivor_boundaryEdgeCount_eq s hγR, hleg]

/-- **body-634 (Step 5, VICTORY) — the RIGHT survivor is φ⁴ connected-divergent** on the stable quotient
ambient.  Connectivity / 1PI transport definitionally (shared intrinsic graph); divergence transports through
the degree equality via the explicit φ⁴ criterion — NO ambient-invariance class. -/
theorem stableRightSurvivor_isConnectedDivergent {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    (stableRightSurvivor s hγR).forget.IsConnectedDivergent := by
  have h : γ ∈ s.outer.elements := hγR.choose
  have hCDγ : γ.forget.IsConnectedDivergent := s.outer.isConnectedDivergent γ h
  refine ⟨hCDγ.1, hCDγ.2.1, ?_⟩
  have hpelc := stableRightSurvivor_physicalExternalLegCount_eq s hγR
  have hdivγ : γ.forget.physicalExternalLegCount ≤ 4 := (phi4_isDivergent_iff γ.forget).mp hCDγ.2.2
  exact (phi4_isDivergent_iff _).mpr (by rw [hpelc]; exact hdivγ)

/-- **body-634 (Step 5) — the survivor is externally-leg saturated on the stable quotient ambient.** -/
theorem stableRightSurvivor_saturated {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    ResolvedExternalLegSaturated (stableSelectedOuterContractGraph s)
      (stableRightSurvivor s hγR) := by
  set A := stableSelectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  have hdisj : Disjoint γ.vertices A.vertices :=
    stableRightComponent_disjoint_selectedOuter s hγR
  have h : γ ∈ s.outer.elements := hγR.choose
  have hγsat : ResolvedExternalLegSaturated G γ :=
    (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.1) γ h
  show (stableSelectedOuterContractGraph s).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ (stableRightSurvivor s hγR).vertices)
      ≤ (stableRightSurvivor s hγR).externalLegs
  simp only [stableRightSurvivor_vertices, stableRightSurvivor_externalLegs,
    stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  rw [Multiset.filter_map]
  simp only [Function.comp]
  have hpred : ∀ ℓ ∈ G.externalLegs,
      (A.retargetExternalLeg starOf ℓ).attachedTo ∈ γ.vertices ↔ ℓ.attachedTo ∈ γ.vertices := by
    intro ℓ _
    show A.retargetVertex starOf ℓ.attachedTo ∈ γ.vertices ↔ ℓ.attachedTo ∈ γ.vertices
    exact stableRetargetVertex_mem_iff s hdisj ℓ.attachedTo
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

/-- **body-634 (Step 5) — the survivor is internal-edge complete on the stable quotient ambient.** -/
theorem stableRightSurvivor_edgeComplete {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ) :
    ResolvedInternalEdgeComplete (stableRightSurvivor s hγR) := by
  set A := stableSelectedOuter s with hA
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstarOf
  set r := A.retargetEdge starOf with hr
  have hdisj : Disjoint γ.vertices A.vertices :=
    stableRightComponent_disjoint_selectedOuter s hγR
  have h : γ ∈ s.outer.elements := hγR.choose
  have hγEC : ResolvedInternalEdgeComplete γ :=
    (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.2) γ h
  show (stableSelectedOuterContractGraph s).internalEdges.filter
      (fun e => e.source ∈ (stableRightSurvivor s hγR).vertices
        ∧ e.target ∈ (stableRightSurvivor s hγR).vertices)
      ≤ (stableRightSurvivor s hγR).internalEdges
  simp only [stableRightSurvivor_vertices, stableRightSurvivor_internalEdges,
    stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  set Q : ResolvedFeynmanEdge → Prop := fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices with hQ
  rw [Multiset.filter_map]
  simp only [Function.comp]
  have hpred : ∀ e ∈ A.complementEdges, Q (r e) ↔ Q e := by
    intro e _
    have hs := stableRetargetVertex_mem_iff s hdisj e.source
    have ht := stableRetargetVertex_mem_iff s hdisj e.target
    simp only [hQ, hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  have hmapid : (A.complementEdges.filter Q).map r = A.complementEdges.filter Q := by
    conv_rhs => rw [← Multiset.map_id (A.complementEdges.filter Q)]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hsγ, htγ⟩ : Q e := (Multiset.mem_filter.mp he).2
    show r e = id e
    simp only [hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hsγ),
      A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj htγ)]
    rfl
  rw [hmapid]
  exact le_trans (Multiset.filter_le_filter Q (Multiset.sub_le_self G.internalEdges A.internalEdges)) hγEC

/-- **body-634 (Step 5) — the survivor map is injective on RIGHT components.** -/
theorem stableRightSurvivor_injOn {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    {γ₁ : ResolvedFeynmanSubgraph G} (hγ₁ : stableIsRightComponent s γ₁)
    {γ₂ : ResolvedFeynmanSubgraph G} (hγ₂ : stableIsRightComponent s γ₂)
    (h : stableRightSurvivor s hγ₁ = stableRightSurvivor s hγ₂) : γ₁ = γ₂ := by
  apply ResolvedFeynmanSubgraph.ext
  · have := congrArg ResolvedFeynmanSubgraph.vertices h
    simpa only [stableRightSurvivor_vertices] using this
  · have := congrArg ResolvedFeynmanSubgraph.internalEdges h
    simpa only [stableRightSurvivor_internalEdges] using this
  · have := congrArg ResolvedFeynmanSubgraph.externalLegs h
    simpa only [stableRightSurvivor_externalLegs] using this

/-! ## Step 6 — the generator anchor (HEADLINE 2) + the RIGHT-survivor forest -/

/-- **body-634 (Step 6, HEADLINE 2) — the stable local RIGHT factor's RIGHT-primitive value is the survivor's
stable generator.**  The RIGHT-primitive branch of body-633's `stableLocalRightFactor` is the boundary-completed
stable generator of `γ`; HEADLINE 1 (survivor completion `= γ` completion) closes it against the survivor's
generator via body-629's `toStableResolvedPhi4HopfGen_class_eq`.  NO frozen generator equality consumed. -/
theorem stableLocalRightFactor_right_eq_survivorGen {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G}
    (hγR : stableIsRightComponent s γ)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    stableLocalRightFactor hSt γ hCDγ (Sum.inl false)
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph (stableRightSurvivor s hγR)).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent (stableRightSurvivor s hγR)
            (stableRightSurvivor_isConnectedDivergent s hγR))
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph (stableRightSurvivor s hγR)
            (stableSelectedOuterContractGraph_stableIds s))) := by
  rw [stableLocalRightFactor_inl_false]
  exact congrArg MvPolynomial.X
    (toStableResolvedPhi4HopfGen_class_eq _ _ _ _
      (congrArg ResolvedFeynmanGraph.toResolvedClass (stableRightSurvivor_localCompletion_eq s hγR).symm))

/-- **body-634 (Step 6) — the RIGHT-survivor forest** in the stable quotient ambient. -/
noncomputable def stableRightSurvivorForest {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    ResolvedAdmissibleSubgraph (stableSelectedOuterContractGraph s) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((stableRightComponents s).attach.image
      (fun γR => stableRightSurvivor s
        ((stableMem_rightComponents s).mp γR.2).2))
    (by
      intro δ hδ
      obtain ⟨γR, -, rfl⟩ := Finset.mem_image.mp hδ
      exact stableRightSurvivor_isConnectedDivergent s _)
    (by
      intro δ hδ δ' hδ' hne
      obtain ⟨γR₁, -, rfl⟩ := Finset.mem_image.mp hδ
      obtain ⟨γR₂, -, rfl⟩ := Finset.mem_image.mp hδ'
      have hγ₁ := ((stableMem_rightComponents s).mp γR₁.2)
      have hγ₂ := ((stableMem_rightComponents s).mp γR₂.2)
      have hγne : γR₁.1 ≠ γR₂.1 := fun heq => hne (by rw [Subtype.ext heq])
      show _root_.Disjoint (stableRightSurvivor s hγ₁.2).vertices
        (stableRightSurvivor s hγ₂.2).vertices
      simp only [stableRightSurvivor_vertices]
      exact s.outer.pairwiseDisjoint hγ₁.1 hγ₂.1 hγne)

@[simp] theorem stableRightSurvivorForest_elements {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    (stableRightSurvivorForest s).elements
      = (stableRightComponents s).attach.image
          (fun γR => stableRightSurvivor s
            ((stableMem_rightComponents s).mp γR.2).2) := rfl

/-- **body-634 (Step 6) — every element of the RIGHT-survivor forest is a survivor of a RIGHT component.** -/
theorem stableRightSurvivorForest_element_origin {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {δ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s)}
    (hδ : δ ∈ (stableRightSurvivorForest s).elements) :
    ∃ (γ : ResolvedFeynmanSubgraph G) (hγR : stableIsRightComponent s γ),
      δ = stableRightSurvivor s hγR := by
  rw [stableRightSurvivorForest_elements] at hδ
  obtain ⟨γR, -, rfl⟩ := Finset.mem_image.mp hδ
  exact ⟨γR.1, ((stableMem_rightComponents s).mp γR.2).2, rfl⟩

/-- **body-634 (Step 6) — the RIGHT-survivor forest is external-leg saturated** (every component). -/
theorem stableRightSurvivorForest_forestSaturated {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    ResolvedForestExternalLegSaturated (stableRightSurvivorForest s) := by
  intro δ hδ
  obtain ⟨γ, hγR, rfl⟩ := stableRightSurvivorForest_element_origin s hδ
  exact stableRightSurvivor_saturated s hγR

/-- **body-634 (Step 6) — the RIGHT-survivor forest is internal-edge complete** (every component). -/
theorem stableRightSurvivorForest_forestEdgeComplete {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (stableRightSurvivorForest s) := by
  intro δ hδ
  obtain ⟨γ, hγR, rfl⟩ := stableRightSurvivorForest_element_origin s hδ
  exact stableRightSurvivor_edgeComplete s hγR

end GaugeGeometry.QFT.Combinatorial
