import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredParentTopology

/-!
# QFT-R1-body-611 — recovered inner component CD transport

Body-609 left the named PROOF FRONTIER `phi4WTriplePrime_inv_innerForest_CD` (the transported inner
components are connected-divergent).  This body DISCHARGES it — NOT by any ambient-invariance class, but by
the EXACT boundary bookkeeping: `γ`'s boundary edges that escape the recovered parent become external legs of
the boundary-completed ambient, exactly compensating, so the physical external valence is preserved and the
source divergence transports.

## Strategy
* Step 1 — topology transports DEFINITIONALLY: `(innerComponent I γ hγ).forget` and `γ.forget` share the
  same support graph (same `vertices` + `internalEdges`), so `IsConnected` / `IsOnePI` move by `.1` / `.2.1`
  of the outer forest's own `isConnectedDivergent γ`.
* Step 2 — the exact boundary bookkeeping (multiplicity-safe, count-level).  The EVEN legs of the inner
  component collapse to `γ`'s saturated legs; the ODD legs collapse to the `escaped` `P`-boundary edges whose
  inside endpoint lands in `γ`.  `γ`'s own `G`-boundary partitions into (edges cut inside the recovered
  parent) + (escaped edges), so the escaped count cancels between the leg identity and the boundary split.
* Step 3 — physical external valence recovery (`omega`).
* Step 4 — divergence transport (`phi4_isDivergent_iff`, NO ambient-invariance class) + assembly + frontier
  discharge.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; no ambient-invariance / preservation / reflection class; no survivor-embed /
`resolvedComponentGen` / polluted supply consumed; no parent topology/divergence re-proof (READ from
609/610); no boundary-completion RAW ID equality (only the CORRECT COUNT equality); multiplicity-safe
throughout; no `s` / `componentEquiv`; no new `class` / `structure` / permanent `instance`; no `sorry` /
`admit` / `native_decide`; no `forget` global injectivity.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst611 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## The two boundary book-keeping multisets. -/

/-- **body-611 — the `∂P γ` book-keeping multiset.**  The recovered-parent internal edges cut by `γ`'s
vertex boundary — exactly the inner component's own resolved boundary edges. -/
noncomputable def phi4WTriplePrime_inv_innerParentBoundary
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (γ : ResolvedFeynmanSubgraph G) :
    Multiset ResolvedFeynmanEdge :=
  (phi4WTriplePrime_inv_recoveredParent I).internalEdges.filter γ.resolvedIsBoundaryEdge

/-- **body-611 — the `escaped` book-keeping multiset.**  The recovered-parent boundary edges whose inside
endpoint lands in `γ` — the `γ`-boundary edges whose outside endpoint escaped the recovered parent. -/
noncomputable def phi4WTriplePrime_inv_escapedBoundary
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (γ : ResolvedFeynmanSubgraph G) :
    Multiset ResolvedFeynmanEdge :=
  (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges.filter
    (fun e => (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices)

/-! ## Step 1 — source ownership + topology transport (DEFINITIONAL). -/

/-- **body-611 (Step 1) — the transported inner component is support-connected.**  Same support graph as the
outer component `γ` (shared `vertices` + `internalEdges`), so `IsConnected` moves by `.1` of `γ`'s own source
connected-divergence.  NO new topology. -/
theorem phi4WTriplePrime_inv_innerComponent_isConnected
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.IsConnected :=
  (z.1.1.isConnectedDivergent γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)).1

/-- **body-611 (Step 1) — the transported inner component is 1PI.**  Same support graph as `γ`, so `IsOnePI`
moves by `.2.1` of `γ`'s source connected-divergence.  NO new topology. -/
theorem phi4WTriplePrime_inv_innerComponent_isOnePI
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.IsOnePI :=
  (z.1.1.isConnectedDivergent γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)).2.1

/-! ## Step 2 — the exact boundary bookkeeping. -/

/-- **body-611 (Step 2, LEG IDENTITY) — the inner component's external-leg count splits.**  Its EVEN legs
(the parent's existing legs re-encoded, filtered to `γ`) collapse — under `γ`'s external-leg saturation +
`γ.vertices ⊆ P.vertices` — to `γ`'s own legs; its ODD legs (the parent's boundary legs, filtered to `γ`)
collapse to the `escaped` edges.  Multiplicity-safe. -/
theorem phi4WTriplePrime_inv_innerComponent_externalLegs_card
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.externalLegs.card
      = γ.externalLegs.card + (phi4WTriplePrime_inv_escapedBoundary I γ).card := by
  classical
  have hγsat : ResolvedExternalLegSaturated G γ :=
    (((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.1) γ
      (phi4WTriplePrime_inv_touchedForest_subset_A hγ)
  have hγsub : γ.vertices ⊆ phi4WTriplePrime_inv_recoveredParent_verts z δ :=
    phi4WTriplePrime_inv_touchedComponent_verts_subset hγ
  have hCext : (phi4WTriplePrime_inv_innerComponent I γ hγ).externalLegs
      = (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈ γ.vertices) := rfl
  rw [ResolvedFeynmanSubgraph.forget_externalLegs, Multiset.card_map, hCext,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_externalLegs]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [Multiset.filter_add, Multiset.card_add]
  congr 1
  · -- EVEN part → γ's own legs
    rw [← Multiset.map_filter_of_iff encodeExistingLeg
          (phi4WTriplePrime_inv_recoveredParent I).externalLegs
          (fun ℓ => ℓ.attachedTo ∈ γ.vertices) (fun ℓ => ℓ.attachedTo ∈ γ.vertices) (fun _ => Iff.rfl),
       Multiset.card_map]
    congr 1
    rw [phi4WTriplePrime_inv_recoveredParent_externalLegs I,
      externalLegs_eq_filter_of_saturated γ hγsat, Multiset.filter_filter]
    apply Multiset.filter_congr
    intro ℓ _
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, hγsub h⟩
  · -- ODD part → escaped edges
    rw [← Multiset.map_filter_of_iff (phi4WTriplePrime_inv_recoveredParent I).boundaryExternalLeg
          (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges
          (fun e => (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices)
          (fun ℓ => ℓ.attachedTo ∈ γ.vertices) (fun _ => Iff.rfl),
       Multiset.card_map]
    rfl

/-- **body-611 (Step 2, BOUNDARY IDENTITY) — the inner component's induced boundary count.**  Its `forget`
boundary edges are its resolved boundary edges (`resolvedBoundaryEdges_forget`), which — over the boundary-
completed ambient's internal edges (`= P.internalEdges`) with `γ`'s vertex-boundary predicate — is exactly
`∂P γ`.  Multiplicity-safe. -/
theorem phi4WTriplePrime_inv_innerComponent_boundaryEdgeCount
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.boundaryEdgeCount
      = (phi4WTriplePrime_inv_innerParentBoundary I γ).card := by
  classical
  have hbe : (phi4WTriplePrime_inv_innerComponent I γ hγ).resolvedBoundaryEdges
      = phi4WTriplePrime_inv_innerParentBoundary I γ := by
    unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges phi4WTriplePrime_inv_innerParentBoundary
    rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges]
    apply Multiset.filter_congr
    intro e _
    exact Iff.rfl
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map, hbe]

/-- **body-611 (Step 2, γ-BOUNDARY SPLIT — the exact escaped partition) — `γ`'s `G`-boundary partitions.**
Each `γ`-boundary edge is EITHER cut inside the recovered parent (its outside endpoint stays in `P`, hence a
`P`-internal edge cut by `γ` — counted in `∂P γ`) OR escaped (its outside endpoint left `P`, hence a
`P`-boundary edge with inside endpoint in `γ`).  Mutually exclusive + exhaustive, proved count-level.
Multiplicity-safe. -/
theorem phi4WTriplePrime_inv_gamma_boundary_split
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    γ.forget.boundaryEdgeCount
      = (phi4WTriplePrime_inv_innerParentBoundary I γ).card
        + (phi4WTriplePrime_inv_escapedBoundary I γ).card := by
  classical
  have hγsub : γ.vertices ⊆ phi4WTriplePrime_inv_recoveredParent_verts z δ :=
    phi4WTriplePrime_inv_touchedComponent_verts_subset hγ
  -- a P-boundary edge with inside endpoint inside γ IS a γ-boundary edge (escaped ⇒ γ-boundary)
  have hIIto : ∀ {e : ResolvedFeynmanEdge},
      (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e
        ∧ (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices
      → γ.resolvedIsBoundaryEdge e := by
    rintro e ⟨hpbd, hpin⟩
    unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint at hpin
    unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge at hpbd ⊢
    rcases hpbd with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [if_pos hs] at hpin
      exact Or.inl ⟨hpin, fun h => ht (hγsub h)⟩
    · rw [if_neg hs] at hpin
      exact Or.inr ⟨fun h => hs (hγsub h), hpin⟩
  -- the count-level partition
  have hsplit : γ.resolvedBoundaryEdges
      = phi4WTriplePrime_inv_innerParentBoundary I γ + phi4WTriplePrime_inv_escapedBoundary I γ := by
    rw [Multiset.ext]
    intro e
    have hLHS : Multiset.count e γ.resolvedBoundaryEdges
        = if γ.resolvedIsBoundaryEdge e then Multiset.count e G.internalEdges else 0 := by
      unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
      rw [Multiset.count_filter]
    have hIPB : Multiset.count e (phi4WTriplePrime_inv_innerParentBoundary I γ)
        = if γ.resolvedIsBoundaryEdge e then
            (if (e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
                  ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
             then Multiset.count e G.internalEdges else 0) else 0 := by
      unfold phi4WTriplePrime_inv_innerParentBoundary
      rw [Multiset.count_filter,
        show (phi4WTriplePrime_inv_recoveredParent I).internalEdges
            = G.internalEdges.filter
                (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
                  ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ) from rfl,
        Multiset.count_filter]
    have hEsc : Multiset.count e (phi4WTriplePrime_inv_escapedBoundary I γ)
        = if (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices then
            (if (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e
             then Multiset.count e G.internalEdges else 0) else 0 := by
      unfold phi4WTriplePrime_inv_escapedBoundary
      rw [Multiset.count_filter,
        show (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges
            = G.internalEdges.filter (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge
          from rfl,
        Multiset.count_filter]
    rw [Multiset.count_add, hLHS, hIPB, hEsc]
    by_cases hγbd : γ.resolvedIsBoundaryEdge e
    · simp only [if_pos hγbd]
      by_cases hpb : e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
          ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      · simp only [if_pos hpb]
        have hnpbd : ¬ (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e := by
          unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge
          rintro (⟨_, h2⟩ | ⟨h1, _⟩)
          · exact h2 hpb.2
          · exact h1 hpb.1
        simp only [if_neg hnpbd, ite_self, Nat.add_zero]
      · simp only [if_neg hpb, Nat.zero_add]
        unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge at hγbd
        rcases hγbd with ⟨hs, ht⟩ | ⟨hs, ht⟩
        · have hspv : e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices := hγsub hs
          have htnpv : e.target ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices :=
            fun h => hpb ⟨hspv, h⟩
          have hPBd : (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e :=
            Or.inl ⟨hspv, htnpv⟩
          have hpin : (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices := by
            unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint; rw [if_pos hspv]; exact hs
          simp only [if_pos hpin, if_pos hPBd]
        · have htpv : e.target ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices := hγsub ht
          have hsnpv : e.source ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices :=
            fun h => hpb ⟨h, htpv⟩
          have hPBd : (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e :=
            Or.inr ⟨hsnpv, htpv⟩
          have hpin : (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices := by
            unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint; rw [if_neg hsnpv]; exact ht
          simp only [if_pos hpin, if_pos hPBd]
    · simp only [if_neg hγbd, Nat.zero_add]
      by_cases hpin : (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e ∈ γ.vertices
      · by_cases hpbd : (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e
        · exact absurd (hIIto ⟨hpbd, hpin⟩) hγbd
        · simp only [if_pos hpin, if_neg hpbd]
      · simp only [if_neg hpin]
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map, hsplit,
    Multiset.card_add]

/-! ## Step 3 — physical valence recovery. -/

/-- **body-611 (Step 3, HEADLINE) — the transported inner component preserves `γ`'s physical external
valence.**  The escaped edges are counted once as an inner external leg (ODD) and once as an outer boundary
edge; they cancel by `omega`.  NO ambient-invariance class. -/
theorem phi4WTriplePrime_inv_innerComponent_physicalExternalLegCount_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.physicalExternalLegCount
      = γ.forget.physicalExternalLegCount := by
  have hL := phi4WTriplePrime_inv_innerComponent_externalLegs_card I γ hγ
  have hB := phi4WTriplePrime_inv_innerComponent_boundaryEdgeCount I γ hγ
  have hGsplit := phi4WTriplePrime_inv_gamma_boundary_split I γ hγ
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [hL, hB, hGsplit, ResolvedFeynmanSubgraph.forget_externalLegs γ, Multiset.card_map]
  omega

/-! ## Step 4 — divergence transport + assembly + frontier discharge. -/

/-- **body-611 (Step 4) — the transported inner component is divergent.**  `γ` is divergent (its source
connected-divergence), hence `γ`'s physical valence is `≤ 4`; Step 3 transports the valence, so the inner
component is `≤ 4`, hence divergent.  Routed through `phi4_isDivergent_iff` — NO ambient-invariance /
preservation / reflection class. -/
theorem phi4WTriplePrime_inv_innerComponent_isDivergent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.IsDivergent := by
  have hCDγ : γ.forget.IsConnectedDivergent :=
    z.1.1.isConnectedDivergent γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)
  have hdivγ : γ.forget.physicalExternalLegCount ≤ 4 :=
    (phi4_isDivergent_iff γ.forget).mp hCDγ.2.2
  exact (phi4_isDivergent_iff _).mpr
    (by rw [phi4WTriplePrime_inv_innerComponent_physicalExternalLegCount_eq I γ hγ]; exact hdivγ)

/-- **body-611 (Step 4) — the transported inner component is connected-divergent.** -/
theorem phi4WTriplePrime_inv_innerComponent_isConnectedDivergent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.IsConnectedDivergent :=
  ⟨phi4WTriplePrime_inv_innerComponent_isConnected I γ hγ,
   phi4WTriplePrime_inv_innerComponent_isOnePI I γ hγ,
   phi4WTriplePrime_inv_innerComponent_isDivergent I γ hγ⟩

/-- **body-611 (VICTORY) — the body-609 `_innerForest_CD` proof frontier is DISCHARGED.**  Takes only `I`. -/
theorem phi4WTriplePrime_inv_innerForest_CD_proof
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    phi4WTriplePrime_inv_innerForest_CD I :=
  fun γ hγ => phi4WTriplePrime_inv_innerComponent_isConnectedDivergent I γ hγ

end GaugeGeometry.QFT.Combinatorial
