import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRemnantComponent

/-!
# QFT-R1-body-636 — STABLE remnant closure + generator transport + remnantForest

Body-635 proved the STABLE contract-twice raw equality
`stableLocalBoundaryCompletedGraph (stableRemnantComponent o) = (stableLocalContractGraph o).mapPerm (stableRemnantTau o)`.
This body PROJECTS that decontraction theorem onto every consumer, on the STABLE carrier, and assembles the
remnant region into a concrete admissible forest.  It is the STABLE mirror of body-605 — reproduced CLEAN;
body-605's old-choice-keyed decls are NOT consumed, the argument is mirrored.

* **Step 1 — CD** (`stableRemnant_isConnectedDivergent`): the decompleted stable remnant is φ⁴
  connected-divergent on the quotient ambient `Q = stableSelectedOuterContractGraph s.1`, by an EXPLICIT
  boundary-completion degree recovery (`stableResolvedSubgraph_physicalExternalLegCount_forget` from body-631,
  the completed self card, and body-568's flat-completion topology iffs), never by any ambient-invariance
  class.  CD source: the inner W‴ class-CD of `stableLocalContractGraph`, transported through the correcting
  permutation `τ` (`toResolvedClass_mapPerm`) and body-635's HEADLINE `stableRemnant_completed_class_eq`.
* **Step 2 — sixth/seventh axes + nonemptiness**: `stableRemnant_externalLegSaturated` (`le_refl`, the legs are
  already the decompleted ambient filter); `stableRemnant_internalEdgeComplete` (count-safe, from body-635's
  vertices/internalEdges anchors + `γ`'s edge-completeness + inner-into-outer edge embedding);
  `stableRemnant_isNonempty` (a contracted-star witness of an inner component, from inner properness — NOT
  derived from CD).
* **Step 3 — stable right-term match**: `stableRemnant_rightTerm_eq` and
  `stableLocalRightFactor_forest_eq_remnantGen` (directly feeds body-633's forest branch factor), via
  `Subtype.ext` on the `toStableResolvedPhi4HopfGen` class components + body-635 `stableRemnant_completed_class_eq`;
  proof-owner differences absorbed by proof irrelevance.  The old `resolvedComponentGen` is NOT consumed.
* **Step 4 — occurrence geometry**: `stableRemnant_origin` (γ-vertex OR promoted-star), `stableRemnant_pairwiseDisjoint`
  (distinct owners → vertex-disjoint), `stableRemnant_injOn` (distinct owners → distinct remnants).
* **Step 5 — remnant forest**: `stableRemnantForest s` built via `Finset.image` over forest-choice occurrences,
  with `stableRemnantForest_elements` / `_component_cd` / `_externalLegSaturated` / `_internalEdgeComplete` /
  `_rightTerm`.  Image injectivity keeps the component multiplicity exact.

## HALT / red lines
Body-625's no-go and bodies 629-635 / the old carrier are UNEDITED.  We do NOT claim
`stableRemnantForest.elements.Nonempty`; `IsProperForest` / complement positivity / W‴ membership are NOT
entered.  The survivor∪union / quotientForest (637), the aggregate right-factor product (638), `quot_eq` (639)
are NOT entered.  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance` for the
φ⁴ family); ZERO forbidden divergence class in any declaration TYPE (`IsAmbientInvariantDivergence` NOT used);
ZERO `sorry` / `admit` / `native_decide`; NO `HEq` / `cast` / graph-data `▸`; NO `toFinset` / dedup / global `τ`.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily636 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-! ## Step 1 — CD transport (boundary-completion degree recovery) -/

/-- **body-636 (Step 1) — the decompleted stable remnant is φ⁴ connected-divergent on the quotient ambient
`Q`.**  The inner W‴ CD of `stableLocalContractGraph` at the class level is transported through the correcting
permutation `τ` (`toResolvedClass_mapPerm`) and body-635's HEADLINE `stableRemnant_completed_class_eq` to the
boundary-completed remnant's class, then landed as its SELF-CD via `isConnectedDivergentFor_toResolvedClass`.
Connectivity / 1PI transport through body-568's `boundaryCompletedGraph_is{SupportConnected,OnePI}_iff`;
divergence through the EXPLICIT degree recovery `physicalExternalLegCount(remnant) = (completed-self).externalLegs.card`
(body-631 forget count + the completed self card), never by an ambient-invariance class. -/
theorem stableRemnant_isConnectedDivergent (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).forget.IsConnectedDivergent := by
  -- 1. class CD of stableLocalContractGraph (inner W‴ CD source)
  have hCDloc : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (stableLocalContractGraph o).toResolvedClass :=
    phi4WTriplePrimeCanonicalSupply.hCD (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 o.B.2
  -- 2+3. the τ vanishes at the class level; the HEADLINE reconstructs the completed remnant
  have hcls : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toResolvedClass
      = (stableLocalContractGraph o).toResolvedClass := stableRemnant_completed_class_eq o
  have hCDbc : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toResolvedClass := by
    rw [hcls]; exact hCDloc
  -- 4. self-CD of the boundary-completed remnant graph
  obtain ⟨hWF, hself⟩ := (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    (stableLocalBoundaryCompletedGraph (stableRemnantComponent o))).mp hCDbc
  -- the forgotten completed graph is the flat boundary completion of `remnant.forget`
  have hforget : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget
      = (stableRemnantComponent o).forget.boundaryCompletedGraph :=
    stableLocalBoundaryCompletedGraph_forget (stableRemnantComponent o)
  -- 5. degree recovery: physicalExternalLegCount(remnant) = (completed-self).externalLegs.card
  have hRfcard : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.externalLegs.card
      = (stableRemnantComponent o).externalLegs.card
        + (stableRemnantComponent o).resolvedBoundaryEdges.card := by
    rw [ResolvedFeynmanGraph.forget_externalLegs, Multiset.card_map,
      stableLocalBoundaryCompletedGraph_externalLegs, Multiset.card_add, Multiset.card_map]
  have hdeg : (stableRemnantComponent o).forget.physicalExternalLegCount
      = (stableRemnantComponent o).externalLegs.card
        + (stableRemnantComponent o).resolvedBoundaryEdges.card :=
    stableResolvedSubgraph_physicalExternalLegCount_forget (stableRemnantComponent o)
  -- transport the divergence numerically (strips the dependent `self`)
  have hle : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.externalLegs.card ≤ 4 := by
    have h3 := (phi4_isDivergent_iff (FeynmanSubgraph.self
      (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget hWF)).mp hself.2.2
    rwa [FeynmanSubgraph.self_physicalExternalLegCount hWF] at h3
  refine ⟨?_, ?_, ?_⟩
  · -- IsConnected
    have hc : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.IsSupportConnected :=
      hself.1
    rw [hforget] at hc
    exact (FeynmanSubgraph.boundaryCompletedGraph_isSupportConnected_iff _).mp hc
  · -- IsOnePI
    have ho : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.IsOnePI :=
      hself.2.1
    rw [hforget] at ho
    exact (FeynmanSubgraph.boundaryCompletedGraph_isOnePI_iff _).mp ho
  · -- IsDivergent, via the degree recovery
    refine (phi4_isDivergent_iff _).mpr ?_
    rw [hdeg, ← hRfcard]
    exact hle

/-! ## Step 2 — quotient-ambient closure (sixth + seventh axes) + nonemptiness -/

/-- **body-636 (Step 2, sixth axis) — the decompleted stable remnant is externally-leg saturated on `Q`.**
Its external legs are already the DECOMPLETED ambient filter over its vertices, so this is `le_refl`. -/
theorem stableRemnant_externalLegSaturated (o : StableForestChoiceOccurrence s) :
    ResolvedExternalLegSaturated (stableSelectedOuterContractGraph s.1) (stableRemnantComponent o) := by
  show (stableSelectedOuterContractGraph s.1).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ (stableRemnantComponent o).vertices)
      ≤ (stableRemnantComponent o).externalLegs
  rw [stableRemnantComponent_vertices, stableRemnantComponent_externalLegs]

/-- **body-636 (Step 2) — the stable inner forest's internal edges embed (with multiplicity) into
`stableSelectedOuter`'s.**  The promoted components carry `B.1`'s internal edges and sit inside `stableSelectedOuter`,
so the sub-sum is `≤` the full sum. -/
theorem stableRemnant_inner_internalEdges_le (o : StableForestChoiceOccurrence s) :
    o.B.1.internalEdges ≤ (stableSelectedOuter s.1).internalEdges := by
  have hPsub : ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).image (stableRootRelativeInner o.γ.1))
      ⊆ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableSelectedOuter s.1) := by
    rw [Finset.image_subset_iff]
    intro δ hδ
    exact stableRemnant_promoted_mem o hδ
  have hPsum : ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).image (stableRootRelativeInner o.γ.1)).sum
        (fun c => c.internalEdges) = o.B.1.internalEdges := by
    rw [Finset.sum_image
      (fun δ₁ h₁ δ₂ h₂ h => stableRemnant_rootRelativeInner_injOn o h₁ h₂ h)]
    show (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).sum
          (fun δ => (stableRootRelativeInner o.γ.1 δ).internalEdges)
        = o.B.1.internalEdges
    exact Finset.sum_congr rfl (fun δ _ => stableRootRelativeInner_internalEdges o.γ.1 δ)
  calc o.B.1.internalEdges
      = ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
          (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1).image (stableRootRelativeInner o.γ.1)).sum
          (fun c => c.internalEdges) := hPsum.symm
    _ ≤ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
          (stableSelectedOuter s.1)).sum (fun c => c.internalEdges) :=
        Finset.sum_le_sum_of_subset hPsub
    _ = (stableSelectedOuter s.1).internalEdges := rfl

/-- **body-636 (Step 2, seventh axis) — the decompleted stable remnant is internal-edge complete on `Q`.**  A
`Q`-edge with both endpoints in the remnant region descends (body-635 KEY membership iff) to a `γ`-doubly-inside
ambient edge; `γ`'s own edge-completeness and `B.1.internalEdges ≤ stableSelectedOuter` close the count
inequality on the shared retarget image. -/
theorem stableRemnant_internalEdgeComplete (o : StableForestChoiceOccurrence s) :
    ResolvedInternalEdgeComplete (stableRemnantComponent o) := by
  show (stableSelectedOuterContractGraph s.1).internalEdges.filter
      (fun e => e.source ∈ (stableRemnantComponent o).vertices
        ∧ e.target ∈ (stableRemnantComponent o).vertices)
      ≤ (stableRemnantComponent o).internalEdges
  rw [stableRemnantComponent_vertices, stableRemnantComponent_internalEdges,
    stableRemnant_internalEdges_eq o, stableSelectedOuterContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.filter_map]
  simp only [Function.comp]
  apply Multiset.map_le_map
  -- goal: stableSelectedOuter.complementEdges.filter (P ∘ r_Q) ≤ B.1.complementEdges
  have hpred : ∀ e ∈ (stableSelectedOuter s.1).complementEdges,
      (((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e).source
        ∈ ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices
      ∧ ((stableSelectedOuter s.1).retargetEdge
          (phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)) e).target
        ∈ ((stableLocalContractGraph o).mapPerm (stableRemnantTau o)).vertices)
      ↔ (e.source ∈ o.γ.1.vertices ∧ e.target ∈ o.γ.1.vertices) := by
    intro e he
    have hsG : e.source ∈ G.vertices :=
      ((stableRemnant_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
    have htG : e.target ∈ G.vertices :=
      ((stableRemnant_ambient o).1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
    have hs := stableRemnant_phi_mem_Ltau_iff o hsG
    have ht := stableRemnant_phi_mem_Ltau_iff o htG
    simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  -- count-safe: stableSelectedOuter.complementEdges.filter Pγ ≤ B.1.complementEdges
  rw [Multiset.le_iff_count]
  intro e
  by_cases hP : e.source ∈ o.γ.1.vertices ∧ e.target ∈ o.γ.1.vertices
  · rw [Multiset.count_filter, if_pos hP]
    have hcompSel : Multiset.count e (stableSelectedOuter s.1).complementEdges
        = Multiset.count e G.internalEdges
          - Multiset.count e (stableSelectedOuter s.1).internalEdges := by
      show Multiset.count e (G.internalEdges - (stableSelectedOuter s.1).internalEdges) = _
      rw [Multiset.count_sub]
    have hcompB : Multiset.count e o.B.1.complementEdges
        = Multiset.count e o.γ.1.internalEdges - Multiset.count e o.B.1.internalEdges := by
      show Multiset.count e ((stableLocalBoundaryCompletedGraph o.γ.1).internalEdges
            - o.B.1.internalEdges) = _
      rw [Multiset.count_sub, stableLocalBoundaryCompletedGraph_internalEdges]
    rw [hcompSel, hcompB]
    -- γ edge-complete: count e G.I ≤ count e γ.I
    have hEC : ResolvedInternalEdgeComplete o.γ.1 :=
      (((mem_phi4WTriplePrimeIndex G s.1.outer).mp s.1.outer_mem).2.2.2.2.2.2) o.γ.1 o.γ.2
    have hi : Multiset.count e G.internalEdges ≤ Multiset.count e o.γ.1.internalEdges := by
      have hcnt := Multiset.le_iff_count.mp hEC e
      rwa [Multiset.count_filter, if_pos hP] at hcnt
    -- inner ≤ stableSelectedOuter
    have hii : Multiset.count e o.B.1.internalEdges
        ≤ Multiset.count e (stableSelectedOuter s.1).internalEdges :=
      Multiset.count_le_of_le e (stableRemnant_inner_internalEdges_le o)
    omega
  · rw [Multiset.count_filter, if_neg hP]
    exact Nat.zero_le _

/-- **body-636 (Step 2) — the decompleted stable remnant is vertex-nonempty.**  A contracted-star witness of an
inner component lives in the remnant vertex set (inner properness gives a component; NOT derived from CD). -/
theorem stableRemnant_isNonempty (o : StableForestChoiceOccurrence s) :
    (stableRemnantComponent o).IsNonempty := by
  obtain ⟨δ₀, hδ₀⟩ := (stableForestOcc_B_isProperForest o).1
  show 0 < (stableRemnantComponent o).vertices.card
  rw [stableRemnantComponent_vertices]
  apply Finset.card_pos.mpr
  refine ⟨stableRemnantTau o
    (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 δ₀), ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 δ₀, ?_, rfl⟩
  rw [stableLocalContractGraph, ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  exact Finset.mem_union_right _
    (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨δ₀, hδ₀, rfl⟩)

/-! ## Step 3 — clean rightTerm / generator equality (no polluted `resolvedComponentGen`) -/

/-- **body-636 (Step 3) — the stable inner forest right term equals the remnant's completed generator.**  The
owner-summand stable forest right term of the inner forest `B` equals `X` of the boundary-completed remnant's
STABLE family generator.  Both sides are `X` of a `StableResolvedPhi4HopfGen` subtype whose `.val` is the
respective `toResolvedClass`; the classes agree (body-635 `stableRemnant_completed_class_eq`) and the CD /
stable-id witnesses enter proof-irrelevantly (`Subtype.ext`).  The old `resolvedComponentGen` is NOT consumed. -/
theorem stableRemnant_rightTerm_eq (o : StableForestChoiceOccurrence s)
    (hCD : ∃ hWF : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget
        (phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget)
        (FeynmanSubgraph.self (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget hWF))
    (hSt' : StableResolvedBoundaryIds (stableLocalBoundaryCompletedGraph (stableRemnantComponent o))) :
    stableForestRightTerm o.B.1
        (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
        (phi4WTriplePrimeCanonicalSupply.hCD (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1 o.B.2)
        (stableResolvedBoundaryIds_contractWithStars o.B.1
          (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph o.γ.1 hSt))
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toStableResolvedPhi4HopfGen
          hCD hSt') := by
  unfold stableForestRightTerm
  refine congrArg MvPolynomial.X (Subtype.ext ?_)
  rw [ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val,
    ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val]
  exact (stableRemnant_completed_class_eq o).symm

/-- **body-636 (Step 3) — the FOREST branch factor equals the remnant's completed generator.**  Directly feeds
body-633's `stableLocalRightFactor` forest branch: the `Sum.inr o.B` value of the stable local right factor is
`X` of the boundary-completed remnant's stable family generator (Step 3's `stableRemnant_rightTerm_eq` after the
`_inr` branch unfold). -/
theorem stableLocalRightFactor_forest_eq_remnantGen (o : StableForestChoiceOccurrence s)
    (hCDγ : o.γ.1.forget.IsConnectedDivergent)
    (hCD : ∃ hWF : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget
        (phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget)
        (FeynmanSubgraph.self (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget hWF))
    (hSt' : StableResolvedBoundaryIds (stableLocalBoundaryCompletedGraph (stableRemnantComponent o))) :
    stableLocalRightFactor hSt o.γ.1 hCDγ (Sum.inr o.B)
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toStableResolvedPhi4HopfGen
          hCD hSt') := by
  rw [stableLocalRightFactor_inr]
  exact stableRemnant_rightTerm_eq o hCD hSt'

/-! ## Step 4 — occurrence geometry (origin / disjoint / injective) -/

/-- **body-636 (Step 4) — remnant-vertex origin cases.**  Each remnant vertex is either a `γ`-vertex (`τ`
fixes it) or a global star of a promoted inner component. -/
theorem stableRemnant_origin (o : StableForestChoiceOccurrence s) {w : VertexId}
    (hw : w ∈ (stableRemnantComponent o).vertices) :
    w ∈ o.γ.1.vertices ∨
      ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1,
        w = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
          (stableRootRelativeInner o.γ.1 δ) := by
  rw [stableRemnantComponent_vertices] at hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [stableLocalContractGraph,
    ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
  rcases hx with hxsdiff | hxstar
  · rw [Finset.mem_sdiff, stableLocalBoundaryCompletedGraph_vertices] at hxsdiff
    rw [stableRemnantTau_fix o (Finset.mem_sdiff.mpr hxsdiff)]
    exact Or.inl hxsdiff.1
  · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hxstar
    obtain ⟨δ₀, hδ₀, rfl⟩ := hxstar
    rw [stableRemnantTau_map o ⟨δ₀, hδ₀⟩]
    exact Or.inr ⟨δ₀, hδ₀, rfl⟩

/-- **body-636 (Step 4) — remnants of distinct-owner occurrences are vertex-disjoint.**  `γ`-vertices are
disjoint (`s.1.outer.pairwiseDisjoint`); `γ`-vertices vs promoted stars are separated by freshness; two promoted
stars coincide only if their promoted components coincide, forcing a shared component vertex into `γ₁ ∩ γ₂ = ∅`
(components are nonempty). -/
theorem stableRemnant_pairwiseDisjoint
    (o₁ o₂ : StableForestChoiceOccurrence s) (hne : o₁.γ.1 ≠ o₂.γ.1) :
    _root_.Disjoint (stableRemnantComponent o₁).vertices (stableRemnantComponent o₂).vertices := by
  have hpfSel := stableSelectedOuter_isProperForest s.1
  have hdd : o₁.γ.1.Disjoint o₂.γ.1 := s.1.outer.pairwiseDisjoint o₁.γ.2 o₂.γ.2 hne
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rcases stableRemnant_origin o₁ hw1 with hγ1 | ⟨δ1, hδ1, hs1⟩
  · rcases stableRemnant_origin o₂ hw2 with hγ2 | ⟨δ2, hδ2, hs2⟩
    · exact Finset.disjoint_left.mp hdd hγ1 hγ2
    · exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1) hpfSel
        (stableRemnant_promoted_mem o₂ hδ2) (hs2 ▸ o₁.γ.1.vertices_subset hγ1)
  · rcases stableRemnant_origin o₂ hw2 with hγ2 | ⟨δ2, hδ2, hs2⟩
    · exact stableRemnant_gen_star_not_mem (stableSelectedOuter s.1) hpfSel
        (stableRemnant_promoted_mem o₁ hδ1) (hs1 ▸ o₂.γ.1.vertices_subset hγ2)
    · have hstar : phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
          (stableRootRelativeInner o₁.γ.1 δ1)
          = phi4WTriplePrimeCanonicalSupply.starOf G (stableSelectedOuter s.1)
              (stableRootRelativeInner o₂.γ.1 δ2) := hs1 ▸ hs2
      have hc12 := stableRemnant_gen_star_injOn (stableSelectedOuter s.1) hpfSel
        (stableRemnant_promoted_mem o₁ hδ1) (stableRemnant_promoted_mem o₂ hδ2) hstar
      obtain ⟨u, hu⟩ := Finset.card_pos.mp
        ((stableForestOcc_B_isProperForest o₁).2.1 δ1 hδ1)
      have huR1 : u ∈ (stableRootRelativeInner o₁.γ.1 δ1).vertices := by
        rw [stableRootRelativeInner_vertices]; exact hu
      have hu1 : u ∈ o₁.γ.1.vertices :=
        stableRootRelativeInner_vertices_subset o₁.γ.1 δ1 huR1
      have huR2 : u ∈ (stableRootRelativeInner o₂.γ.1 δ2).vertices := hc12 ▸ huR1
      have hu2 : u ∈ o₂.γ.1.vertices :=
        stableRootRelativeInner_vertices_subset o₂.γ.1 δ2 huR2
      exact Finset.disjoint_left.mp hdd hu1 hu2

/-- **body-636 (Step 4) — the occurrence→remnant map is injective on distinct owners.**  Distinct owners give
vertex-disjoint (hence distinct nonempty) remnants. -/
theorem stableRemnant_injOn
    (o₁ o₂ : StableForestChoiceOccurrence s) (hne : o₁.γ.1 ≠ o₂.γ.1) :
    stableRemnantComponent o₁ ≠ stableRemnantComponent o₂ := by
  intro heq
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (stableRemnant_isNonempty o₁)
  have hw2 : w ∈ (stableRemnantComponent o₂).vertices := by
    rw [← congrArg ResolvedFeynmanSubgraph.vertices heq]; exact hw
  exact Finset.disjoint_left.mp (stableRemnant_pairwiseDisjoint o₁ o₂ hne) hw hw2

/-! ## Step 5 — remnantForest assembly -/

/-- A component of `s.1.outer` is FOREST-chosen (its stable split choice lands in the `Sum.inr` forest carrier). -/
def stableIsForestComponent (s : StablePhi4MixedSplitChoice G hSt) (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.1.outer,
    ∃ B : StableLocalForestIdx γ,
      s.1.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inr B

/-- **body-636 (Step 5) — the forest-component set.** -/
noncomputable def stableForestComponents
    (s : StablePhi4MixedSplitChoice G hSt) : Finset (ResolvedFeynmanSubgraph G) :=
  s.1.outer.elements.filter (stableIsForestComponent s)

theorem stableMem_forestComponents
    (s : StablePhi4MixedSplitChoice G hSt) {γ : ResolvedFeynmanSubgraph G} :
    γ ∈ stableForestComponents s ↔
      γ ∈ s.1.outer.elements ∧ stableIsForestComponent s γ := by
  simp only [stableForestComponents, Finset.mem_filter]

/-- **body-636 (Step 5) — the forest-choice occurrence of a forest component.**  `Classical.choose` the
witnessing membership and inner forest `B` off the `stableIsForestComponent` existential. -/
noncomputable def stableForestComponentOccurrence
    {s : StablePhi4MixedSplitChoice G hSt}
    (γF : {x // x ∈ stableForestComponents s}) :
    StableForestChoiceOccurrence s :=
  let hForest := ((stableMem_forestComponents s).mp γF.2).2
  { γ := ⟨γF.1, hForest.choose⟩
    B := hForest.choose_spec.choose
    hchoice := hForest.choose_spec.choose_spec }

@[simp] theorem stableForestComponentOccurrence_owner
    {s : StablePhi4MixedSplitChoice G hSt}
    (γF : {x // x ∈ stableForestComponents s}) :
    (stableForestComponentOccurrence γF).γ.1 = γF.1 := rfl

/-- **body-636 (Step 5) — the decompleted-remnant forest** in the quotient ambient `Q`.  One remnant per
forest-choice occurrence, admissible via Step 1 (CD) + Step 4 (pairwise disjointness).  We do NOT claim
`elements.Nonempty` (a mixed left/right choice may yield an empty remnant). -/
noncomputable def stableRemnantForest (s : StablePhi4MixedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily (stableSelectedOuterContractGraph s.1) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((stableForestComponents s).attach.image
      (fun γF => stableRemnantComponent (stableForestComponentOccurrence γF)))
    (by
      intro δ hδ
      obtain ⟨γF, -, rfl⟩ := Finset.mem_image.mp hδ
      exact stableRemnant_isConnectedDivergent _)
    (by
      intro δ hδ δ' hδ' hne
      obtain ⟨γF₁, -, rfl⟩ := Finset.mem_image.mp hδ
      obtain ⟨γF₂, -, rfl⟩ := Finset.mem_image.mp hδ'
      have hγRne : γF₁ ≠ γF₂ := fun h => hne (by rw [h])
      show _root_.Disjoint
        (stableRemnantComponent (stableForestComponentOccurrence γF₁)).vertices
        (stableRemnantComponent (stableForestComponentOccurrence γF₂)).vertices
      exact stableRemnant_pairwiseDisjoint _ _ (fun h => hγRne (Subtype.ext h)))

@[simp] theorem stableRemnantForest_elements (s : StablePhi4MixedSplitChoice G hSt) :
    (stableRemnantForest s).elements
      = (stableForestComponents s).attach.image
          (fun γF => stableRemnantComponent (stableForestComponentOccurrence γF)) := rfl

/-- **body-636 (Step 5) — origin recovery.**  Every remnant-forest element is `stableRemnantComponent o` for a
concrete forest-choice occurrence `o`. -/
theorem stableRemnantForest_element_origin
    {s : StablePhi4MixedSplitChoice G hSt}
    {δ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)}
    (hδ : δ ∈ (stableRemnantForest s).elements) :
    ∃ o : StableForestChoiceOccurrence s, δ = stableRemnantComponent o := by
  rw [stableRemnantForest_elements] at hδ
  obtain ⟨γF, -, rfl⟩ := Finset.mem_image.mp hδ
  exact ⟨stableForestComponentOccurrence γF, rfl⟩

/-- **body-636 (Step 5) — the remnant forest is componentwise connected-divergent** (Step-1 CD, per element). -/
theorem stableRemnantForest_component_cd
    {s : StablePhi4MixedSplitChoice G hSt}
    {δ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)}
    (hδ : δ ∈ (stableRemnantForest s).elements) :
    δ.forget.IsConnectedDivergent := by
  obtain ⟨o, rfl⟩ := stableRemnantForest_element_origin hδ
  exact stableRemnant_isConnectedDivergent o

/-- **body-636 (Step 5) — the remnant forest is externally-leg saturated** (sixth axis, componentwise). -/
theorem stableRemnantForest_externalLegSaturated (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedForestExternalLegSaturated (stableRemnantForest s) := by
  intro δ hδ
  obtain ⟨o, rfl⟩ := stableRemnantForest_element_origin hδ
  exact stableRemnant_externalLegSaturated o

/-- **body-636 (Step 5) — the remnant forest is internal-edge complete** (seventh axis, componentwise). -/
theorem stableRemnantForest_internalEdgeComplete (s : StablePhi4MixedSplitChoice G hSt) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (stableRemnantForest s) := by
  intro γ hγ
  obtain ⟨o, rfl⟩ := stableRemnantForest_element_origin hγ
  exact stableRemnant_internalEdgeComplete o

/-- **body-636 (Step 5) — the remnant forest carries its right-factor generators.**  Every forest element is
`stableRemnantComponent o` for an occurrence `o`, and the `Sum.inr o.B` forest branch of body-633's stable local
right factor is `X` of that element's boundary-completed stable generator (Step-3
`stableLocalRightFactor_forest_eq_remnantGen`). -/
theorem stableRemnantForest_rightTerm
    {s : StablePhi4MixedSplitChoice G hSt}
    {δ : ResolvedFeynmanSubgraph (stableSelectedOuterContractGraph s.1)}
    (hδ : δ ∈ (stableRemnantForest s).elements) :
    ∃ o : StableForestChoiceOccurrence s, δ = stableRemnantComponent o ∧
      ∀ (hCDγ : o.γ.1.forget.IsConnectedDivergent)
        (hCD : ∃ hWF : (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget.WellFormed,
          @FeynmanSubgraph.IsConnectedDivergent
            (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget
            (phi4DivergenceMeasureFamily
              (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget)
            (FeynmanSubgraph.self
              (stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).forget hWF))
        (hSt' : StableResolvedBoundaryIds
          (stableLocalBoundaryCompletedGraph (stableRemnantComponent o))),
        stableLocalRightFactor hSt o.γ.1 hCDγ (Sum.inr o.B)
          = MvPolynomial.X
              ((stableLocalBoundaryCompletedGraph (stableRemnantComponent o)).toStableResolvedPhi4HopfGen
                hCD hSt') := by
  obtain ⟨o, rfl⟩ := stableRemnantForest_element_origin hδ
  exact ⟨o, rfl, fun hCDγ hCD hSt' => stableLocalRightFactor_forest_eq_remnantGen o hCDγ hCD hSt'⟩

end GaugeGeometry.QFT.Combinatorial
