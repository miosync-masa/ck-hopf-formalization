import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockDecontraction

/-!
# QFT-R1-body-610 — recovered parent forget topology discharge

Body-609 proved the recovered parent's φ⁴ divergence outright, leaving its `forget` support-connectivity and
one-particle-irreducibility as the named PROOF FRONTIER `phi4WTriplePrime_inv_recoveredParent_ForgetTopology`.
This body DISCHARGES that frontier — pure graph topology, no physics, no divergence re-proof — by re-keying the
(polluted) body-549–552 parent-reachability blueprint to body-609's INDUCED-subgraph parent.

The induced presentation is CLEANER than the flat blueprint: the two decomposition lemmas
`phi4WTriplePrime_inv_delta_internalEdges_eq` (`δ.internalEdges = ExactEdges.map retargetEdge`) and
`phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp` (`P.internalEdges = touchedForest + ExactEdges`)
replace the flat `quotientEdgePreimage_map` / `recontract548_parent_internalEdges`; the KEY MEMBERSHIP IFF
`phi4WTriplePrime_inv_retarget_mem_delta_iff` replaces the polluted `localizedParentVertex_retargets`.  Everything
else is the flat support-reachability-lift / erase-reroute proof shape re-derived clean at the induced owner —
NEW TOPOLOGY = ZERO.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; no `ResolvedCanonicalStarFacts` / `ForestBlockCodType` / `localizedParentWithTouchedLegs`
consumed; no `resolvedComponentGen`; no `s` / `componentEquiv`; no `innerForest` / `recontraction` /
`complement`-positivity / owner / global decl touched; no strict cross-presentation star equality; no divergence
re-proof (the `_isDivergent` is READ from body-609); no `sorry` / `admit` / `native_decide`; no `forget` global
injectivity assumption (erase survival is count/support bookkeeping).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst610 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Support-reachability monotonicity (re-derived clean). -/

/-- Support-reachability transports up an internal-edge inclusion. -/
private theorem phi4WTriplePrime_inv_supportReachable_mono {H K : FeynmanGraph}
    (hle : H.internalEdges ≤ K.internalEdges) {u v : VertexId}
    (h : H.SupportReachable u v) : K.SupportReachable u v := by
  refine SimpleGraph.Reachable.mono ?_ h
  intro a b hab
  obtain ⟨hne, e, heH, hend⟩ := hab
  exact ⟨hne, e, Multiset.mem_of_le hle heH, hend⟩

/-! ## The Exact edges + the two induced-parent internal-edge decompositions. -/

/-- **body-610 — the recovered parent's EXACT edges.**  The `A`-complement edges whose both endpoints already
sit in the recovered-parent region.  (The de-contraction boundary/reconnecting edges + the `δ`-root preimages,
uniformly — via the KEY MEMBERSHIP IFF these are exactly the complement edges landing inside `δ`.) -/
noncomputable def phi4WTriplePrime_inv_parentExactEdges
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    Multiset ResolvedFeynmanEdge :=
  z.1.1.complementEdges.filter
    (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)

/-- **body-610 — `A`-internal edges cut by the region ARE the touched forest's edges.**  An `A`-internal edge
survives the region filter iff its owner component is touched (its star lands in `δ`); the sum over touched
components is the touched-outer-forest's internal edges. -/
theorem phi4WTriplePrime_inv_touchedInternalEdges_filter
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    z.1.1.internalEdges.filter
      (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges := by
  classical
  have hfilter_sum : ∀ (s : Finset (ResolvedFeynmanSubgraph G)),
      (s.sum (fun γ => γ.internalEdges)).filter
          (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
            ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
        = s.sum (fun γ => (γ.internalEdges).filter
          (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
            ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a t ha ih => rw [Finset.sum_insert ha, Multiset.filter_add, ih, Finset.sum_insert ha]
  rw [ResolvedAdmissibleSubgraph.internalEdges, hfilter_sum, ResolvedAdmissibleSubgraph.internalEdges,
    phi4WTriplePrime_touchedOuterForest_elements, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro γ hγ
  by_cases htouched : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices
  · rw [if_pos htouched]
    apply Multiset.filter_eq_self.mpr
    intro e he
    have hγT : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
      rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]; exact ⟨hγ, htouched⟩
    obtain ⟨hs, ht⟩ := γ.edges_supported e he
    have hsub := phi4WTriplePrime_inv_touchedComponent_verts_subset (z := z) (δ := δ) hγT
    exact ⟨hsub hs, hsub ht⟩
  · rw [if_neg htouched]
    apply Multiset.filter_eq_nil.mpr
    intro e he hp
    obtain ⟨hs, _ht⟩ := γ.edges_supported e he
    have hsG : e.source ∈ G.vertices := γ.vertices_subset hs
    have hmem := (phi4WTriplePrime_inv_retarget_mem_delta_iff _I hsG).mpr hp.1
    rw [phi4WTriplePrime_retargetVertex_eq_star z.1.1
      (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) hγ hs] at hmem
    exact htouched hmem

/-- **body-610 — the recovered parent's internal edges split as touched-forest + Exact edges.** -/
theorem phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).internalEdges
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges
        + phi4WTriplePrime_inv_parentExactEdges z δ := by
  have hGdecomp : G.internalEdges = z.1.1.internalEdges + z.1.1.complementEdges := by
    rw [ResolvedAdmissibleSubgraph.complementEdges, add_tsub_cancel_of_le (fgIntEdgesLe z.1.1)]
  rw [phi4WTriplePrime_inv_recoveredParent_internalEdges, hGdecomp, Multiset.filter_add]
  congr 1
  exact phi4WTriplePrime_inv_touchedInternalEdges_filter I

/-- **body-610 — the `δ`-component's internal edges are the Exact edges retargeted.**  `δ` is internal-edge
complete on the quotient (its live W‴ membership), so its edges are exactly the quotient edges with both
endpoints inside `δ`, i.e. the Exact complement edges retargeted (KEY MEMBERSHIP IFF on both endpoints).  This
is the clean induced-parent analogue of the flat `quotientEdgePreimage_map`. -/
theorem phi4WTriplePrime_inv_delta_internalEdges_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    δ.1.internalEdges
      = (phi4WTriplePrime_inv_parentExactEdges z δ).map
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  classical
  have hδEC : ResolvedInternalEdgeComplete δ.1 :=
    (((mem_phi4WTriplePrimeIndex
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
        z.2.2).2.2.2.2.2.2) δ.1 δ.2
  have hcompLe : z.1.1.complementEdges ≤ G.internalEdges := by
    rw [ResolvedAdmissibleSubgraph.complementEdges]; exact Multiset.sub_le_self _ _
  -- Step (i): `δ.internalEdges` is the quotient edges induced on `δ.vertices`.
  have hstep1 : δ.1.internalEdges
      = (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges.filter
          (fun e => e.source ∈ δ.1.vertices ∧ e.target ∈ δ.1.vertices) := by
    apply le_antisymm
    · rw [Multiset.le_filter]
      exact ⟨δ.1.internalEdges_le, fun e he => δ.1.edges_supported e he⟩
    · exact hδEC
  have key : δ.1.internalEdges
      = (z.1.1.complementEdges.filter
          (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
            ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)).map
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
    rw [hstep1, ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
      ← Multiset.map_filter_of_iff (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
          z.1.1.complementEdges
          (fun e => (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source
              ∈ δ.1.vertices
            ∧ (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).target ∈ δ.1.vertices)
          (fun e => e.source ∈ δ.1.vertices ∧ e.target ∈ δ.1.vertices)
          (fun _ => Iff.rfl)]
    congr 1
    apply Multiset.filter_congr
    intro e he
    have hsG : e.source ∈ G.vertices := (I.rootAmbientSupported.1 e (Multiset.mem_of_le hcompLe he)).1
    have htG : e.target ∈ G.vertices := (I.rootAmbientSupported.1 e (Multiset.mem_of_le hcompLe he)).2
    have hs := phi4WTriplePrime_inv_retarget_mem_delta_iff I hsG
    have ht := phi4WTriplePrime_inv_retarget_mem_delta_iff I htG
    show ((z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source ∈ δ.1.vertices
        ∧ (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).target ∈ δ.1.vertices)
      ↔ (e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ∧ e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
      ResolvedFeynmanEdge.retarget_target]
    rw [hs, ht]
  exact key

/-- The recovered parent's `forget` internal edges are the resolved internal edges forgotten. -/
theorem phi4WTriplePrime_inv_recoveredParent_forget_internalEdges
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges
      = (phi4WTriplePrime_inv_recoveredParent I).internalEdges.map ResolvedFeynmanEdge.forget := by
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]

/-- The recovered parent's `forget` internal edges split as (touched forest ‖ Exact), forgotten. -/
theorem phi4WTriplePrime_inv_recoveredParent_forget_internalEdges_decomp
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        + (phi4WTriplePrime_inv_parentExactEdges z δ).map ResolvedFeynmanEdge.forget := by
  rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges I,
    phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I, Multiset.map_add]

/-! ## Step 1 — parent edge decomposition + connected trunk. -/

/-- **body-610 (Step 1) — parent internal-edge cases.**  Every recovered-parent internal edge is either a
touched-forest edge (Promoted) or an Exact edge — exhaustive by the internal-edge decomposition, NO third
unowned class. -/
theorem phi4WTriplePrime_inv_parentEdge_cases
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges) :
    e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges
      ∨ e ∈ phi4WTriplePrime_inv_parentExactEdges z δ := by
  rw [phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I] at he
  exact Multiset.mem_add.mp he

/-- **body-610 — parent-vertex retarget classification.**  Each vertex is either fixed by the retarget (off
`A`) or sits in a touched-outer-forest owner component and retargets to that component's canonical star. -/
theorem phi4WTriplePrime_inv_parent_retarget_cases
    (z : Phi4WTriplePrimeInverseCodomain G) {v : VertexId} :
    (z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v = v ∧ v ∉ z.1.1.vertices)
      ∨ (∃ γ ∈ z.1.1.elements, v ∈ γ.vertices
        ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v
            = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ) := by
  by_cases hvA : v ∈ z.1.1.vertices
  · obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
    exact Or.inr ⟨γ, hγ, hvγ, phi4WTriplePrime_retargetVertex_eq_star z.1.1
      (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) hγ hvγ⟩
  · exact Or.inl ⟨z.1.1.retargetVertex_of_not_mem _ hvA, hvA⟩

/-- **body-610 — within-touched-component reachability, generalized to `K`.**  Two vertices of a touched
component `γ` are `K.SupportReachable` whenever `γ`'s forgotten edges sit inside `K` (`γ.forget` is
support-connected via its own `isConnectedDivergent`). -/
theorem phi4WTriplePrime_inv_touchedComponent_reachable_in
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ) {K : FeynmanGraph}
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements)
    (hγle : γ.internalEdges.map ResolvedFeynmanEdge.forget ≤ K.internalEdges)
    {u v : VertexId} (hu : u ∈ γ.vertices) (hv : v ∈ γ.vertices) :
    K.SupportReachable u v := by
  have hconn : γ.forget.toFeynmanGraph.IsSupportConnected :=
    ((phi4WTriplePrime_touchedOuterForest z δ).isConnectedDivergent γ hγ).1
  have hreach : γ.forget.toFeynmanGraph.SupportReachable u v := hconn hu hv
  have hle : γ.forget.toFeynmanGraph.internalEdges ≤ K.internalEdges := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    exact hγle
  exact phi4WTriplePrime_inv_supportReachable_mono hle hreach

/-- **body-610 (★load-bearing★) — same-retarget gluing, generalized to `K`.**  Two parent vertices with equal
retarget image are `K.SupportReachable` (given the whole touched-forest half sits in `K`) — four cases: both
non-star ⇒ `x = y`; mixed ⇒ star-freshness contradiction; star/star ⇒ `star_injOn` identifies the SAME owner
component, connected via the touched-component reachability. -/
theorem phi4WTriplePrime_inv_sameRetarget_reachable_in
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {K : FeynmanGraph}
    (hPromLe : (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        ≤ K.internalEdges)
    {x y : VertexId} (hx : x ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hy : y ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hret : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) x
          = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) y) :
    K.SupportReachable x y := by
  classical
  have hApf : z.1.1.IsProperForest := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1
  rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := x) with ⟨hx0, _⟩ | ⟨Ax, hAx, hxAx, hxret⟩
  · rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := y) with ⟨hy0, _⟩ | ⟨Ay, hAy, hyAy, hyret⟩
    · rw [show x = y from hx0.symm.trans (hret.trans hy0)]
      exact FeynmanGraph.SupportReachable.refl _ _
    · exfalso
      have hxstar : x = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ay :=
        hx0.symm.trans (hret.trans hyret)
      exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf hAy
        (hxstar ▸ phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hx)
  · rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := y) with ⟨hy0, _⟩ | ⟨Ay, hAy, hyAy, hyret⟩
    · exfalso
      have hystar : y = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax :=
        hy0.symm.trans (hret.symm.trans hxret)
      exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf hAx
        (hystar ▸ phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hy)
    · have hstar : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax
          = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ay := hxret.symm.trans (hret.trans hyret)
      have hAeq : Ax = Ay := phi4WTriplePrime_gen_star_injOn z.1.1 hApf hAx hAy hstar
      subst hAeq
      have hxG : x ∈ G.vertices := phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hx
      have hstarδ : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax ∈ δ.1.vertices := by
        have hmem := (phi4WTriplePrime_inv_retarget_mem_delta_iff I hxG).mpr hx
        rwa [hxret] at hmem
      have hAxT : Ax ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]; exact ⟨hAx, hstarδ⟩
      have hγle : Ax.internalEdges.map ResolvedFeynmanEdge.forget ≤ K.internalEdges :=
        le_trans (Multiset.map_le_map (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hAxT)) hPromLe
      exact phi4WTriplePrime_inv_touchedComponent_reachable_in I hAxT hγle hxAx hyAy

/-- **body-610 — edge-step lift (un-erased skeleton).**  A `δ`-adjacency `c—b` + a source-preimage `wc` of `c`
yields a source-preimage `wb` of `b` reachable from `wc` in `P.forget`: the `δ`-edge has an Exact preimage in
`P`, glued via the same-retarget lemma. -/
theorem phi4WTriplePrime_inv_parent_edgeStep
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {c b : VertexId}
    (hadj : δ.1.forget.toFeynmanGraph.SupportAdj c b)
    {wc : VertexId} (hwc : wc ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hwcc : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wb = b
      ∧ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.SupportReachable wc wb := by
  classical
  obtain ⟨hcb, eδ, heδ, hend⟩ := hadj
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges,
    ResolvedFeynmanSubgraph.forget_internalEdges] at heδ
  rw [phi4WTriplePrime_inv_delta_internalEdges_eq I, Multiset.map_map] at heδ
  obtain ⟨eE, heE, rfl⟩ := Multiset.mem_map.mp heδ
  simp only [Function.comp_apply, ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target,
    ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
    ResolvedFeynmanEdge.retarget_target] at hend
  have heEP : eE ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I]
    exact Multiset.mem_add.mpr (Or.inr heE)
  obtain ⟨hsE, htE⟩ := (phi4WTriplePrime_inv_recoveredParent I).edges_supported eE heEP
  have heEforget : eE.forget ∈ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges I]
    exact Multiset.mem_map_of_mem _ heEP
  have hPromLe : (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
      ≤ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges_decomp I]
    exact Multiset.le_add_right _ _
  have plusAdj : eE.source ≠ eE.target →
      (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.SupportReachable eE.source eE.target :=
    fun hne => SimpleGraph.Adj.reachable
      (show (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.SupportAdj eE.source eE.target
        from ⟨hne, eE.forget, heEforget, Or.inl ⟨rfl, rfl⟩⟩)
  rcases hend with ⟨hsc, htb⟩ | ⟨hsb, htc⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (hsc.symm.trans ((congrArg _ h).trans htb))
    exact ⟨eE.target, htE, htb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_in I hPromLe hwc hsE (hwcc.trans hsc.symm)).trans
        (plusAdj hne)⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (htc.symm.trans ((congrArg _ h.symm).trans hsb))
    exact ⟨eE.source, hsE, hsb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_in I hPromLe hwc htE (hwcc.trans htc.symm)).trans
        (plusAdj hne).symm⟩

/-- **body-610 — the full path lift.**  A `δ.forget` support path lifts to a `P.forget` support path, joining
same-retarget fibers; `Relation.ReflTransGen` induction, edge-step per adjacency. -/
theorem phi4WTriplePrime_inv_recoveredParent_reachable_lift
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {a b u : VertexId}
    (hu : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hua : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u = a)
    (hab : δ.1.forget.toFeynmanGraph.SupportReachable a b) :
    ∃ w, w ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) w = b
      ∧ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.SupportReachable u w := by
  have hrtg : Relation.ReflTransGen δ.1.forget.toFeynmanGraph.SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ := phi4WTriplePrime_inv_parent_edgeStep I hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-- **body-610 (HEADLINE 1) — the recovered parent's `forget` is support-connected.** -/
theorem phi4WTriplePrime_inv_recoveredParent_isConnected
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.IsConnected := by
  classical
  have hδconn : δ.1.forget.toFeynmanGraph.IsSupportConnected :=
    (z.2.1.isConnectedDivergent δ.1 δ.2).1
  intro u v hu hv
  have hu' : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hu
  have hv' : v ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hv
  have hretu : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hu')).mpr hu'
  have hretv : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hv')).mpr hv'
  have hab : δ.1.forget.toFeynmanGraph.SupportReachable
      (z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u)
      (z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v) := hδconn hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ := phi4WTriplePrime_inv_recoveredParent_reachable_lift I hu' rfl hab
  have hPromLe : (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
      ≤ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges_decomp I]
    exact Multiset.le_add_right _ _
  exact huw.trans (phi4WTriplePrime_inv_sameRetarget_reachable_in I hPromLe hw hv' hwv)

/-! ## Step 2 — Exact edges are not bridges. -/

/-- **body-610 (Step 2) — erasing an Exact edge leaves the touched forest whole + the Exact half short one.**
`e.forget` lives in the Exact (right) summand, so `erase_add_right_pos` keeps the Promoted (left) half intact. -/
theorem phi4WTriplePrime_inv_erase_exact_decomp
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) :
    ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges).erase e.forget
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        + ((phi4WTriplePrime_inv_parentExactEdges z δ).map ResolvedFeynmanEdge.forget).erase e.forget := by
  rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges_decomp I,
    Multiset.erase_add_right_pos _ (Multiset.mem_map_of_mem _ he)]

/-- **body-610 (Step 2) — the touched-forest half survives an Exact-edge erase.** -/
theorem phi4WTriplePrime_inv_promoted_le_erase_exact
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) :
    (phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
      ≤ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).internalEdges := by
  rw [FeynmanGraph.eraseInternalEdge_internalEdges, phi4WTriplePrime_inv_erase_exact_decomp I he]
  exact Multiset.le_add_right _ _

/-- **body-610 (Step 2) — edge-step avoiding the erased Exact edge.**  A `δ∖(retarget e)`-adjacency `c—b` +
a source-preimage of `c` yields a source-preimage of `b` reachable in `P∖e.forget`: the surviving Exact
preimage (`map_erase_of_mem`, both forget/retarget layers) lives in `P∖e.forget`; the touched-forest half is
untouched so the same-retarget lemma glues. -/
theorem phi4WTriplePrime_inv_edgeStep_erase_exact
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) {c b : VertexId}
    (hadj : (δ.1.forget.toFeynmanGraph.eraseInternalEdge
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).forget).SupportAdj c b)
    {wc : VertexId} (hwc : wc ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hwcc : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wb = b
      ∧ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportReachable wc wb := by
  classical
  obtain ⟨hcb, eδ, heδ, hend⟩ := hadj
  rw [FeynmanGraph.eraseInternalEdge_internalEdges] at heδ
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges,
    ResolvedFeynmanSubgraph.forget_internalEdges] at heδ
  have hre : z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e ∈ δ.1.internalEdges := by
    rw [phi4WTriplePrime_inv_delta_internalEdges_eq I]; exact Multiset.mem_map_of_mem _ he
  rw [← Multiset.map_erase_of_mem ResolvedFeynmanEdge.forget _ hre,
    phi4WTriplePrime_inv_delta_internalEdges_eq I,
    ← Multiset.map_erase_of_mem (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) _ he,
    Multiset.map_map] at heδ
  obtain ⟨eE, heEerase, rfl⟩ := Multiset.mem_map.mp heδ
  have heE : eE ∈ phi4WTriplePrime_inv_parentExactEdges z δ := Multiset.mem_of_mem_erase heEerase
  simp only [Function.comp_apply, ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target,
    ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
    ResolvedFeynmanEdge.retarget_target] at hend
  have heEP : eE ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I]
    exact Multiset.mem_add.mpr (Or.inr heE)
  obtain ⟨hsE, htE⟩ := (phi4WTriplePrime_inv_recoveredParent I).edges_supported eE heEP
  have heEsurvive : eE.forget ∈
      ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).internalEdges := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, phi4WTriplePrime_inv_erase_exact_decomp I he]
    refine Multiset.mem_add.mpr (Or.inr ?_)
    rw [← Multiset.map_erase_of_mem ResolvedFeynmanEdge.forget _ he]
    exact Multiset.mem_map_of_mem _ heEerase
  have hPromLe := phi4WTriplePrime_inv_promoted_le_erase_exact I he
  have plusAdj : eE.source ≠ eE.target →
      ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable eE.source eE.target :=
    fun hne => SimpleGraph.Adj.reachable
      (show ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportAdj eE.source eE.target from ⟨hne, eE.forget, heEsurvive, Or.inl ⟨rfl, rfl⟩⟩)
  rcases hend with ⟨hsc, htb⟩ | ⟨hsb, htc⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (hsc.symm.trans ((congrArg _ h).trans htb))
    exact ⟨eE.target, htE, htb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_in I hPromLe hwc hsE (hwcc.trans hsc.symm)).trans
        (plusAdj hne)⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (htc.symm.trans ((congrArg _ h.symm).trans hsb))
    exact ⟨eE.source, hsE, hsb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_in I hPromLe hwc htE (hwcc.trans htc.symm)).trans
        (plusAdj hne).symm⟩

/-- **body-610 (Step 2) — path lift avoiding the erased Exact edge.** -/
theorem phi4WTriplePrime_inv_reachable_lift_erase_exact
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) {a b u : VertexId}
    (hu : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hua : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u = a)
    (hab : (δ.1.forget.toFeynmanGraph.eraseInternalEdge
        (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).forget).SupportReachable a b) :
    ∃ w, w ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) w = b
      ∧ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportReachable u w := by
  have hrtg : Relation.ReflTransGen (δ.1.forget.toFeynmanGraph.eraseInternalEdge
      (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).forget).SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ := phi4WTriplePrime_inv_edgeStep_erase_exact I he hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-- **body-610 (Step 2) — erasing an Exact edge keeps `P.forget` support-connected.**  Its retarget is a
`δ`-edge; `δ` is 1PI so `δ∖(retarget e)` is connected; the touched-forest half survives; the path lifts and
the endpoints glue. -/
theorem phi4WTriplePrime_inv_exactEdge_isSupportConnected
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) :
    ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).IsSupportConnected := by
  classical
  have hδCD : δ.1.forget.IsConnectedDivergent := z.2.1.isConnectedDivergent δ.1 δ.2
  have hre : z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e ∈ δ.1.internalEdges := by
    rw [phi4WTriplePrime_inv_delta_internalEdges_eq I]; exact Multiset.mem_map_of_mem _ he
  have hreF : (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).forget
      ∈ δ.1.forget.toFeynmanGraph.internalEdges := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    exact Multiset.mem_map_of_mem _ hre
  have hδErase : (δ.1.forget.toFeynmanGraph.eraseInternalEdge
      (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).forget).IsSupportConnected := by
    by_contra hnot
    exact hδCD.2.1.no_bridge _ hreF ⟨hreF, hnot⟩
  intro u v hu hv
  rw [FeynmanGraph.eraseInternalEdge_vertices] at hu hv
  have hu' : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hu
  have hv' : v ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hv
  have hretu : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hu')).mpr hu'
  have hretv : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hv')).mpr hv'
  have hab := hδErase hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ := phi4WTriplePrime_inv_reachable_lift_erase_exact I he hu' rfl hab
  exact huw.trans
    (phi4WTriplePrime_inv_sameRetarget_reachable_in I
      (phi4WTriplePrime_inv_promoted_le_erase_exact I he) hw hv' hwv)

/-- **body-610 (Step 2, VICTORY) — an Exact edge of the recovered parent is NOT a bridge.** -/
theorem phi4WTriplePrime_inv_exactEdge_no_bridge
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (hExact : e ∈ phi4WTriplePrime_inv_parentExactEdges z δ) :
    ¬ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.IsBridge e.forget :=
  fun hbridge => hbridge.2 (phi4WTriplePrime_inv_exactEdge_isSupportConnected I hExact)

/-! ## Step 3 — Promoted edges are not bridges. -/

/-- **body-610 (Step 3) — erasing a Promoted edge leaves the touched forest short one + the Exact half whole.**
`e.forget` lives in the Promoted (left) summand, so `erase_add_left_pos` keeps the Exact (right) half intact. -/
theorem phi4WTriplePrime_inv_erase_promoted_decomp
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) :
    ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges).erase e.forget
      = ((phi4WTriplePrime_touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget).erase e.forget
        + (phi4WTriplePrime_inv_parentExactEdges z δ).map ResolvedFeynmanEdge.forget := by
  rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges_decomp I,
    Multiset.erase_add_left_pos _ (Multiset.mem_map_of_mem _ he)]

/-- **body-610 (Step 3) — the Exact half survives a Promoted-edge erase.** -/
theorem phi4WTriplePrime_inv_exact_le_erase_promoted
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) :
    (phi4WTriplePrime_inv_parentExactEdges z δ).map ResolvedFeynmanEdge.forget
      ≤ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).internalEdges := by
  rw [FeynmanGraph.eraseInternalEdge_internalEdges, phi4WTriplePrime_inv_erase_promoted_decomp I he]
  exact Multiset.le_add_left _ _

/-- **body-610 (Step 3) — cross-owner flat-edge separation.**  For distinct touched components `A' ≠ E'` and
`e ∈ E'.internalEdges`, `e.forget ∉ A'.internalEdges.map forget`: a shared forgotten edge would place `e.source`
in both owners, contradicting the touched forest's pairwise vertex-disjointness.  `forget` is NOT assumed
injective — owner + disjointness *before* forgetting refutes the flat collision. -/
theorem phi4WTriplePrime_inv_forget_notMem_of_ne_owner
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {A' E' : ResolvedFeynmanSubgraph G}
    (hA' : A' ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements)
    (hE' : E' ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements)
    (hne : A' ≠ E') {e : ResolvedFeynmanEdge} (heE : e ∈ E'.internalEdges) :
    e.forget ∉ A'.internalEdges.map ResolvedFeynmanEdge.forget := by
  intro hmem
  obtain ⟨eA, heA, hforget⟩ := Multiset.mem_map.mp hmem
  have hsrc : eA.source = e.source := by
    have h := congrArg FeynmanEdge.source hforget
    simpa only [ResolvedFeynmanEdge.forget_source] using h
  obtain ⟨hsA, _⟩ := A'.edges_supported eA heA
  obtain ⟨hsE, _⟩ := E'.edges_supported e heE
  have hvA : e.source ∈ A'.vertices := hsrc ▸ hsA
  have hdisj : A'.Disjoint E' := (phi4WTriplePrime_touchedOuterForest z δ).isPairwiseDisjoint hA' hE' hne
  exact Finset.disjoint_left.mp hdisj hvA hsE

/-- **body-610 (Step 3, ★load-bearing★) — same-retarget gluing avoiding a Promoted edge.**  Star/star ⇒ SAME
owner `Ax`; then `by_cases e ∈ Ax.internalEdges`: **Case A** — `Ax` is 1PI so `Ax∖e.forget` is connected
(`erase_le_erase` transport); **Case B** — `Ax` is intact in `Promoted∖e.forget` (the erased edge's owner
`E' ≠ Ax` gives `count e.forget = 0` in `Ax`, cross-owner separation). -/
theorem phi4WTriplePrime_inv_sameRetarget_reachable_erase_promoted
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges)
    {x y : VertexId} (hx : x ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hy : y ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hret : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) x
          = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) y) :
    ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).SupportReachable x y := by
  classical
  have hApf : z.1.1.IsProperForest := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1
  rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := x) with ⟨hx0, _⟩ | ⟨Ax, hAx, hxAx, hxret⟩
  · rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := y) with ⟨hy0, _⟩ | ⟨Ay, hAy, hyAy, hyret⟩
    · rw [show x = y from hx0.symm.trans (hret.trans hy0)]
      exact FeynmanGraph.SupportReachable.refl _ _
    · exfalso
      have hxstar : x = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ay :=
        hx0.symm.trans (hret.trans hyret)
      exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf hAy
        (hxstar ▸ phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hx)
  · rcases phi4WTriplePrime_inv_parent_retarget_cases z (v := y) with ⟨hy0, _⟩ | ⟨Ay, hAy, hyAy, hyret⟩
    · exfalso
      have hystar : y = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax :=
        hy0.symm.trans (hret.symm.trans hxret)
      exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf hAx
        (hystar ▸ phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hy)
    · have hstar : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax
          = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ay := hxret.symm.trans (hret.trans hyret)
      have hAeq : Ax = Ay := phi4WTriplePrime_gen_star_injOn z.1.1 hApf hAx hAy hstar
      subst hAeq
      have hxG : x ∈ G.vertices := phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hx
      have hstarδ : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 Ax ∈ δ.1.vertices := by
        have hmem := (phi4WTriplePrime_inv_retarget_mem_delta_iff I hxG).mpr hx
        rwa [hxret] at hmem
      have hAxT : Ax ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]; exact ⟨hAx, hstarδ⟩
      have hA1PI : Ax.forget.toFeynmanGraph.IsOnePI :=
        ((phi4WTriplePrime_touchedOuterForest z δ).isConnectedDivergent Ax hAxT).2.1
      by_cases hee : e ∈ Ax.internalEdges
      · have he_forget : e.forget ∈ Ax.forget.toFeynmanGraph.internalEdges := by
          simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
          exact Multiset.mem_map_of_mem _ hee
        have hAxErase : (Ax.forget.toFeynmanGraph.eraseInternalEdge e.forget).IsSupportConnected := by
          by_contra hnot
          exact hA1PI.no_bridge e.forget he_forget ⟨he_forget, hnot⟩
        have hreach := hAxErase hxAx hyAy
        have hsub : Ax.internalEdges ≤ (phi4WTriplePrime_inv_recoveredParent I).internalEdges :=
          phi4WTriplePrime_inv_touchedComponent_internalEdges_le I hAxT
        have hsubF : Ax.forget.toFeynmanGraph.internalEdges
            ≤ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.internalEdges := by
          rw [phi4WTriplePrime_inv_recoveredParent_forget_internalEdges I]
          simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
          exact Multiset.map_le_map hsub
        have hle : (Ax.forget.toFeynmanGraph.eraseInternalEdge e.forget).internalEdges
            ≤ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
                e.forget).internalEdges := by
          rw [FeynmanGraph.eraseInternalEdge_internalEdges, FeynmanGraph.eraseInternalEdge_internalEdges]
          exact Multiset.erase_le_erase e.forget hsubF
        exact phi4WTriplePrime_inv_supportReachable_mono hle hreach
      · have hreach : Ax.forget.toFeynmanGraph.SupportReachable x y :=
          ((phi4WTriplePrime_touchedOuterForest z δ).isConnectedDivergent Ax hAxT).1 hxAx hyAy
        have hown : ∃ Ee ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements, e ∈ Ee.internalEdges := by
          have h := he
          simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at h
          exact h
        obtain ⟨Ee, hEe, heEe⟩ := hown
        have hne : Ax ≠ Ee := fun h => hee (h ▸ heEe)
        have hnotmem : e.forget ∉ Ax.internalEdges.map ResolvedFeynmanEdge.forget :=
          phi4WTriplePrime_inv_forget_notMem_of_ne_owner I hAxT hEe hne heEe
        have hle : Ax.forget.toFeynmanGraph.internalEdges
            ≤ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
                e.forget).internalEdges := by
          rw [FeynmanGraph.eraseInternalEdge_internalEdges, phi4WTriplePrime_inv_erase_promoted_decomp I he]
          simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
          refine le_trans ?_ (Multiset.le_add_right _ _)
          rw [Multiset.le_iff_count]
          intro a
          by_cases ha : a = e.forget
          · subst ha
            rw [Multiset.count_erase_self, Multiset.count_eq_zero.mpr hnotmem]
            exact Nat.zero_le _
          · rw [Multiset.count_erase_of_ne ha]
            exact Multiset.le_iff_count.mp
              (Multiset.map_le_map (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hAxT)) a
        exact phi4WTriplePrime_inv_supportReachable_mono hle hreach

/-- **body-610 (Step 3) — edge-step on the (un-erased) `δ`-skeleton.**  A Promoted erase leaves the Exact half
untouched, so the full `δ` skeleton lifts: the Exact preimage survives (Step 3 exact-survival), glued via the
promoted-avoiding same-retarget lemma. -/
theorem phi4WTriplePrime_inv_edgeStep_erase_promoted
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) {c b : VertexId}
    (hadj : δ.1.forget.toFeynmanGraph.SupportAdj c b)
    {wc : VertexId} (hwc : wc ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hwcc : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) wb = b
      ∧ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportReachable wc wb := by
  classical
  obtain ⟨hcb, eδ, heδ, hend⟩ := hadj
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges,
    ResolvedFeynmanSubgraph.forget_internalEdges] at heδ
  rw [phi4WTriplePrime_inv_delta_internalEdges_eq I, Multiset.map_map] at heδ
  obtain ⟨eE, heE, rfl⟩ := Multiset.mem_map.mp heδ
  simp only [Function.comp_apply, ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target,
    ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
    ResolvedFeynmanEdge.retarget_target] at hend
  have heEP : eE ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I]
    exact Multiset.mem_add.mpr (Or.inr heE)
  obtain ⟨hsE, htE⟩ := (phi4WTriplePrime_inv_recoveredParent I).edges_supported eE heEP
  have heEsurvive : eE.forget ∈
      ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).internalEdges :=
    Multiset.mem_of_le (phi4WTriplePrime_inv_exact_le_erase_promoted I he)
      (Multiset.mem_map_of_mem _ heE)
  have plusAdj : eE.source ≠ eE.target →
      ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable eE.source eE.target :=
    fun hne => SimpleGraph.Adj.reachable
      (show ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportAdj eE.source eE.target from ⟨hne, eE.forget, heEsurvive, Or.inl ⟨rfl, rfl⟩⟩)
  rcases hend with ⟨hsc, htb⟩ | ⟨hsb, htc⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (hsc.symm.trans ((congrArg _ h).trans htb))
    exact ⟨eE.target, htE, htb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_erase_promoted I he hwc hsE (hwcc.trans hsc.symm)).trans
        (plusAdj hne)⟩
  · have hne : eE.source ≠ eE.target := fun h => hcb (htc.symm.trans ((congrArg _ h.symm).trans hsb))
    exact ⟨eE.source, hsE, hsb,
      (phi4WTriplePrime_inv_sameRetarget_reachable_erase_promoted I he hwc htE (hwcc.trans htc.symm)).trans
        (plusAdj hne).symm⟩

/-- **body-610 (Step 3) — path lift on the un-erased `δ`-skeleton (Promoted erase).** -/
theorem phi4WTriplePrime_inv_reachable_lift_erase_promoted
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) {a b u : VertexId}
    (hu : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
    (hua : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u = a)
    (hab : δ.1.forget.toFeynmanGraph.SupportReachable a b) :
    ∃ w, w ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
      ∧ z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) w = b
      ∧ ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportReachable u w := by
  have hrtg : Relation.ReflTransGen δ.1.forget.toFeynmanGraph.SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ := phi4WTriplePrime_inv_edgeStep_erase_promoted I he hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-- **body-610 (Step 3) — erasing a Promoted edge keeps `P.forget` support-connected.** -/
theorem phi4WTriplePrime_inv_promotedEdge_isSupportConnected
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) :
    ((phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).IsSupportConnected := by
  classical
  have hδconn : δ.1.forget.toFeynmanGraph.IsSupportConnected :=
    (z.2.1.isConnectedDivergent δ.1 δ.2).1
  intro u v hu hv
  rw [FeynmanGraph.eraseInternalEdge_vertices] at hu hv
  have hu' : u ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hu
  have hv' : v ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := hv
  have hretu : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) u ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hu')).mpr hu'
  have hretv : z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v ∈ δ.1.vertices :=
    (phi4WTriplePrime_inv_retarget_mem_delta_iff I
      (phi4WTriplePrime_inv_recoveredParent_verts_subset z δ hv')).mpr hv'
  have hab := hδconn hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ := phi4WTriplePrime_inv_reachable_lift_erase_promoted I he hu' rfl hab
  exact huw.trans (phi4WTriplePrime_inv_sameRetarget_reachable_erase_promoted I he hw hv' hwv)

/-- **body-610 (Step 3, VICTORY) — a Promoted edge of the recovered parent is NOT a bridge. -/
theorem phi4WTriplePrime_inv_promotedEdge_no_bridge
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (hPromoted : e ∈ (phi4WTriplePrime_touchedOuterForest z δ).internalEdges) :
    ¬ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.IsBridge e.forget :=
  fun hbridge => hbridge.2 (phi4WTriplePrime_inv_promotedEdge_isSupportConnected I hPromoted)

/-! ## Step 4 — bridge-free assembly ⇒ IsOnePI. -/

/-- **body-610 (Step 4) — no internal edge of the recovered parent is a bridge.**  Dispatch via the edge cases
to Step 2 (Exact) / Step 3 (Promoted). -/
theorem phi4WTriplePrime_inv_recoveredParent_no_bridge
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {e : ResolvedFeynmanEdge}
    (he : e ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges) :
    ¬ (phi4WTriplePrime_inv_recoveredParent I).forget.toFeynmanGraph.IsBridge e.forget := by
  rcases phi4WTriplePrime_inv_parentEdge_cases I he with hP | hE
  · exact phi4WTriplePrime_inv_promotedEdge_no_bridge I hP
  · exact phi4WTriplePrime_inv_exactEdge_no_bridge I hE

/-- **body-610 (HEADLINE 2) — the recovered parent's `forget` is 1PI.** -/
theorem phi4WTriplePrime_inv_recoveredParent_isOnePI
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.IsOnePI := by
  refine ⟨phi4WTriplePrime_inv_recoveredParent_isConnected I, ?_⟩
  intro e he
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges,
    ResolvedFeynmanSubgraph.forget_internalEdges] at he
  obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
  exact phi4WTriplePrime_inv_recoveredParent_no_bridge I he₀

/-! ## Step 5 — frontier discharge. -/

/-- **body-610 (VICTORY) — the body-609 `_ForgetTopology` proof frontier is DISCHARGED.**  Takes only `I`. -/
theorem phi4WTriplePrime_inv_recoveredParent_ForgetTopology_proof
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    phi4WTriplePrime_inv_recoveredParent_ForgetTopology I :=
  ⟨phi4WTriplePrime_inv_recoveredParent_isConnected I, phi4WTriplePrime_inv_recoveredParent_isOnePI I⟩

/-- **body-610 — the recovered parent is φ⁴ connected-divergent, UNCONDITIONALLY** (topology from this body +
body-609's unconditional divergence; NO divergence re-proof). -/
theorem phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent_uncond
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.IsConnectedDivergent :=
  ⟨phi4WTriplePrime_inv_recoveredParent_isConnected I,
   phi4WTriplePrime_inv_recoveredParent_isOnePI I,
   phi4WTriplePrime_inv_recoveredParent_isDivergent I⟩

end GaugeGeometry.QFT.Combinatorial
