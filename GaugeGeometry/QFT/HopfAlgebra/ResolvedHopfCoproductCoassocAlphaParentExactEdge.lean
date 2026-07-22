import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentConnected

/-!
# R-6c-body-550 — an EXACT parent edge is NOT a bridge of the canonical `W″` parent, NO `Parent` input

Five-hundred-and-fiftieth genuine-body step.  It **re-keys** the flat `SourceSubgraphExactPlus` *exact-edge*
erase-connectivity blueprint (`Coassoc.lean:20180–20508`, the private
`forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus_{promotedComponent_reachable_in,
sameRetarget_reachable_in, edgeStep_erase_exact, reachable_lift_erase_exact, erase_exact_isSupportConnected}`
chain) to the canonical `W″` parent, proving that erasing a `quotientEdgePreimage` (Exact) edge keeps the parent's
`.forget` support-connected — WITHOUT any `Parent` hypothesis.  The proof-SHAPE is the flat blueprint verbatim;
only the lemmas are re-keyed to the resolved parent — **NEW TOPOLOGY = ZERO**.

## The ONE wiring change (★confirmed `erase_add_right_pos`, NOT `_left`★)

The RESOLVED parent internal-edge order is `Promoted + Exact`
(`recontract548_parent_internalEdges`: `(touchedOuterForest …).internalEdges + quotientEdgePreimage …`), with
**Exact = the RIGHT summand**.  The flat blueprint (order `Exact + Promoted`) uses `Multiset.erase_add_left_pos`
and `Multiset.le_add_left`; the resolved version therefore uses **`Multiset.erase_add_right_pos`**
(`(s + t).erase a = s + t.erase a` for `a ∈ t`) and **`Multiset.le_add_right`** (Promoted is the LEFT summand `s`).
Everything works one map-`forget` layer up: the parent `.forget.toFeynmanGraph.internalEdges`
`= Promoted.map forget + Exact.map forget`, and `e.forget ∈ Exact.map forget` via `Multiset.mem_map_of_mem`.
`forget` is **never assumed injective**; no resolved edge-equality is recovered from a flat one — everything is a
`Multiset … map/erase/count` computation.

## Correspondence (flat → resolved)

```text
SourceSubgraphExactPlus                    → localizedParentWithTouchedLegs (.forget = canonicalLegSaturatedParentForget)
retargetVertex (admissibleForestCanonical…)→ (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1)
ExactInternalEdges                         → quotientEdgePreimage (touchedOuterForest …) (D.starOf …) (touchedLocalComponent …)
PromotedInternalEdges                      → (touchedOuterForest z δ).internalEdges
retargetEdge                               → (touchedOuterForest z δ).retargetEdge (D.starOf …)
δ / erased retarget edge d                 → touchedLocalComponent z δ / ((touchedOuterForest).retargetEdge … e)
admissibleSubgraphQuotientRemainderSubgraph_vertices → localizedParentVertex_retargets                         (329)
```

## Steps

1. `legSaturated_parent_insertedComponent_reachable_in K` — Helper 1 generalized to any `K` whose internal edges
   contain the promoted half (`hPromLe`): two vertices of a touched component are `K.SupportReachable`.
2. `legSaturated_parent_sameRetarget_reachable_in K` — the K-generalized same-retarget glue; four cases identical to
   body-549 Step 4, star/star uses Step 1 (in `K`), reading only the SAME `D.starOf` allocator.
3. `legSaturated_parent_erase_exact_decomp` + `legSaturated_parent_promoted_le_erase_exact` — the multiplicity-safe
   erase decomposition `(parent.forget.internalEdges).erase e.forget = Promoted.map forget + (Exact.map forget).erase
   e.forget` (via `recontract548_parent_internalEdges` mapped by `forget` + **`erase_add_right_pos`**), and the
   promoted-half inclusion (`le_add_right`).
4. `legSaturated_parent_edgeStep_erase_exact` — a `δ∖d`-adjacency step lifted to the parent-erase graph
   (`K = parent∖e.forget`): the surviving Exact preimage edge (`map_erase_of_mem`) is a parent-erase `SupportAdj`,
   glued via Step 2 with `hKle` from Step 3.
5. `legSaturated_parent_reachable_lift_erase_exact` — `Relation.ReflTransGen` induction, edge-step per adjacency.
6. **★target★** `legSaturated_parent_erase_exact_isSupportConnected` + the canonical specialization
   `canonicalLegSaturated_parent_erase_exact_isSupportConnected` (NO `Parent` argument): `δ∖d` is connected
   (`IsOnePI.no_bridge`), the promoted half survives (Step 3), the endpoints retarget into `δ.vertices`
   (`localizedParentVertex_retargets`), the path lifts (Step 5) and the endpoints glue (Step 2).

## Scoreboard

```text
canonicalLegSaturated_parent_erase_exact_isSupportConnected   PROVED   (NO Parent input)
NEW TOPOLOGY                                                  ZERO     (flat blueprint re-keyed)
wiring change                                                 erase_add_right_pos / le_add_right (order Promoted+Exact)
parentOnePI residual                                          now Promoted edges ONLY (exact edges not bridges)
```

Next: 551 promoted-edge erase / 552 bridge-free assembly ⟹ `parentOnePI` GONE; then `parentDivergent` migration from
`IsDivergenceReflectedByAdmissibleForestContract`.

Per the HALT/guards: NO `Parent` / round-trip / coassoc input; NO new structure/class/instance; NO promoted-edge erase
(551) / bridge-free assembly (552); NO `forget` injectivity assumption; NO resolved edge-ID equality recovered from a
flat one; NO hardcoded-star equality (only the SAME selected `D.starOf` allocator is read); the physics
`IsDivergenceReflectedByAdmissibleForestContract` instance is NOT consumed; no old private flat theorem is publicized
or modified; no facade, no `sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

/-- **R-6c-body-550 (mono) — support-reachability transports up an internal-edge inclusion.**  A faithful re-derivation
of the flat `supportReachable_mono_of_internalEdges_le` (both the flat and body-549 copies are private; NEW TOPOLOGY =
ZERO). -/
private theorem legSaturated_supportReachable_mono_of_internalEdges_le'
    {H K : FeynmanGraph} (hle : H.internalEdges ≤ K.internalEdges)
    {u v : VertexId} (h : H.SupportReachable u v) : K.SupportReachable u v := by
  refine SimpleGraph.Reachable.mono ?_ h
  intro a b hab
  obtain ⟨hne, e, heH, hend⟩ := hab
  exact ⟨hne, e, Multiset.mem_of_le hle heH, hend⟩

/-! ## Step 1 — within-touched-component gluing (Helper 1, target-graph generalized). -/

/-- **R-6c-body-550 — Step 1: within-touched-component reachability, generalized to `K`.**  Helper 1 relativized to any
graph `K` whose internal edges contain the promoted half (`hPromLe`): two vertices of a touched component `A` are
`K.SupportReachable` (`A.forget` is support-connected, `A.internalEdges.map forget ≤ Promoted.map forget ≤
K.internalEdges`). -/
theorem legSaturated_parent_insertedComponent_reachable_in (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (touchedOuterForest z δ).elements)
    {K : FeynmanGraph}
    (hPromLe : (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget ≤ K.internalEdges)
    {u v : VertexId} (hu : u ∈ A.vertices) (hv : v ∈ A.vertices) :
    K.SupportReachable u v := by
  have hAcd : A.forget.IsConnectedDivergent := (touchedOuterForest z δ).isConnectedDivergent A hA
  have hAconn : A.forget.toFeynmanGraph.IsSupportConnected := hAcd.1
  have hreach : A.forget.toFeynmanGraph.SupportReachable u v := hAconn hu hv
  have hsub : A.internalEdges ≤ (touchedOuterForest z δ).internalEdges :=
    Finset.single_le_sum (fun i _ => Multiset.zero_le _) hA
  have hle : A.forget.toFeynmanGraph.internalEdges ≤ K.internalEdges := by
    have h2 : A.forget.toFeynmanGraph.internalEdges
        ≤ (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget := by
      simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
      exact Multiset.map_le_map hsub
    exact le_trans h2 hPromLe
  exact legSaturated_supportReachable_mono_of_internalEdges_le' hle hreach

/-! ## Step 2 — the same-retarget gluing, target-graph generalized (★load-bearing★). -/

/-- **R-6c-body-550 — Step 2 (★load-bearing★): same-retarget gluing, generalized to `K`.**  Two parent vertices with
equal touched-forest retarget image are `K.SupportReachable` — four cases mirroring body-549 Step 4: both non-star ⇒
`x = y`; mixed ⇒ `starOf_fresh` contradiction; star/star ⇒ `starOf_injective` identifies the SAME owner component (SAME
`(G, z.1.1)` allocator — no cross-ambient star equality), where Step 1 (in `K`) connects them. -/
theorem legSaturated_parent_sameRetarget_reachable_in (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {K : FeynmanGraph}
    (hPromLe : (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget ≤ K.internalEdges)
    {x y : VertexId}
    (hx : x ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hy : y ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hret : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) x
          = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) y) :
    K.SupportReachable x y := by
  classical
  rcases legSaturated_parent_retarget_cases z δ (v := x) with hx0 | ⟨Ax, hAx, hxAx, hxret⟩
  · rcases legSaturated_parent_retarget_cases z δ (v := y) with hy0 | ⟨Ay, hAy, hyAy, hyret⟩
    · rw [show x = y from hx0.symm.trans (hret.trans hy0)]
      exact FeynmanGraph.SupportReachable.refl _ _
    · exfalso
      have hAyz : Ay ∈ z.1.1.elements := (mem_touchedOuterComponents.mp hAy).1
      have hxstar : x = D.starOf G z.1.1 Ay := hx0.symm.trans (hret.trans hyret)
      exact Fstar.starOf_fresh G z.1.1 Ay hAyz
        (hxstar ▸ (localizedParentWithTouchedLegs z δ datum hE hL).vertices_subset hx)
  · rcases legSaturated_parent_retarget_cases z δ (v := y) with hy0 | ⟨Ay, hAy, hyAy, hyret⟩
    · exfalso
      have hAxz : Ax ∈ z.1.1.elements := (mem_touchedOuterComponents.mp hAx).1
      have hystar : y = D.starOf G z.1.1 Ax := hy0.symm.trans (hret.symm.trans hxret)
      exact Fstar.starOf_fresh G z.1.1 Ax hAxz
        (hystar ▸ (localizedParentWithTouchedLegs z δ datum hE hL).vertices_subset hy)
    · have hAxz : Ax ∈ z.1.1.elements := (mem_touchedOuterComponents.mp hAx).1
      have hAyz : Ay ∈ z.1.1.elements := (mem_touchedOuterComponents.mp hAy).1
      have hstar : D.starOf G z.1.1 Ax = D.starOf G z.1.1 Ay :=
        hxret.symm.trans (hret.trans hyret)
      have hAeq : Ax = Ay := Fstar.starOf_injective G z.1.1 hAxz hAyz hstar
      subst hAeq
      exact legSaturated_parent_insertedComponent_reachable_in z δ datum hE hL hAx hPromLe hxAx hyAy

/-! ## Step 3 — the exact-edge erase decomposition (★`erase_add_right_pos`, order Promoted+Exact★). -/

/-- **R-6c-body-550 — Step 3a: the exact-edge erase decomposition.**  Erasing the `forget` of an Exact edge from the
parent `.forget` graph leaves `Promoted.map forget + (Exact.map forget).erase e.forget`.  ★The one wiring change:
Promoted is the LEFT summand and Exact the RIGHT, so `Multiset.erase_add_right_pos` (NOT `_left`) is what fires; the
erased edge lives in the RIGHT (Exact) half (`Multiset.mem_map_of_mem`).★ -/
theorem legSaturated_parent_erase_exact_decomp (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)) :
    ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges).erase e.forget
      = (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        + ((quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
              (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget).erase e.forget := by
  have hmemF : e.forget ∈ (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
      (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget :=
    Multiset.mem_map_of_mem _ he
  have hbase : (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges
      = (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        + (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
            (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges,
      recontract548_parent_internalEdges, Multiset.map_add]
  rw [hbase, Multiset.erase_add_right_pos _ hmemF]

/-- **R-6c-body-550 — Step 3b: the promoted half survives the exact-edge erase.**  `Promoted.map forget ≤
(parent∖e.forget).internalEdges` (via `eraseInternalEdge_internalEdges` + Step 3a + `Multiset.le_add_right`, Promoted
being the LEFT summand). -/
theorem legSaturated_parent_promoted_le_erase_exact (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)) :
    (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
      ≤ ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).internalEdges := by
  rw [FeynmanGraph.eraseInternalEdge_internalEdges, legSaturated_parent_erase_exact_decomp z δ datum hE hL he]
  exact Multiset.le_add_right _ _

/-! ## Step 4 — the single-edge lift avoiding the erased Exact edge. -/

/-- **R-6c-body-550 — Step 4: edge-step avoiding the erased Exact edge.**  A `δ∖d`-support-adjacency `c—b` (where `d =
retargetEdge e`) + a source-preimage of `c` yields a source-preimage of `b` reachable from it in `parent∖e.forget`: the
`δ∖d` edge still has a surviving Exact preimage `eE ≠ e` (`map_erase_of_mem`, both `forget` and `retargetEdge` layers)
that lives in `parent∖e.forget` (Step 3a decomp); the promoted half is untouched so Step 2 (`K = parent∖e.forget`,
`hKle` from Step 3b) glues the endpoints. -/
theorem legSaturated_parent_edgeStep_erase_exact (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ))
    {c b : VertexId}
    (hadj : ((touchedLocalComponent z δ).forget.toFeynmanGraph.eraseInternalEdge
        ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget).SupportAdj c b)
    {wc : VertexId}
    (hwc : wc ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hwcc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wb = b ∧
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable wc wb := by
  classical
  obtain ⟨hcb, eδ, heδ, hend⟩ := hadj
  rw [FeynmanGraph.eraseInternalEdge_internalEdges] at heδ
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges] at heδ
  -- `d := retargetEdge e` is a `touchedLocalComponent`-edge; push the `forget`-erase inside the map.
  have hd_res : (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e
      ∈ (touchedLocalComponent z δ).internalEdges := by
    rw [← quotientEdgePreimage_map (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)]
    exact Multiset.mem_map_of_mem _ he
  rw [← Multiset.map_erase_of_mem ResolvedFeynmanEdge.forget _ hd_res] at heδ
  obtain ⟨eR, heRerase, rfl⟩ := Multiset.mem_map.mp heδ
  simp only [ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target] at hend
  -- `eR ∈ δ.internalEdges.erase d = (Exact.erase e).map retargetEdge`, so recover an Exact preimage `eE ≠ e`.
  have heRerase' : eR ∈ ((quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
      (touchedLocalComponent z δ)).erase e).map ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1)) := by
    rw [Multiset.map_erase_of_mem _ _ he, quotientEdgePreimage_map]
    exact heRerase
  obtain ⟨eE, heEerase, hmap⟩ := Multiset.mem_map.mp heRerase'
  have heE : eE ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) :=
    Multiset.mem_of_mem_erase heEerase
  have hrs : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = eR.source := by
    rw [← hmap]; rfl
  have hrt : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = eR.target := by
    rw [← hmap]; rfl
  -- `eE` sits in the parent's internal edges, hence its endpoints are supported.
  have heEPlus : eE ∈ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges := by
    rw [recontract548_parent_internalEdges]
    exact Multiset.mem_add.mpr (Or.inr heE)
  obtain ⟨hsE, htE⟩ := (localizedParentWithTouchedLegs z δ datum hE hL).edges_supported eE heEPlus
  -- `eE.forget` survives in `parent∖e.forget` (it is in the erased Exact half).
  have heEsurvive : eE.forget ∈
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).internalEdges := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, legSaturated_parent_erase_exact_decomp z δ datum hE hL he]
    refine Multiset.mem_add.mpr (Or.inr ?_)
    rw [← Multiset.map_erase_of_mem ResolvedFeynmanEdge.forget _ he]
    exact Multiset.mem_map_of_mem _ heEerase
  have hKle := legSaturated_parent_promoted_le_erase_exact z δ datum hE hL he
  have plusAdj : eE.source ≠ eE.target →
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable eE.source eE.target :=
    fun hne => SimpleGraph.Adj.reachable
      (show ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).SupportAdj eE.source eE.target from ⟨hne, eE.forget, heEsurvive, Or.inl ⟨rfl, rfl⟩⟩)
  rcases hend with ⟨hsc, htb⟩ | ⟨hsb, htc⟩
  · have hsEc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = c := hrs.trans hsc
    have htEb : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = b := hrt.trans htb
    have hne : eE.source ≠ eE.target := fun h =>
      hcb (hsEc.symm.trans ((congrArg _ h).trans htEb))
    exact ⟨eE.target, htE, htEb,
      (legSaturated_parent_sameRetarget_reachable_in Fstar z δ datum hE hL hKle hwc hsE
        (hwcc.trans hsEc.symm)).trans (plusAdj hne)⟩
  · have hsEb : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = b := hrs.trans hsb
    have htEc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = c := hrt.trans htc
    have hne : eE.source ≠ eE.target := fun h =>
      hcb (htEc.symm.trans ((congrArg _ h.symm).trans hsEb))
    exact ⟨eE.source, hsE, hsEb,
      (legSaturated_parent_sameRetarget_reachable_in Fstar z δ datum hE hL hKle hwc htE
        (hwcc.trans htEc.symm)).trans (plusAdj hne).symm⟩

/-! ## Step 5 — the full path lift avoiding the erased Exact edge. -/

/-- **R-6c-body-550 — Step 5: path lift avoiding the erased Exact edge.**  A full `δ∖d`-support-reachability path lifts
to reachability in `parent∖e.forget`: `Relation.ReflTransGen` induction, `edgeStep_erase_exact` per adjacency. -/
theorem legSaturated_parent_reachable_lift_erase_exact (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ))
    {a b u : VertexId}
    (hu : u ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hua : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u = a)
    (hab : ((touchedLocalComponent z δ).forget.toFeynmanGraph.eraseInternalEdge
        ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget).SupportReachable a b) :
    ∃ w, w ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) w = b ∧
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable u w := by
  have hrtg : Relation.ReflTransGen
      ((touchedLocalComponent z δ).forget.toFeynmanGraph.eraseInternalEdge
        ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget).SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ :=
        legSaturated_parent_edgeStep_erase_exact Fstar z δ datum hE hL he hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-! ## Step 6 — the target: an Exact parent edge is not a bridge. -/

/-- **R-6c-body-550 — Step 6 (generic): erasing an Exact edge keeps the parent `.forget` support-connected.**  Its
retarget `d` is a `touchedLocalComponent`-edge; `δ` is 1PI so `δ∖d` is connected (`IsOnePI.no_bridge`); the promoted
half survives (Step 3b); both endpoints retarget into `δ.vertices` (`localizedParentVertex_retargets`); the path lifts
(Step 5) and the endpoints glue (Step 2). -/
theorem legSaturated_parent_erase_exact_isSupportConnected (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hδCD : δ.forget.IsConnectedDivergent)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)) :
    ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).IsSupportConnected := by
  classical
  -- `d := retargetEdge e` is a `touchedLocalComponent`-edge.
  have hd_res : (touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e
      ∈ (touchedLocalComponent z δ).internalEdges := by
    rw [← quotientEdgePreimage_map (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)]
    exact Multiset.mem_map_of_mem _ he
  have hd : ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget
      ∈ (touchedLocalComponent z δ).forget.toFeynmanGraph.internalEdges := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    exact Multiset.mem_map_of_mem _ hd_res
  have hδConnDiv : (touchedLocalComponent z δ).forget.IsConnectedDivergent :=
    touchedLocalComponent_isConnectedDivergent z δ hδCD
  -- `δ` is 1PI so `δ∖d` is connected.
  have hδErase : ((touchedLocalComponent z δ).forget.toFeynmanGraph.eraseInternalEdge
      ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget).IsSupportConnected := by
    by_contra hnot
    exact hδConnDiv.isOnePI.no_bridge _ hd ⟨hd, hnot⟩
  have hKle := legSaturated_parent_promoted_le_erase_exact z δ datum hE hL he
  intro u v hu hv
  rw [FeynmanGraph.eraseInternalEdge_vertices] at hu hv
  have hu' : u ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices := hu
  have hv' : v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices := hv
  have hretu : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u ∈ δ.vertices :=
    localizedParentVertex_retargets z δ datum hE hL hu'
  have hretv : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices :=
    localizedParentVertex_retargets z δ datum hE hL hv'
  have hab : ((touchedLocalComponent z δ).forget.toFeynmanGraph.eraseInternalEdge
      ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1) e).forget).SupportReachable
      ((touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u)
      ((touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v) :=
    hδErase hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ :=
    legSaturated_parent_reachable_lift_erase_exact Fstar z δ datum hE hL he hu' rfl hab
  exact huw.trans
    (legSaturated_parent_sameRetarget_reachable_in Fstar z δ datum hE hL hKle hw hv' hwv)

/-- **R-6c-body-550 ∎ (★target★) — an Exact edge of the canonical `W″` parent is NOT a bridge**, with NO `Parent`
input.  The canonical specialization of the generic Step 6: fix the canonical datum / ambient and read `δ`'s
connected-divergence off `z.2.1.isConnectedDivergent` (from `δ.2 : δ.1 ∈ forestDomain z`).  ⟹ the `parentOnePI`
residual is now Promoted edges ONLY. -/
theorem canonicalLegSaturated_parent_erase_exact_isSupportConnected {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    {e : ResolvedFeynmanEdge}
    (he : e ∈ quotientEdgePreimage (touchedOuterForest z δ.1)
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) (touchedLocalComponent z δ.1)) :
    ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph.eraseInternalEdge e.forget).IsSupportConnected := by
  classical
  have hδCD : δ.1.forget.IsConnectedDivergent :=
    z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1
  exact legSaturated_parent_erase_exact_isSupportConnected canonicalLegSaturatedStarFacts z δ.1
    (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
    (liveAmbient_edges_supported ambientSupportOfW'' z)
    (liveAmbient_legs_supported ambientSupportOfW'' z)
    hδCD he

end GaugeGeometry.QFT.Combinatorial
