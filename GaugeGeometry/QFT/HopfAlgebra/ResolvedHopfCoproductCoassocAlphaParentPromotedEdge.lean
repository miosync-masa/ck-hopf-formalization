import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentExactEdge

/-!
# R-6c-body-551 — a PROMOTED parent edge is NOT a bridge of the canonical `W″` parent, NO `Parent` input

Five-hundred-and-fifty-first genuine-body step.  It **re-keys** the flat `SourceSubgraphExactPlus` *promoted-edge*
erase-connectivity blueprint (`Coassoc.lean:20647–20818`, the private
`forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus_{sameRetarget_reachable_erase_promoted,
erase_promoted_isSupportConnected}` chain) to the canonical `W″` parent, proving that erasing a
`(touchedOuterForest …).internalEdges` (Promoted) edge keeps the parent's `.forget` support-connected — WITHOUT any
`Parent` hypothesis.  The proof-SHAPE is the flat blueprint verbatim; only the lemmas are re-keyed to the resolved
parent — **NEW TOPOLOGY = ZERO**.

## The ★RESOLVED-SPECIFIC novelty★ — Step 2 (cross-owner flat-edge separation)

In the flat proof, Case B uses `e ∉ ηx.internalEdges ⟹ count e ηx.internalEdges = 0` DIRECTLY.  In the resolved
carrier this does NOT transport: `e ∉ A.internalEdges` does **not** give `e.forget ∉ A.internalEdges.map forget`,
because `forget` drops the edge ID.  The fix (`legSaturated_parent_forget_notMem_of_ne_owner`): recover `e`'s owner
component `E` (`resolvedAdmissible_mem_internalEdges'`); for the same-retarget owner `A ≠ E`, if some `eA ∈
A.internalEdges` had `eA.forget = e.forget`, then `eA.source = e.source` (`forget_source`), so `A.edges_supported eA`
and `E.edges_supported e` give the COMMON vertex `e.source ∈ A.vertices ∩ E.vertices`, contradicting
`(touchedOuterForest z δ).isPairwiseDisjoint A E (A≠E)`.  Hence `e.forget ∉ A.internalEdges.map forget`
(`Multiset.count … = 0`).  ★`forget` is NEVER assumed injective — the owner + pairwise-disjointness *before* forgetting
is what rules out the cross-owner flat collision (rigidify-then-forget).★

## The wiring (★confirmed `erase_add_left_pos` + `le_add_left`, order Promoted+Exact★)

The RESOLVED parent internal-edge order is `Promoted + Exact` (`recontract548_parent_internalEdges`:
`(touchedOuterForest …).internalEdges + quotientEdgePreimage …`), with **Promoted = the LEFT summand**.  Erasing a
Promoted edge → `parent.forget.internalEdges.erase e.forget = (Promoted.map forget).erase e.forget + Exact.map forget`
via **`Multiset.erase_add_left_pos`** (`e.forget ∈ Promoted.map forget = LEFT summand`).  The Exact skeleton survives
untouched: it is the **RIGHT summand** of the split, so `Exact.map forget ≤ (parent∖e).internalEdges` fires with
**`Multiset.le_add_left`** (`s ≤ t + s`) — NOT `le_add_right` (the flat blueprint's `Exact+Promoted` order made Exact
the left summand; the resolved `Promoted+Exact` order flips it).  In the load-bearing glue, Case B routes into the LEFT
`(Promoted.map forget).erase e.forget` summand via **`le_add_right`** (`s ≤ s + t`).  `forget` is never assumed
injective; no resolved edge-equality is recovered from a flat one — Step 2 REFUTES such a collision.

## Correspondence (flat → resolved, same as 549/550)

```text
SourceSubgraphExactPlus                    → localizedParentWithTouchedLegs (.forget = canonicalLegSaturatedParentForget)
retargetVertex (admissibleForestCanonical…)→ (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1)
ExactInternalEdges                         → quotientEdgePreimage (touchedOuterForest …) (D.starOf …) (touchedLocalComponent …)
PromotedInternalEdges                      → (touchedOuterForest z δ).internalEdges
promoted child ηx (owner)                  → touched component A ∈ (touchedOuterForest z δ).elements
hFresh.eq_of_star_eq                       → canonicalLegSaturatedStarFacts.starOf_injective
isConnectedDivergent_of_mem                → (touchedOuterForest z δ).isConnectedDivergent
admissibleSubgraphQuotientRemainderSubgraph_vertices → localizedParentVertex_retargets            (329)
```

## Steps

1. `legSaturated_parent_erase_promoted_decomp` + `legSaturated_parent_exact_le_erase_promoted` — the split
   (`erase_add_left_pos`, Promoted = LEFT) + Exact-skeleton inclusion (`le_add_left`, Exact = RIGHT summand).
2. ★resolved-specific★ `legSaturated_parent_forget_notMem_of_ne_owner` — cross-owner flat-edge separation via owner +
   pairwise disjointness *before* forgetting; NO `forget` injectivity.
3. **★load-bearing★** `legSaturated_parent_sameRetarget_reachable_erase_promoted` — the same-retarget glue after
   promoted erase.  Four cases (mirroring 549/550); star/star ⇒ SAME owner `A` (`starOf_injective`), then Case A
   (`e ∈ A.internalEdges` ⇒ `A∖e` connected via `no_bridge`, `erase_le_erase` transport) / Case B
   (`e ∉ A.internalEdges` ⇒ Step 2 gives `count = 0`, `A` intact inside `Promoted∖e`).
4. `legSaturated_parent_edgeStep_erase_promoted` / `..._reachable_lift_erase_promoted` — the (UN-erased) δ-skeleton
   edge-step + path lift into `parent∖e.forget` (the Exact half is untouched, `Exact.map forget ≤ (parent∖e)` from
   Step 1, glued via Step 3).
5. **★target★** `legSaturated_parent_erase_promoted_isSupportConnected` + the canonical specialization
   `canonicalLegSaturated_parent_erase_promoted_isSupportConnected` (NO `Parent` argument).

## Scoreboard

```text
canonicalLegSaturated_parent_erase_promoted_isSupportConnected   PROVED   (NO Parent input)
NEW TOPOLOGY                                                     ZERO     (flat blueprint re-keyed)
resolved novelty                                                Step 2 (cross-owner flat-edge separation, rigidify-then-forget)
wiring                                                           erase_add_left_pos / le_add_left / le_add_right (order Promoted+Exact)
parentOnePI residual                                            now the bridge-free ASSEMBLY ONLY (551 + 550 ⇒ all parent edges non-bridges)
```

Next: 552 assembles support-connected (549) + no-bridge (550 Exact + 551 Promoted) ⟹ `parentOnePI` GONE; then
`parentDivergent` ← `IsDivergenceReflectedByAdmissibleForestContract` migration.

Per the HALT/guards: NO `Parent` / round-trip / coassoc input; NO new structure/class/instance; NO bridge-free /
`parentOnePI` assembly (552); NO `parentDivergent` / `IsDivergenceReflectedByAdmissibleForestContract`; NO `forget`
injectivity assumption; NO resolved edge-ID equality recovered from a flat one (Step 2 REFUTES it); NO hardcoded-star
equality (only the SAME selected `D.starOf` allocator is read); no old private flat theorem is publicized or modified;
no facade, no `sorry`/`admit`.
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

/-- **R-6c-body-551 (mono) — support-reachability transports up an internal-edge inclusion.**  A faithful re-derivation
of the flat `supportReachable_mono_of_internalEdges_le` (both the flat and body-549/550 copies are private; NEW TOPOLOGY
= ZERO). -/
private theorem legSaturated_supportReachable_mono_of_internalEdges_le_promoted
    {H K : FeynmanGraph} (hle : H.internalEdges ≤ K.internalEdges)
    {u v : VertexId} (h : H.SupportReachable u v) : K.SupportReachable u v := by
  refine SimpleGraph.Reachable.mono ?_ h
  intro a b hab
  obtain ⟨hne, e, heH, hend⟩ := hab
  exact ⟨hne, e, Multiset.mem_of_le hle heH, hend⟩

/-! ## Step 1 — the promoted-edge erase decomposition (★`erase_add_left_pos`, order Promoted+Exact★). -/

/-- **R-6c-body-551 — Step 1a: the promoted-edge erase decomposition.**  Erasing the `forget` of a Promoted edge from
the parent `.forget` graph leaves `(Promoted.map forget).erase e.forget + Exact.map forget`.  ★The wiring: Promoted is
the LEFT summand and Exact the RIGHT, so `Multiset.erase_add_left_pos` (NOT `_right`) fires; the erased edge lives in
the LEFT (Promoted) half (`Multiset.mem_map_of_mem`).★ -/
theorem legSaturated_parent_erase_promoted_decomp (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges) :
    ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges).erase e.forget
      = ((touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget).erase e.forget
        + (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
            (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget := by
  have hmemF : e.forget ∈ (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget :=
    Multiset.mem_map_of_mem _ he
  have hbase : (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges
      = (touchedOuterForest z δ).internalEdges.map ResolvedFeynmanEdge.forget
        + (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
            (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges,
      recontract548_parent_internalEdges, Multiset.map_add]
  rw [hbase, Multiset.erase_add_left_pos _ hmemF]

/-- **R-6c-body-551 — Step 1b: the Exact half survives the promoted-edge erase.**  `Exact.map forget ≤
(parent∖e.forget).internalEdges` (via `eraseInternalEdge_internalEdges` + Step 1a + `Multiset.le_add_left`, Exact being
the RIGHT summand `s` of `t + s`). -/
theorem legSaturated_parent_exact_le_erase_promoted (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges) :
    (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
        (touchedLocalComponent z δ)).map ResolvedFeynmanEdge.forget
      ≤ ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
          e.forget).internalEdges := by
  rw [FeynmanGraph.eraseInternalEdge_internalEdges, legSaturated_parent_erase_promoted_decomp z δ datum hE hL he]
  exact Multiset.le_add_left _ _

/-! ## Step 2 — ★resolved-specific★ cross-owner flat-edge separation (rigidify-then-forget). -/

/-- **R-6c-body-551 — Step 2 (★resolved novelty★): cross-owner flat-edge separation.**  For distinct touched components
`A ≠ E` and an edge `e ∈ E.internalEdges`, `e.forget ∉ A.internalEdges.map forget`.  If it were, some `eA ∈
A.internalEdges` would share `eA.forget = e.forget`, hence `eA.source = e.source`; `A.edges_supported eA` /
`E.edges_supported e` place `e.source` in both `A.vertices` and `E.vertices`, contradicting the touched forest's
pairwise vertex-disjointness.  ★`forget` is NOT assumed injective — the owner + disjointness *before* forgetting is what
refutes the flat collision.★ -/
theorem legSaturated_parent_forget_notMem_of_ne_owner (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {A E : ResolvedFeynmanSubgraph G}
    (hA : A ∈ (touchedOuterForest z δ).elements)
    (hEmem : E ∈ (touchedOuterForest z δ).elements)
    (hne : A ≠ E)
    {e : ResolvedFeynmanEdge} (heE : e ∈ E.internalEdges) :
    e.forget ∉ A.internalEdges.map ResolvedFeynmanEdge.forget := by
  intro hmem
  obtain ⟨eA, heA, hforget⟩ := Multiset.mem_map.mp hmem
  have hsrc : eA.source = e.source := by
    have h := congrArg FeynmanEdge.source hforget
    simpa only [ResolvedFeynmanEdge.forget_source] using h
  obtain ⟨hsA, _⟩ := A.edges_supported eA heA
  obtain ⟨hsE, _⟩ := E.edges_supported e heE
  have hvA : e.source ∈ A.vertices := hsrc ▸ hsA
  have hdisj : A.Disjoint E := (touchedOuterForest z δ).isPairwiseDisjoint hA hEmem hne
  exact Finset.disjoint_left.mp hdisj hvA hsE

/-! ## Step 3 — the same-retarget gluing avoiding a Promoted edge (★load-bearing★). -/

/-- **R-6c-body-551 — Step 3 (★load-bearing★): same-retarget gluing avoiding a Promoted edge.**  Two parent vertices
with equal touched-forest retarget image are `(parent∖e.forget)`-support-reachable — four cases mirroring 549/550: both
non-star ⇒ `x = y`; mixed ⇒ `starOf_fresh` contradiction; star/star ⇒ `starOf_injective` identifies the SAME owner
component `A` (SAME `(G, z.1.1)` allocator).  Within `A` a `by_cases e ∈ A.internalEdges`: **Case A** — `A` is 1PI so
`A∖e.forget` is support-connected (`no_bridge`), transported by `erase_le_erase`; **Case B** — `A` is intact, and
`A.internalEdges.map forget ≤ (Promoted∖e.forget)` since `e`'s owner `E ≠ A` gives `count e.forget = 0` (Step 2). -/
theorem legSaturated_parent_sameRetarget_reachable_erase_promoted (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges)
    {x y : VertexId}
    (hx : x ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hy : y ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hret : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) x
          = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) y) :
    ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).SupportReachable x y := by
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
      have hA1PI : Ax.forget.toFeynmanGraph.IsOnePI :=
        ((touchedOuterForest z δ).isConnectedDivergent Ax hAx).isOnePI
      by_cases hee : e ∈ Ax.internalEdges
      · -- Case A: `e` is an edge of the owner `Ax`; `Ax∖e.forget` is support-connected.
        have he_forget : e.forget ∈ Ax.forget.toFeynmanGraph.internalEdges := by
          simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
          exact Multiset.mem_map_of_mem _ hee
        have hAxErase : (Ax.forget.toFeynmanGraph.eraseInternalEdge e.forget).IsSupportConnected := by
          by_contra hnot
          exact hA1PI.no_bridge e.forget he_forget ⟨he_forget, hnot⟩
        have hreach : (Ax.forget.toFeynmanGraph.eraseInternalEdge e.forget).SupportReachable x y :=
          hAxErase hxAx hyAy
        have hsub : Ax.internalEdges ≤ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges := by
          show Ax.internalEdges ≤ (touchedOuterForest z δ).internalEdges
              + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
          exact le_trans (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hAx) (Multiset.le_add_right _ _)
        have hsubF : Ax.forget.toFeynmanGraph.internalEdges
            ≤ (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges := by
          simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
          exact Multiset.map_le_map hsub
        have hle : (Ax.forget.toFeynmanGraph.eraseInternalEdge e.forget).internalEdges
            ≤ ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
                e.forget).internalEdges := by
          rw [FeynmanGraph.eraseInternalEdge_internalEdges, FeynmanGraph.eraseInternalEdge_internalEdges]
          exact Multiset.erase_le_erase e.forget hsubF
        exact legSaturated_supportReachable_mono_of_internalEdges_le_promoted hle hreach
      · -- Case B: `e ∉ Ax.internalEdges`; `Ax` is intact inside `Promoted∖e.forget` (Step 2 gives count 0).
        have hreach : Ax.forget.toFeynmanGraph.SupportReachable x y :=
          ((touchedOuterForest z δ).isConnectedDivergent Ax hAx).1 hxAx hyAy
        obtain ⟨Ee, hEe, heE⟩ := resolvedAdmissible_mem_internalEdges'.mp he
        have hne : Ax ≠ Ee := fun h => hee (h ▸ heE)
        have hnotmem : e.forget ∉ Ax.internalEdges.map ResolvedFeynmanEdge.forget :=
          legSaturated_parent_forget_notMem_of_ne_owner z δ hAx hEe hne heE
        have hle : Ax.forget.toFeynmanGraph.internalEdges
            ≤ ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
                e.forget).internalEdges := by
          rw [FeynmanGraph.eraseInternalEdge_internalEdges, legSaturated_parent_erase_promoted_decomp z δ datum hE hL he]
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
              (Multiset.map_le_map (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hAx)) a
        exact legSaturated_supportReachable_mono_of_internalEdges_le_promoted hle hreach

/-! ## Step 4a — the single-edge lift on the un-erased δ-skeleton. -/

/-- **R-6c-body-551 — Step 4a: edge-step on the un-erased δ-skeleton.**  A δ support-adjacency `c—b` (the Exact half is
UNTOUCHED by a promoted erase, so δ is the full `touchedLocalComponent`) + a source-preimage of `c` yields a
source-preimage of `b` reachable from it in `parent∖e.forget`: the Exact preimage edge (`quotientEdgePreimage_map`)
survives in `parent∖e.forget` (Step 1b), and the endpoints glue via Step 3. -/
theorem legSaturated_parent_edgeStep_erase_promoted (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges)
    {c b : VertexId}
    (hadj : (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportAdj c b)
    {wc : VertexId}
    (hwc : wc ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hwcc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wb = b ∧
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable wc wb := by
  classical
  obtain ⟨hcb, eδ, heδ, hend⟩ := hadj
  simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges] at heδ
  obtain ⟨eR, heR, rfl⟩ := Multiset.mem_map.mp heδ
  simp only [ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target] at hend
  have heR2 : eR ∈ (quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
      (touchedLocalComponent z δ)).map ((touchedOuterForest z δ).retargetEdge (D.starOf G z.1.1)) := by
    rw [quotientEdgePreimage_map]; exact heR
  obtain ⟨eE, heE, hmap⟩ := Multiset.mem_map.mp heR2
  have hrs : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = eR.source := by
    rw [← hmap]; rfl
  have hrt : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = eR.target := by
    rw [← hmap]; rfl
  have heEPlus : eE ∈ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges := by
    show eE ∈ (touchedOuterForest z δ).internalEdges
      + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
    exact Multiset.mem_add.mpr (Or.inr heE)
  obtain ⟨hsE, htE⟩ := (localizedParentWithTouchedLegs z δ datum hE hL).edges_supported eE heEPlus
  -- `eE.forget` survives in `parent∖e.forget` (it lies in the untouched Exact half).
  have heEsurvive : eE.forget ∈
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).internalEdges :=
    Multiset.mem_of_le (legSaturated_parent_exact_le_erase_promoted z δ datum hE hL he)
      (Multiset.mem_map_of_mem _ heE)
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
      (legSaturated_parent_sameRetarget_reachable_erase_promoted Fstar z δ datum hE hL he hwc hsE
        (hwcc.trans hsEc.symm)).trans (plusAdj hne)⟩
  · have hsEb : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = b := hrs.trans hsb
    have htEc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = c := hrt.trans htc
    have hne : eE.source ≠ eE.target := fun h =>
      hcb (htEc.symm.trans ((congrArg _ h.symm).trans hsEb))
    exact ⟨eE.source, hsE, hsEb,
      (legSaturated_parent_sameRetarget_reachable_erase_promoted Fstar z δ datum hE hL he hwc htE
        (hwcc.trans htEc.symm)).trans (plusAdj hne).symm⟩

/-! ## Step 4b — the full path lift on the un-erased δ-skeleton. -/

/-- **R-6c-body-551 — Step 4b: path lift on the un-erased δ-skeleton.**  A full δ support-reachability path lifts to
reachability in `parent∖e.forget`: `Relation.ReflTransGen` induction, `edgeStep_erase_promoted` per adjacency. -/
theorem legSaturated_parent_reachable_lift_erase_promoted (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges)
    {a b u : VertexId}
    (hu : u ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hua : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u = a)
    (hab : (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportReachable a b) :
    ∃ w, w ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) w = b ∧
      ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
        e.forget).SupportReachable u w := by
  have hrtg : Relation.ReflTransGen (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ :=
        legSaturated_parent_edgeStep_erase_promoted Fstar z δ datum hE hL he hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-! ## Step 5 — the target: a Promoted parent edge is not a bridge. -/

/-- **R-6c-body-551 — Step 5 (generic): erasing a Promoted edge keeps the parent `.forget` support-connected.**  The
Exact half is UNTOUCHED, so the full un-erased δ-skeleton (support-connected via
`touchedLocalComponent_isConnectedDivergent`) lifts (Step 4b) and the endpoints glue (Step 3); both endpoints retarget
into `δ.vertices` (`localizedParentVertex_retargets`). -/
theorem legSaturated_parent_erase_promoted_isSupportConnected (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hδCD : δ.forget.IsConnectedDivergent)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ).internalEdges) :
    ((localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.eraseInternalEdge
      e.forget).IsSupportConnected := by
  classical
  have hδConn : (touchedLocalComponent z δ).forget.toFeynmanGraph.IsSupportConnected :=
    (touchedLocalComponent_isConnectedDivergent z δ hδCD).1
  intro u v hu hv
  rw [FeynmanGraph.eraseInternalEdge_vertices] at hu hv
  have hu' : u ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices := hu
  have hv' : v ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices := hv
  have hretu : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u ∈ δ.vertices :=
    localizedParentVertex_retargets z δ datum hE hL hu'
  have hretv : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v ∈ δ.vertices :=
    localizedParentVertex_retargets z δ datum hE hL hv'
  have hab : (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportReachable
      ((touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u)
      ((touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v) :=
    hδConn hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ :=
    legSaturated_parent_reachable_lift_erase_promoted Fstar z δ datum hE hL he hu' rfl hab
  exact huw.trans
    (legSaturated_parent_sameRetarget_reachable_erase_promoted Fstar z δ datum hE hL he hw hv' hwv)

/-- **R-6c-body-551 ∎ (★target★) — a Promoted edge of the canonical `W″` parent is NOT a bridge**, with NO `Parent`
input.  The canonical specialization of the generic Step 5: fix the canonical datum / ambient and read `δ`'s
connected-divergence off `z.2.1.isConnectedDivergent` (from `δ.2 : δ.1 ∈ forestDomain z`).  ⟹ together with body-550
(Exact edges) EVERY parent internal edge is a non-bridge; the `parentOnePI` residual is now the bridge-free ASSEMBLY
ONLY (body-552). -/
theorem canonicalLegSaturated_parent_erase_promoted_isSupportConnected {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (touchedOuterForest z δ.1).internalEdges) :
    ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph.eraseInternalEdge e.forget).IsSupportConnected := by
  classical
  have hδCD : δ.1.forget.IsConnectedDivergent :=
    z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1
  exact legSaturated_parent_erase_promoted_isSupportConnected canonicalLegSaturatedStarFacts z δ.1
    (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
    (liveAmbient_edges_supported ambientSupportOfW'' z)
    (liveAmbient_legs_supported ambientSupportOfW'' z)
    hδCD he

end GaugeGeometry.QFT.Combinatorial
