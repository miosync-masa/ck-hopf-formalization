import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentArchitectureAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentRetarget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentCD
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInner
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-body-549 — the canonical `W″` parent is support-connected (`IsConnected`), NO `Parent` input

Five-hundred-and-forty-ninth genuine-body step.  It **re-keys** the flat `SourceSubgraphExactPlus` connectivity blueprint
(`Coassoc.lean:19955–20172`, the private `forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus_*` chain) to the
canonical `W″` parent, discharging body-548's **Connected trunk of `parentCD`** WITHOUT any `Parent` hypothesis.  The
proof-SHAPE is the flat blueprint verbatim; only the lemmas are re-keyed to the resolved parent — **NEW TOPOLOGY = ZERO**.

## Correspondence (flat → resolved)

```text
SourceSubgraphExactPlus                    → localizedParentWithTouchedLegs z δ.1 datum hE hL
   its .forget                             → canonicalLegSaturatedParentForget z δ                      (body-548)
retargetVertex (admissibleForestCanonical…)→ (touchedOuterForest z δ.1).retargetVertex (D.starOf G z.1.1)
ExactInternalEdges                         → quotientEdgePreimage (touchedOuterForest …) (D.starOf …) (touchedLocalComponent …)
PromotedInternalEdges                      → (touchedOuterForest z δ.1).internalEdges
SourceVertices                             → (localizedParentWithTouchedLegs …).vertices
quotient component δ                       → touchedLocalComponent z δ.1  (touchedLocalComponent_isConnectedDivergent, 322)
promoted child / within-child gluing       → the touched component A ∈ touchedOuterForest.elements, CD via its own field
"retargets into δ.vertices"                → localizedParentVertex_retargets                            (body-329)
```

## Steps

1. `legSaturated_parent_edge_cases` — `Multiset.mem_add` on the parent's internal edges (`= touchedOuterForest.internalEdges
   + quotientEdgePreimage`, body-548 `recontract548_parent_internalEdges`).
2. `legSaturated_parent_insertedComponent_reachable` — two vertices of a touched component `A` are support-reachable in the
   parent: `A.forget` is support-connected (its own `isConnectedDivergent` field), `A.internalEdges ≤ parent.internalEdges`
   (single-le-sum + le_add_right), and reachability transports up the internal-edge inclusion.  NO new connectivity datum.
3. `legSaturated_parent_retarget_cases` — every vertex is either fixed by `retargetVertex` (`retargetVertex_of_not_mem`) or
   sits in a touched component `A` and retargets to `D.starOf G z.1.1 A` (`retargetVertex_eq_star_of_mem_element`).
4. **★load-bearing★** `legSaturated_parent_sameRetarget_reachable` — equal retarget image ⇒ support-reachable in the parent.
   Four cases (mirroring the flat `_sameRetarget_reachable`): non-star/non-star ⇒ `x = y`; mixed ⇒ `starOf_fresh`
   contradiction (`canonicalLegSaturatedStarFacts.starOf_fresh`); star/star ⇒ `starOf_injective` identifies the SAME owner
   component (SAME `D.starOf` allocator — no cross-ambient star equality), then Step 2 glues.
5. `legSaturated_parent_edgeStep` — a δ-adjacency `c—b` + a source-preimage of `c` yields a source-preimage of `b` reachable
   from it: the exact preimage edge (`quotientEdgePreimage_map`) is a parent `SupportAdj`, glued via Step 4.
6. `legSaturated_parent_reachable_lift` — `Relation.ReflTransGen` induction lifting a full δ-path, edge-step per adjacency.
7. **★target★** `canonicalLegSaturated_parent_isConnected` — both endpoints retarget into `δ.1.vertices`
   (`localizedParentVertex_retargets`); `touchedLocalComponent_isConnectedDivergent` gives δ support-connected; the path
   lifts (Step 6) and the endpoints glue (Step 4).

## Scoreboard

```text
canonicalLegSaturated_parent_isConnected   PROVED   (NO Parent input)   ⟹  Connected trunk of parentCD DERIVED
NEW TOPOLOGY                               ZERO     (flat blueprint re-keyed)
parentOnePI residual                       now BRIDGE-FREE ONLY (Connected discharged)
```

Note (record only, NOT consumed): the physics side `IsDivergenceReflectedByAdmissibleForestContract` is the likely home of
`parentDivergent` (quotient + divergent inserted forest ⇒ source parent divergent), i.e. `parentDivergent` may be a
migration residual of an existing typeclass, not a new axiom.  Next: 550 exact-edge erase connectivity / 551 promoted-edge
erase / 552 bridge-free assembly ⟹ parentOnePI.

Per the HALT/guards: NO `Parent` / round-trip / coassoc input; NO new structure/class/instance; NO hardcoded-star equality
(only the SAME selected `D.starOf` allocator is read); NO erase-aware path lift / `parentOnePI` / `parentDivergent`; the
physics `IsDivergenceReflectedByAdmissibleForestContract` instance is NOT consumed; no old private flat theorem is
publicized or modified; no facade, no `sorry`/`admit`.
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

/-- **R-6c-body-549 (mono) — support-reachability transports up an internal-edge inclusion.**  A faithful re-derivation of
the flat `supportReachable_mono_of_internalEdges_le` (the flat theorem is private; NEW TOPOLOGY = ZERO). -/
private theorem legSaturated_supportReachable_mono_of_internalEdges_le
    {H K : FeynmanGraph} (hle : H.internalEdges ≤ K.internalEdges)
    {u v : VertexId} (h : H.SupportReachable u v) : K.SupportReachable u v := by
  refine SimpleGraph.Reachable.mono ?_ h
  intro a b hab
  obtain ⟨hne, e, heH, hend⟩ := hab
  exact ⟨hne, e, Multiset.mem_of_le hle heH, hend⟩

/-! ## Step 1 — the parent internal-edge case split. -/

/-- **R-6c-body-549 — Step 1: parent internal-edge cases.**  Every parent internal edge is either a quotient-edge preimage
or a touched-forest internal edge (`Multiset.mem_add` on `recontract548_parent_internalEdges`). -/
theorem legSaturated_parent_edge_cases (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {e : ResolvedFeynmanEdge}
    (he : e ∈ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges) :
    e ∈ (touchedOuterForest z δ).internalEdges ∨
      e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) := by
  have he' : e ∈ (touchedOuterForest z δ).internalEdges
      + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) := he
  exact Multiset.mem_add.mp he'

/-! ## Step 2 — within-touched-component gluing (the resolved Helper 1). -/

/-- **R-6c-body-549 — Step 2: within-touched-component reachability.**  Two vertices of a touched component `A` are
support-reachable in the parent: `A.forget` is support-connected (its own component `isConnectedDivergent`), and `A`'s
internal edges sit inside the parent's, so reachability transports up. -/
theorem legSaturated_parent_insertedComponent_reachable (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {A : ResolvedFeynmanSubgraph G} (hA : A ∈ (touchedOuterForest z δ).elements)
    {u v : VertexId} (hu : u ∈ A.vertices) (hv : v ∈ A.vertices) :
    (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportReachable u v := by
  have hAcd : A.forget.IsConnectedDivergent := (touchedOuterForest z δ).isConnectedDivergent A hA
  have hAconn : A.forget.toFeynmanGraph.IsSupportConnected := hAcd.1
  have hreach : A.forget.toFeynmanGraph.SupportReachable u v := hAconn hu hv
  have hsub : A.internalEdges ≤ (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges := by
    show A.internalEdges ≤ (touchedOuterForest z δ).internalEdges
        + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ)
    exact le_trans (Finset.single_le_sum (fun i _ => Multiset.zero_le _) hA) (Multiset.le_add_right _ _)
  have hle : A.forget.toFeynmanGraph.internalEdges
      ≤ (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    exact Multiset.map_le_map hsub
  exact legSaturated_supportReachable_mono_of_internalEdges_le hle hreach

/-! ## Step 3 — the parent-vertex retarget classification. -/

/-- **R-6c-body-549 — Step 3: parent-vertex retarget classification.**  Each vertex is either fixed by the touched-forest
retarget, or sits in a touched component and retargets to that component's `D.starOf`. -/
theorem legSaturated_parent_retarget_cases (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    {v : VertexId} :
    ((touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v = v) ∨
      (∃ A ∈ (touchedOuterForest z δ).elements, v ∈ A.vertices ∧
        (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) v = D.starOf G z.1.1 A) := by
  by_cases hvt : v ∈ (touchedOuterForest z δ).vertices
  · rw [ResolvedAdmissibleSubgraph.mem_vertices] at hvt
    obtain ⟨A, hA, hvA⟩ := hvt
    exact Or.inr ⟨A, hA, hvA,
      retargetVertex_eq_star_of_mem_element (touchedOuterForest z δ) (D.starOf G z.1.1) hA hvA⟩
  · exact Or.inl (ResolvedAdmissibleSubgraph.retargetVertex_of_not_mem _ _ hvt)

/-! ## Step 4 — the same-retarget gluing (★load-bearing★). -/

/-- **R-6c-body-549 — Step 4 (★load-bearing★): same-retarget gluing.**  Two parent vertices with equal touched-forest
retarget image are support-reachable in the parent — either they coincide (both non-star), or lie in the same touched
component (equal stars ⇒ equal component by `starOf_injective` at the SAME `(G, z.1.1)` allocator), where Step 2 connects
them; the mixed non-star/star cases contradict `starOf_fresh`. -/
theorem legSaturated_parent_sameRetarget_reachable (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {x y : VertexId}
    (hx : x ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hy : y ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hret : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) x
          = (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) y) :
    (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportReachable x y := by
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
      exact legSaturated_parent_insertedComponent_reachable z δ datum hE hL hAx hxAx hyAy

/-! ## Step 5 — the single-edge lift. -/

/-- **R-6c-body-549 — Step 5: edge-step lift.**  A δ support-adjacency `c—b` + a source-preimage `wc` of `c` yields a
source-preimage `wb` of `b` reachable from `wc` in the parent, via the exact preimage edge (`quotientEdgePreimage_map`) as a
parent `SupportAdj` and Step 4 gluing. -/
theorem legSaturated_parent_edgeStep (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {c b : VertexId}
    (hadj : (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportAdj c b)
    {wc : VertexId}
    (hwc : wc ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hwcc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wc = c) :
    ∃ wb, wb ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) wb = b ∧
      (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportReachable wc wb := by
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
  have heEforget : eE.forget ∈
      (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.internalEdges := by
    simp only [FeynmanSubgraph.toFeynmanGraph_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges]
    exact Multiset.mem_map_of_mem _ heEPlus
  obtain ⟨hsE, htE⟩ := (localizedParentWithTouchedLegs z δ datum hE hL).edges_supported eE heEPlus
  have plusAdj : eE.source ≠ eE.target →
      (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportReachable
        eE.source eE.target :=
    fun hne => SimpleGraph.Adj.reachable
      (show (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportAdj
          eE.source eE.target from ⟨hne, eE.forget, heEforget, Or.inl ⟨rfl, rfl⟩⟩)
  rcases hend with ⟨hsc, htb⟩ | ⟨hsb, htc⟩
  · have hsEc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = c := hrs.trans hsc
    have htEb : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = b := hrt.trans htb
    have hne : eE.source ≠ eE.target := fun h =>
      hcb (hsEc.symm.trans ((congrArg _ h).trans htEb))
    exact ⟨eE.target, htE, htEb,
      (legSaturated_parent_sameRetarget_reachable Fstar z δ datum hE hL hwc hsE
        (hwcc.trans hsEc.symm)).trans (plusAdj hne)⟩
  · have hsEb : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.source = b := hrs.trans hsb
    have htEc : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) eE.target = c := hrt.trans htc
    have hne : eE.source ≠ eE.target := fun h =>
      hcb (htEc.symm.trans ((congrArg _ h.symm).trans hsEb))
    exact ⟨eE.source, hsE, hsEb,
      (legSaturated_parent_sameRetarget_reachable Fstar z δ datum hE hL hwc htE
        (hwcc.trans htEc.symm)).trans (plusAdj hne).symm⟩

/-! ## Step 6 — the full path lift. -/

/-- **R-6c-body-549 — Step 6: path lift.**  A full δ support-reachability path lifts to the parent: induction on the
reflexive-transitive support path, edge-step per adjacency. -/
theorem legSaturated_parent_reachable_lift (Fstar : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    {a b u : VertexId}
    (hu : u ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices)
    (hua : (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) u = a)
    (hab : (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportReachable a b) :
    ∃ w, w ∈ (localizedParentWithTouchedLegs z δ datum hE hL).vertices ∧
      (touchedOuterForest z δ).retargetVertex (D.starOf G z.1.1) w = b ∧
      (localizedParentWithTouchedLegs z δ datum hE hL).forget.toFeynmanGraph.SupportReachable u w := by
  have hrtg : Relation.ReflTransGen (touchedLocalComponent z δ).forget.toFeynmanGraph.SupportAdj a b :=
    (SimpleGraph.reachable_iff_reflTransGen _ _).1 hab
  clear hab
  induction hrtg with
  | refl => exact ⟨u, hu, hua, FeynmanGraph.SupportReachable.refl _ _⟩
  | tail _hac hcb IH =>
      obtain ⟨wc, hwc, hwcc, hreach⟩ := IH
      obtain ⟨wb, hwb, hwbb, hstepR⟩ :=
        legSaturated_parent_edgeStep Fstar z δ datum hE hL hcb hwc hwcc
      exact ⟨wb, hwb, hwbb, hreach.trans hstepR⟩

/-! ## Step 7 — the target: the canonical `W″` parent is support-connected. -/

/-- **R-6c-body-549 ∎ (★target★) — the canonical `W″` parent is support-connected**, with NO `Parent` input.  Both
endpoints retarget into `δ.1.vertices` (`localizedParentVertex_retargets`, 329); `touchedLocalComponent_isConnectedDivergent`
(322) gives δ support-connected; the path lifts (Step 6) and the endpoints glue (Step 4).  Discharges the Connected trunk of
body-548's `parentCD`. -/
theorem canonicalLegSaturated_parent_isConnected {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsConnected := by
  classical
  show ((localizedParentWithTouchedLegs z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z)).forget).IsConnected
  set datum := touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ) with hdatum
  set hE := liveAmbient_edges_supported ambientSupportOfW'' z with hEdef
  set hL := liveAmbient_legs_supported ambientSupportOfW'' z with hLdef
  intro u v hu hv
  have hu' : u ∈ (localizedParentWithTouchedLegs z δ.1 datum hE hL).vertices := hu
  have hv' : v ∈ (localizedParentWithTouchedLegs z δ.1 datum hE hL).vertices := hv
  -- the quotient component `δ.1` is connected-divergent (from `δ.2 : δ.1 ∈ forestDomain z`)
  have hδCD : δ.1.forget.IsConnectedDivergent :=
    z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1
  have hδconn : (touchedLocalComponent z δ.1).forget.toFeynmanGraph.IsSupportConnected :=
    (touchedLocalComponent_isConnectedDivergent z δ.1 hδCD).1
  -- both endpoints retarget into `δ.1.vertices = touchedLocalComponent.vertices`
  have hretu : (touchedOuterForest z δ.1).retargetVertex
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) u ∈ δ.1.vertices :=
    localizedParentVertex_retargets z δ.1 datum hE hL hu'
  have hretv : (touchedOuterForest z δ.1).retargetVertex
      (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) v ∈ δ.1.vertices :=
    localizedParentVertex_retargets z δ.1 datum hE hL hv'
  have hab : (touchedLocalComponent z δ.1).forget.toFeynmanGraph.SupportReachable
      ((touchedOuterForest z δ.1).retargetVertex
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) u)
      ((touchedOuterForest z δ.1).retargetVertex
        (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1) v) :=
    hδconn hretu hretv
  obtain ⟨w, hw, hwv, huw⟩ :=
    legSaturated_parent_reachable_lift canonicalLegSaturatedStarFacts z δ.1 datum hE hL hu' rfl hab
  exact huw.trans
    (legSaturated_parent_sameRetarget_reachable canonicalLegSaturatedStarFacts z δ.1 datum hE hL hw hv' hwv)

end GaugeGeometry.QFT.Combinatorial
