import GaugeGeometry.QFT.HopfAlgebra.Phi4StableNestedBoundaryCoherence
import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoassocSplitChoice
import GaugeGeometry.QFT.Combinatorial.Phi4ExternalValence

/-!
# QFT-R1-body-599 — root-relative CD correction audit + gated split-choice landing

Body-597 built the *stable* nested boundary completion `rootRelativeInner γ δ` (`= R`) and proved the
raw graph equality with the single root completion of `R`.  This body audits what that lift does to the
**φ⁴ superficial degree of divergence**, and lands a HONESTLY GATED connected-divergent transport.

## The hidden root boundary

The nested boundary edges split (body-597) as
`R.resolvedBoundaryEdges = inheritedOuter γ δ + newRootBoundary γ δ`.  The inherited half re-absorbs into
`δ.externalLegs`; the fresh half `newRootBoundary` is the newly-cut root boundary.  But `δ`'s OWN boundary
edges `δ.resolvedBoundaryEdges` (computed inside the boundary-completed ambient
`H = γ.boundaryCompletedResolvedGraph`) are a SUB-multiset of `newRootBoundary`, and the residual

```text
hiddenRootBoundary γ δ := newRootBoundary γ δ - δ.resolvedBoundaryEdges
```

is exactly the set of root-crossing edges that `δ` cannot see from inside `H`.  These are the edges the
nested completion silently adds.

## The load-bearing UNCONDITIONAL result (Step 2)

```text
ωφ4(R.forget) = ωφ4(δ.forget) − |hiddenRootBoundary γ δ|
```

i.e. every hidden root-boundary edge lowers the φ⁴ superficial degree by exactly one.  This is a pure
combinatorial identity — no gate, no divergence-class assumption, no CD transport.

## The honest transport GATE (Steps 3–4)

CD transport `δ divergent → R divergent` is **only** legitimate under the boundary-closed gate
`RootRelativeBoundaryClosed γ δ := hiddenRootBoundary γ δ = 0` (equivalently, by Step 5, iff the degree is
preserved).  Transporting divergence WITHOUT this gate would revive the body-562 rejected false
ambient-invariance, so it is forbidden.  Under the gate the two degrees coincide and connected /
1PI / divergent all transport (connectivity + 1PI are `induced`-structure predicates that only read
`vertices`/`internalEdges` — which are shared verbatim between `R.forget` and `δ.forget` — so they move
definitionally; divergence moves through the gated degree equality).

## The Step-5 VERDICT — branch 2 (big win)

Unconditional closure is **NOT** derivable from W″ membership alone: there genuinely exist hidden
root-boundary edges whenever the inner forest does not saturate every root-crossing edge, and W″
membership only forces external-leg saturation of `δ` inside `H`, never the disappearance of the hidden
root boundary.  We therefore do NOT fabricate a derivation.  Instead:

* the split-choice-level gate `Phi4StableSplitChoiceBoundaryClosed` isolates a genuinely NEW
  edge-completeness / hidden-boundary-zero axis (the fourth-emptying-axis analogue at root coordinates);
* the UNCONDITIONAL load-bearing result is the Step-2 degree correction
  `phi4SuperficialDegree_rootRelativeInner_eq`;
* the gated landing `phi4StableSplitChoice_rootRelativeInner_isConnectedDivergent` DERIVES the outer
  saturation from `s.outer_mem` (via `mem_resolvedLegSaturatedIndexFor`) and consumes the inner
  saturation + inner component CD supplied by the live inner membership.

Per the HALT: axiom-clean; ZERO forbidden divergence classes in any type; NO unconditional CD transport
(all gated by `RootRelativeBoundaryClosed`); no `selectedOuter` / `promotedOf` / forest_block / alpha /
coassoc construction; no `induced` assumption; only `DivergenceMeasureFamily` /
`PermInvariantDivergenceMeasureFamily D` / the concrete φ⁴ families appear as divergence binders.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the hidden root-boundary residual -/

/-- **body-599 (Step 1) — the hidden root boundary.**  The freshly-cut root boundary edges of `R` that `δ`
cannot see from inside the boundary-completed ambient `H = γ.boundaryCompletedResolvedGraph`.  Multiplicity
exact (`Multiset` difference). -/
noncomputable def hiddenRootBoundary (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Multiset ResolvedFeynmanEdge :=
  newRootBoundary γ δ - δ.resolvedBoundaryEdges

/-- **body-599 (Step 1) — `δ`'s own boundary edges sit inside the freshly-cut root boundary.**  Count-level:
`inheritedOuter` and `δ.resolvedBoundaryEdges` have disjoint support (an inherited edge is a `γ`-boundary
edge, hence NOT in `γ.internalEdges`, while a `δ`-boundary edge IS), and each is individually `≤` the root
boundary of `R`; so their sum is `≤ R.resolvedBoundaryEdges`, and `le_tsub_of_add_le_left` lands the claim. -/
theorem resolvedBoundaryEdges_le_newRootBoundary (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    δ.resolvedBoundaryEdges ≤ newRootBoundary γ δ := by
  have hδR : δ.resolvedBoundaryEdges ≤ (rootRelativeInner γ δ).resolvedBoundaryEdges := by
    have h1 : δ.resolvedBoundaryEdges
        = γ.internalEdges.filter (rootRelativeInner γ δ).resolvedIsBoundaryEdge := by
      show γ.internalEdges.filter δ.resolvedIsBoundaryEdge
          = γ.internalEdges.filter (rootRelativeInner γ δ).resolvedIsBoundaryEdge
      exact Multiset.filter_congr (fun _ _ => Iff.rfl)
    rw [h1]
    exact Multiset.filter_le_filter _ γ.internalEdges_le
  unfold newRootBoundary
  apply le_tsub_of_add_le_left
  rw [Multiset.le_iff_count]
  intro e
  rw [Multiset.count_add]
  have ha : Multiset.count e (inheritedOuter γ δ)
      ≤ Multiset.count e (rootRelativeInner γ δ).resolvedBoundaryEdges :=
    Multiset.count_le_of_le e (inheritedOuter_le_R_resolvedBoundaryEdges γ δ)
  have hb : Multiset.count e δ.resolvedBoundaryEdges
      ≤ Multiset.count e (rootRelativeInner γ δ).resolvedBoundaryEdges :=
    Multiset.count_le_of_le e hδR
  have hdisj : Multiset.count e (inheritedOuter γ δ) = 0
      ∨ Multiset.count e δ.resolvedBoundaryEdges = 0 := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    have he1 : e ∈ inheritedOuter γ δ := Multiset.count_pos.mp (Nat.pos_of_ne_zero h1)
    have he2 : e ∈ δ.resolvedBoundaryEdges := Multiset.count_pos.mp (Nat.pos_of_ne_zero h2)
    have hein : e ∈ γ.internalEdges := (resolvedBoundaryEdges_mem.mp he2).1
    obtain ⟨hs, ht⟩ := γ.edges_supported e hein
    have hbe : γ.resolvedIsBoundaryEdge e := by
      unfold inheritedOuter at he1
      exact (resolvedBoundaryEdges_mem.mp (Multiset.mem_filter.mp he1).1).2
    rcases hbe with ⟨_, hout⟩ | ⟨hout, _⟩
    · exact hout ht
    · exact hout hs
  omega

/-- **body-599 (Step 1) — the fresh root boundary decomposes as `δ`'s boundary plus the hidden residual.** -/
theorem newRootBoundary_eq_add_hidden (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    newRootBoundary γ δ = δ.resolvedBoundaryEdges + hiddenRootBoundary γ δ := by
  unfold hiddenRootBoundary
  exact (add_tsub_cancel_of_le (resolvedBoundaryEdges_le_newRootBoundary γ δ)).symm

/-! ## Step 2 — the valence / degree correction (LOAD-BEARING, UNCONDITIONAL) -/

/-- **body-599 (Step 2) — the physical external valence of a resolved subgraph's forget.**  `Eγ` counts the
forgotten external legs plus the forgotten boundary edges; the latter are `resolvedBoundaryEdges` via the
body-589 forget compatibility.  Card-exact. -/
theorem resolvedSubgraph_physicalExternalLegCount_forget {H : ResolvedFeynmanGraph}
    (η : ResolvedFeynmanSubgraph H) :
    η.forget.physicalExternalLegCount = η.externalLegs.card + η.resolvedBoundaryEdges.card := by
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
    FeynmanSubgraph.boundaryEdgeCount
  rw [ResolvedFeynmanSubgraph.forget_externalLegs, Multiset.card_map,
    ← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map]

/-- **body-599 (Step 2) — physical valence of `R.forget`.** -/
theorem physicalExternalLegCount_rootRelativeInner_forget (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (rootRelativeInner γ δ).forget.physicalExternalLegCount
      = (rootRelativeInner γ δ).externalLegs.card + (rootRelativeInner γ δ).resolvedBoundaryEdges.card :=
  resolvedSubgraph_physicalExternalLegCount_forget (rootRelativeInner γ δ)

/-- **body-599 (Step 2) — physical valence of `δ.forget`.** -/
theorem physicalExternalLegCount_delta_forget (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    δ.forget.physicalExternalLegCount = δ.externalLegs.card + δ.resolvedBoundaryEdges.card :=
  resolvedSubgraph_physicalExternalLegCount_forget δ

/-- **body-599 (Step 2, HEADLINE valence) — the nested lift adds exactly the hidden root boundary.**  Under
both saturation hypotheses, the physical external valence of `R.forget` exceeds that of `δ.forget` by the
size of the hidden root boundary.  Collected from the body-597 leg decomposition + the Step-1 split +
`omega`; no gate. -/
theorem physicalExternalLegCount_rootRelativeInner_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    (rootRelativeInner γ δ).forget.physicalExternalLegCount
      = δ.forget.physicalExternalLegCount + (hiddenRootBoundary γ δ).card := by
  have hR := physicalExternalLegCount_rootRelativeInner_forget γ δ
  have hδ := physicalExternalLegCount_delta_forget γ δ
  have hA : δ.externalLegs.card
      = (rootRelativeInner γ δ).externalLegs.card + (inheritedOuter γ δ).card := by
    rw [rootRelativeInner_externalLegs, rootRelativeInner_externalLegs_decomp γ δ hγsat hδsat,
      Multiset.card_add, Multiset.card_map, Multiset.card_map]
  have hB : (rootRelativeInner γ δ).resolvedBoundaryEdges.card
      = (inheritedOuter γ δ).card + (newRootBoundary γ δ).card := by
    have hsplit : (rootRelativeInner γ δ).resolvedBoundaryEdges
        = inheritedOuter γ δ + newRootBoundary γ δ := by
      unfold newRootBoundary
      rw [add_tsub_cancel_of_le (inheritedOuter_le_R_resolvedBoundaryEdges γ δ)]
    rw [hsplit, Multiset.card_add]
  have hC : (newRootBoundary γ δ).card
      = δ.resolvedBoundaryEdges.card + (hiddenRootBoundary γ δ).card := by
    rw [newRootBoundary_eq_add_hidden γ δ, Multiset.card_add]
  rw [hR, hδ]
  omega

/-- **body-599 (Step 2, HEADLINE degree) — the unconditional φ⁴ degree correction.**  Each hidden
root-boundary edge lowers the φ⁴ superficial degree by exactly one:
`ωφ4(R.forget) = ωφ4(δ.forget) − |hiddenRootBoundary γ δ|`.  This is the load-bearing UNCONDITIONAL
identity — no divergence-class assumption, no gate. -/
theorem phi4SuperficialDegree_rootRelativeInner_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    (rootRelativeInner γ δ).forget.phi4SuperficialDegree
      = δ.forget.phi4SuperficialDegree - ((hiddenRootBoundary γ δ).card : Int) := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [physicalExternalLegCount_rootRelativeInner_eq γ δ hγsat hδsat]
  push_cast
  ring

/-! ## Step 3 — the honest transport gate -/

/-- **body-599 (Step 3) — the boundary-closed gate.**  The nested lift is boundary-closed when it adds NO
hidden root-boundary edge.  All CD transport below is gated by this predicate; ungated CD transport is
forbidden (it would revive the body-562 rejected false ambient-invariance).  A bare `Prop`, no divergence
class. -/
def RootRelativeBoundaryClosed (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) : Prop :=
  hiddenRootBoundary γ δ = 0

/-- **body-599 (Step 3) — boundary-closed iff the fresh root boundary is exactly `δ`'s boundary.** -/
theorem rootRelativeBoundaryClosed_iff (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    RootRelativeBoundaryClosed γ δ ↔ newRootBoundary γ δ = δ.resolvedBoundaryEdges := by
  unfold RootRelativeBoundaryClosed
  constructor
  · intro h
    rw [newRootBoundary_eq_add_hidden γ δ, h, add_zero]
  · intro h
    have hEq : δ.resolvedBoundaryEdges + hiddenRootBoundary γ δ = δ.resolvedBoundaryEdges + 0 := by
      rw [add_zero, ← newRootBoundary_eq_add_hidden γ δ, h]
    exact add_left_cancel hEq

/-- **body-599 (Step 3) — connectivity transports from `δ.forget` to `R.forget`.**  `IsConnected` reads only
`vertices` / `internalEdges` (through the induced support graph), and `R.forget` and `δ.forget` share those
verbatim, so the predicate moves definitionally. -/
theorem rootRelativeInner_forget_isConnected_of_delta (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (h : δ.forget.IsConnected) : (rootRelativeInner γ δ).forget.IsConnected := h

/-- **body-599 (Step 3) — 1PI transports from `δ.forget` to `R.forget`.**  `IsOnePI` reads only
`vertices` / `internalEdges` (support-connectivity + bridge-freeness), shared verbatim, so definitional. -/
theorem rootRelativeInner_forget_isOnePI_of_delta (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (h : δ.forget.IsOnePI) : (rootRelativeInner γ δ).forget.IsOnePI := h

/-- **body-599 (Step 3) — GATED divergence transport.**  Under the boundary-closed gate the hidden root
boundary is empty, so the Step-2 degree correction collapses to `ωφ4(R.forget) = ωφ4(δ.forget)`, and
`δ`-divergence transports to `R`-divergence.  WITHOUT the gate this is forbidden. -/
theorem rootRelativeInner_forget_isDivergent_of_closed (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hclosed : RootRelativeBoundaryClosed γ δ)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hδdiv : @FeynmanSubgraph.IsDivergent γ.boundaryCompletedResolvedGraph.forget
      (phi4DivergenceMeasureFamily _) δ.forget) :
    @FeynmanSubgraph.IsDivergent G.forget (phi4DivergenceMeasureFamily _)
      (rootRelativeInner γ δ).forget := by
  have hcard : ((hiddenRootBoundary γ δ).card : Int) = 0 := by
    unfold RootRelativeBoundaryClosed at hclosed
    rw [hclosed]; simp
  have hdeg := phi4SuperficialDegree_rootRelativeInner_eq γ δ hγsat hδsat
  rw [hcard, sub_zero] at hdeg
  have hδdeg : (0 : Int) ≤ δ.forget.phi4SuperficialDegree := hδdiv
  show (0 : Int) ≤ (rootRelativeInner γ δ).forget.phi4SuperficialDegree
  rw [hdeg]; exact hδdeg

/-- **body-599 (Step 3, HEADLINE) — GATED connected-divergent transport.**  Connectivity and 1PI move
definitionally; divergence moves through the gate.  Assembles the full `IsConnectedDivergent` on
`R.forget` from `δ.forget`'s, under the boundary-closed gate. -/
theorem rootRelativeInner_forget_isConnectedDivergent_of_closed (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hclosed : RootRelativeBoundaryClosed γ δ)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hδCD : @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
      (phi4DivergenceMeasureFamily _) δ.forget) :
    @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily _)
      (rootRelativeInner γ δ).forget :=
  ⟨rootRelativeInner_forget_isConnected_of_delta γ δ hδCD.1,
   rootRelativeInner_forget_isOnePI_of_delta γ δ hδCD.2.1,
   rootRelativeInner_forget_isDivergent_of_closed γ δ hclosed hγsat hδsat hδCD.2.2⟩

/-! ## Step 4 — split-choice landing gate -/

/-- **body-599 (Step 4) — the split-choice-level boundary-closed gate.**  For every outer component `γ` of
the filtered split choice and every externally-leg-saturated inner `δ` on the boundary-completed ambient,
the nested lift is boundary-closed.  A bare `Prop` carrying NO forbidden divergence class.

This is the FALLBACK design of the spec (direct quantification over `(γ, δ)` with the inner saturation as a
binder), chosen over the `ForestIdx`→`elements` navigation because the split-choice `.choice` legs index
the inner forest through a `Sum` + `phi4LocalChoiceCarrier` layer whose component-`δ` accessor is not a
clean single step; the direct form keeps the gate a transparent edge-completeness axis without dismantling
any live membership. -/
def Phi4StableSplitChoiceBoundaryClosed (s : Phi4FilteredCoassocSplitChoice G) : Prop :=
  ∀ (γ : ResolvedFeynmanSubgraph G),
    γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer →
    ∀ (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph),
      ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ →
      RootRelativeBoundaryClosed γ δ

/-- **body-599 (Step 4, HEADLINE landing) — the gated split-choice CD landing.**  Under the split-choice
boundary-closed gate, for every outer component `γ` (whose external-leg saturation is DERIVED from
`s.outer_mem` via the W″ membership criterion) and every saturated inner `δ` carrying its own component CD
(supplied by the live inner membership), the nested root lift `R = rootRelativeInner γ δ` is connected
divergent on `G.forget`.  The gate does the CD transport; nothing is fabricated. -/
theorem phi4StableSplitChoice_rootRelativeInner_isConnectedDivergent
    (s : Phi4FilteredCoassocSplitChoice G)
    (hclosed : Phi4StableSplitChoiceBoundaryClosed s)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer)
    {δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph}
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hδCD : @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
      (phi4DivergenceMeasureFamily _) δ.forget) :
    @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily _)
      (rootRelativeInner γ δ).forget := by
  have hγsat : ResolvedExternalLegSaturated G γ := by
    have hmem : s.outer ∈ resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily G := s.outer_mem
    exact ((mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G s.outer).mp hmem).2.2.2.2.2 γ hγ
  exact rootRelativeInner_forget_isConnectedDivergent_of_closed γ δ
    (hclosed γ hγ δ hδsat) hγsat hδsat hδCD

/-! ## Step 5 — the two-way verdict (branch 2)

The gate is NOT idle bookkeeping: `RootRelativeBoundaryClosed γ δ` is EXACTLY the condition that the nested
lift preserves the φ⁴ superficial degree.  Unconditional closure is genuinely absent from W″ membership
(which only forces external-leg saturation of `δ` inside `H`, not the vanishing of the hidden root
boundary), so the gate isolates a new axis rather than recording a theorem — the branch-2 "big win". -/

/-- **body-599 (Step 5, VERDICT) — the gate is exactly degree preservation.**  `RootRelativeBoundaryClosed γ
δ` holds iff the nested lift preserves the φ⁴ superficial degree.  This is the honest characterization: the
gate is not a hidden extra assumption but precisely the degree-correction axis of Step 2 set to zero. -/
theorem rootRelativeBoundaryClosed_iff_degree_eq (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ) :
    RootRelativeBoundaryClosed γ δ ↔
      (rootRelativeInner γ δ).forget.phi4SuperficialDegree = δ.forget.phi4SuperficialDegree := by
  rw [phi4SuperficialDegree_rootRelativeInner_eq γ δ hγsat hδsat]
  unfold RootRelativeBoundaryClosed
  constructor
  · intro h; rw [h]; simp
  · intro h
    rw [sub_eq_self] at h
    have hc : (hiddenRootBoundary γ δ).card = 0 := by exact_mod_cast h
    exact Multiset.card_eq_zero.mp hc

end GaugeGeometry.QFT.Combinatorial
