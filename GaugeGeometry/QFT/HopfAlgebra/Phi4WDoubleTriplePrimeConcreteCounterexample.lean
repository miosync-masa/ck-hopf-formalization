import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeCounterexample

/-!
# QFT-R1-body-653b — the CONCRETE marginal root-relative defect witness (Figure 1, realized)

Body-653a proved the GENERIC marginal criterion
`R.forget.IsDivergent ↔ hiddenRootBoundary γ δ = 0` (for a marginal inner `δ`) and the general
`W‴ ⊆ W″` inclusion, leaving the CONCRETE named 12-edge instance for this body.  Here we build ONE
concrete boundary-resolved φ⁴ graph and prove everything about it so that Figure 1 is a genuine Lean
witness: the incidence table, the exact hidden defect edges, the degree drop `0 → −2`, and the
root-relative divergence FAILURE all point at the SAME concrete object.

## The concrete graph (the 12-edge incidence table)

`VertexId := Nat`; inner vertices `{0,1,2}`, outer vertices `{3,4,5}`.  Twelve distinct-`edgeId`
internal edges (all sector `.hypercharge`), NO external legs:

```text
  inner triangle :  a01 (0–1) [id 0]   a12 (1–2) [id 1]   a20 (2–0) [id 2]
  outer triangle :  b34 (3–4) [id 3]   b45 (4–5) [id 4]   b53 (5–3) [id 5]
  visible cross  :  c04 (0–4) [id 6]   c15 (1–5) [id 7]   c25 (2–5) [id 8]   c23 (2–3) [id 9]
  hidden cross   :  h03 (0–3) [id 10]  h14 (1–4) [id 11]
```

Quartic incidence (every vertex valence 4):
`0:{a01,a20,c04,h03}  1:{a01,a12,c15,h14}  2:{a12,a20,c25,c23}  3:{b34,b53,c23,h03}
 4:{b34,b45,c04,h14}  5:{b45,b53,c15,c25}`.

* `phi4CarrierGapAmbient` `G` — all 12 edges, vertices `{0..5}`, no legs.
* `phi4CarrierGapOuter` `γ ⊆ G` — all six vertices, the 10 edges EXCEPT `h03,h14` (so `γ` omits exactly
  the two hidden root edges), no legs.
* `phi4CarrierGapInner` `δ ⊆ γ.boundaryCompletedResolvedGraph` — the inner triangle on `{0,1,2}`.

## Figure 1 (the caption, realized)

> A marginal inner triangle has four VISIBLE boundary edges (`c04,c15,c25,c23`) inside the W″ ambient,
> while two omitted root edges (`h03,h14`) remain INVISIBLE.  Root-relative reconstruction exposes six
> boundary edges, shifting the superficial degree from `0` to `−2`.  The W‴ edge-completeness condition
> excludes precisely this forest (`h03` has both endpoints inside `γ` but is not an internal edge of `γ`).

## Steps (this file = 653b-1)

1. Ambient `phi4CarrierGapAmbient`, named edge multisets `innerEdges / outerEdges / visibleCrossEdges /
   hiddenCrossEdges`, `G.internalEdges = innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges`.
2. Geometry: the two subgraphs `phi4CarrierGapOuter`, `phi4CarrierGapInner`; the (empty-leg) saturation
   certificates `hγsat`, `hδsat`.  The outer subgraph has NO resolved boundary edges (all vertices).
4. Exact boundary (`Multiset.ext`-free, `filter_add` + `filter_eq_nil` / `filter_eq_self`, NOT `decide`
   on the noncomputable Classical filters):
     * `phi4CarrierGap_delta_resolvedBoundaryEdges : δ.resolvedBoundaryEdges = visibleCrossEdges`;
     * `phi4CarrierGap_rootRelativeInner_resolvedBoundaryEdges :
        (rootRelativeInner γ δ).resolvedBoundaryEdges = visibleCrossEdges + hiddenCrossEdges`;
     * `phi4CarrierGap_hiddenRootBoundary : hiddenRootBoundary γ δ = hiddenCrossEdges` (EXACT Multiset,
        `{h03,h14}`, NOT card only), hence `card = 2` and `≠ 0`.
5. Four degrees: `ω(γ) = 4`, `ω(δ) = 0`, `ω(R) = −2` (the last via body-599's degree correction
   `phi4SuperficialDegree_rootRelativeInner_eq` + inner marginal `0` + exact hidden card `2`, NOT a
   recompute), and `phi4CarrierGap_root_not_divergent : ¬ (rootRelativeInner γ δ).forget.IsDivergent`
   (immediate from 653a `..._not_isDivergent_of_marginal_of_hiddenRootBoundary_ne`).

HEADLINE (this file): `phi4CarrierGap_marginal_contraction_failure`.

## HALT compliance / SPLIT NOTE (honest partial)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only; NO `Lean.ofReduceBool` — NO
`native_decide`).  ZERO forbidden divergence classes in ANY declaration type; Multiplicity-exact
(`Multiset`, `count_filter` / `filter_add`, no `Finset`/dedup — the exact `{h03,h14}` equality is kept,
never weakened to card).  No coproduct / body-556 / evaluation / symmetry factor; no `HEq` / `cast` /
graph-data `▸`; no ambient-transport CD; one file-local `local instance` (never global); ZERO new
`structure` / `class` / global `instance`; bodies ≤653a UNEDITED.

**SPLIT (653b-1 delivered; 653b-2 remains).**  This file is the topology-free half: the concrete graph +
subgraph geometry + trivial (empty-leg) saturation + exact defect + four degrees + root-not-divergent +
the self-contained headline `phi4CarrierGap_marginal_contraction_failure`.  The remaining 653b-2 (which
will import this file) owns: the singleton forests `A := ofElements {γ}`, `B := ofElements {δ}` and their
NATIVE topology (`outer`/`inner` support-connected + 1PI, proved from explicit reachability / bridge-free
witnesses — NOT one giant `decide`, and NOT ambient-transported), the ambient
`IsConnectedDivergentFor` gate, the two W″ memberships
(`phi4CarrierGap_outerForest_mem_wDoublePrime`, `phi4CarrierGap_innerForest_mem_wDoublePrime`), the fifth-
axis failure `phi4CarrierGap_outer_not_edgeComplete` (witness `h03`) hence
`phi4CarrierGap_outerForest_not_mem_wTriplePrime`, and the strictness headline
`exists_mem_wDoublePrime_not_mem_wTriplePrime`.  The split is on genuine volume: the outer subgraph's 1PI
certificate is a bridge-free proof over ten internal edges, each a reachability argument, which is
independent of everything delivered here.  Nothing here is faked to complete the split.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-- **body-653b — file-local φ⁴ divergence-measure family instance** (same value used throughout QFT-R1;
registered ONLY as a `local instance` in this file so `.IsDivergent` resolves to `phi4SuperficialDegree`
nonnegativity, never globally). -/
local instance instPhi4DivergenceMeasureFamily653b :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 1 — the concrete 12-edge ambient -/

/-- A boundary-resolved `.hypercharge` internal edge with the given `edgeId` and endpoints. -/
def phi4CarrierGapEdge (id s t : Nat) : ResolvedFeynmanEdge :=
  ⟨⟨id⟩, s, t, .hypercharge⟩

/-- The inner triangle edges `a01, a12, a20`. -/
def innerEdges : Multiset ResolvedFeynmanEdge :=
  {phi4CarrierGapEdge 0 0 1, phi4CarrierGapEdge 1 1 2, phi4CarrierGapEdge 2 2 0}

/-- The outer triangle edges `b34, b45, b53`. -/
def outerEdges : Multiset ResolvedFeynmanEdge :=
  {phi4CarrierGapEdge 3 3 4, phi4CarrierGapEdge 4 4 5, phi4CarrierGapEdge 5 5 3}

/-- The four visible cross edges `c04, c15, c25, c23`. -/
def visibleCrossEdges : Multiset ResolvedFeynmanEdge :=
  {phi4CarrierGapEdge 6 0 4, phi4CarrierGapEdge 7 1 5, phi4CarrierGapEdge 8 2 5, phi4CarrierGapEdge 9 2 3}

/-- The two hidden cross edges `h03, h14` — the root-crossing edges omitted by `γ`. -/
def hiddenCrossEdges : Multiset ResolvedFeynmanEdge :=
  {phi4CarrierGapEdge 10 0 3, phi4CarrierGapEdge 11 1 4}

/-- **body-653b (Step 1) — the concrete 12-edge boundary-resolved φ⁴ ambient graph** (Figure 1). -/
def phi4CarrierGapAmbient : ResolvedFeynmanGraph where
  vertices := {0, 1, 2, 3, 4, 5}
  internalEdges := innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges
  externalLegs := 0

/-! ## Step 2 — the outer / inner geometry -/

/-- **body-653b (Step 2) — the outer subgraph `γ`.**  All six vertices; the ten internal edges EXCEPT the
two hidden root edges `h03, h14`; no external legs. -/
def phi4CarrierGapOuter : ResolvedFeynmanSubgraph phi4CarrierGapAmbient where
  vertices := {0, 1, 2, 3, 4, 5}
  internalEdges := innerEdges + outerEdges + visibleCrossEdges
  externalLegs := 0
  vertices_subset := by decide
  internalEdges_le := by
    show innerEdges + outerEdges + visibleCrossEdges
        ≤ innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges
    exact Multiset.le_add_right _ _
  externalLegs_le := Multiset.zero_le _
  edges_supported := by
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  legs_supported := by intro ℓ h; simp at h

/-- **body-653b (Step 2) — the inner marginal triangle `δ`**, a subgraph of the boundary-completed outer
ambient `γ.boundaryCompletedResolvedGraph`.  Vertices `{0,1,2}`, the inner triangle edges, no legs. -/
def phi4CarrierGapInner :
    ResolvedFeynmanSubgraph phi4CarrierGapOuter.boundaryCompletedResolvedGraph where
  vertices := {0, 1, 2}
  internalEdges := innerEdges
  externalLegs := 0
  vertices_subset := by decide
  internalEdges_le := by
    show innerEdges ≤ innerEdges + outerEdges + visibleCrossEdges
    exact le_trans (Multiset.le_add_right innerEdges outerEdges)
      (Multiset.le_add_right _ visibleCrossEdges)
  externalLegs_le := Multiset.zero_le _
  edges_supported := by
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  legs_supported := by intro ℓ h; simp at h

/-- **body-653b (Step 2) — the outer subgraph has NO resolved boundary edges.**  It carries all six
vertices, so every ambient internal edge has both endpoints inside `γ.vertices` and the boundary
predicate fails.  Exact multiplicity (`= 0`). -/
theorem phi4CarrierGap_outer_resolvedBoundaryEdges :
    phi4CarrierGapOuter.resolvedBoundaryEdges = 0 := by
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
  rw [Multiset.filter_eq_nil]
  intro e he
  fin_cases he <;>
    · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4CarrierGapOuter
      decide

/-- **body-653b (Step 2) — outer external-leg saturation** (trivial: the ambient `G` has no external
legs, so the saturating filter is empty). -/
theorem phi4CarrierGap_outer_saturated :
    ResolvedExternalLegSaturated phi4CarrierGapAmbient phi4CarrierGapOuter := by
  unfold ResolvedExternalLegSaturated
  show (0 : Multiset ResolvedExternalLeg).filter _ ≤ _
  rw [Multiset.filter_zero]
  exact Multiset.zero_le _

/-- **body-653b (Step 2) — inner external-leg saturation** (trivial: the outer completion has empty
external legs, since `γ` has no legs AND no boundary edges). -/
theorem phi4CarrierGap_inner_saturated :
    ResolvedExternalLegSaturated phi4CarrierGapOuter.boundaryCompletedResolvedGraph
      phi4CarrierGapInner := by
  unfold ResolvedExternalLegSaturated
  rw [boundaryCompletedResolvedGraph_externalLegs]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [phi4CarrierGap_outer_resolvedBoundaryEdges, Multiset.map_zero, add_zero]
  show (Multiset.map _ (0 : Multiset ResolvedExternalLeg)).filter _ ≤ _
  rw [Multiset.map_zero, Multiset.filter_zero]
  exact Multiset.zero_le _

/-! ## Step 4 — the exact boundary multisets (`count_filter` / `filter_add`, NOT `decide`) -/

/-- **body-653b (Step 4) — the inner triangle's boundary edges are exactly the four visible cross
edges.**  Filter over `H.internalEdges = innerEdges + outerEdges + visibleCrossEdges`: the inner and outer
triangle edges keep both endpoints on the same side of `{0,1,2}`, only the visible cross edges straddle. -/
theorem phi4CarrierGap_delta_resolvedBoundaryEdges :
    phi4CarrierGapInner.resolvedBoundaryEdges = visibleCrossEdges := by
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
  show (innerEdges + outerEdges + visibleCrossEdges).filter
      phi4CarrierGapInner.resolvedIsBoundaryEdge = visibleCrossEdges
  rw [Multiset.filter_add, Multiset.filter_add]
  have hi : innerEdges.filter phi4CarrierGapInner.resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4CarrierGapInner; decide
  have ho : outerEdges.filter phi4CarrierGapInner.resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4CarrierGapInner; decide
  have hv : visibleCrossEdges.filter phi4CarrierGapInner.resolvedIsBoundaryEdge = visibleCrossEdges := by
    rw [Multiset.filter_eq_self]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4CarrierGapInner; decide
  rw [hi, ho, hv, zero_add, zero_add]

/-- **body-653b (Step 4) — the root lift's boundary edges are the six visible+hidden cross edges.**  The
root-relative lift is evaluated at ambient `G` (all 12 edges), so the two hidden cross edges become
boundary edges of `{0,1,2}` as well. -/
theorem phi4CarrierGap_rootRelativeInner_resolvedBoundaryEdges :
    (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedBoundaryEdges
      = visibleCrossEdges + hiddenCrossEdges := by
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
  show (innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges).filter
      (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedIsBoundaryEdge
      = visibleCrossEdges + hiddenCrossEdges
  rw [Multiset.filter_add, Multiset.filter_add, Multiset.filter_add]
  have hi : innerEdges.filter
      (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge rootRelativeInner phi4CarrierGapInner
        decide
  have ho : outerEdges.filter
      (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge rootRelativeInner phi4CarrierGapInner
        decide
  have hv : visibleCrossEdges.filter
      (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedIsBoundaryEdge
      = visibleCrossEdges := by
    rw [Multiset.filter_eq_self]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge rootRelativeInner phi4CarrierGapInner
        decide
  have hh : hiddenCrossEdges.filter
      (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).resolvedIsBoundaryEdge
      = hiddenCrossEdges := by
    rw [Multiset.filter_eq_self]; intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge rootRelativeInner phi4CarrierGapInner
        decide
  rw [hi, ho, hv, hh, zero_add, zero_add]

/-- **body-653b (Step 4) — the inherited outer boundary is empty** (the outer subgraph has no boundary
edges, so nothing is inherited). -/
theorem phi4CarrierGap_inheritedOuter :
    inheritedOuter phi4CarrierGapOuter phi4CarrierGapInner = 0 := by
  unfold inheritedOuter
  rw [phi4CarrierGap_outer_resolvedBoundaryEdges, Multiset.filter_zero]

/-- **body-653b (Step 4, EXACT DEFECT) — the hidden root boundary is exactly `{h03, h14}`.**  The fresh
root boundary `visibleCrossEdges + hiddenCrossEdges` minus `δ`'s own boundary `visibleCrossEdges` leaves
precisely the two omitted hidden cross edges.  EXACT Multiset equality — not weakened to card. -/
theorem phi4CarrierGap_hiddenRootBoundary :
    hiddenRootBoundary phi4CarrierGapOuter phi4CarrierGapInner = hiddenCrossEdges := by
  unfold hiddenRootBoundary newRootBoundary
  rw [phi4CarrierGap_rootRelativeInner_resolvedBoundaryEdges, phi4CarrierGap_inheritedOuter,
    tsub_zero, phi4CarrierGap_delta_resolvedBoundaryEdges, add_tsub_cancel_left]

/-- **body-653b (Step 4) — the hidden root boundary has exactly two edges.** -/
theorem phi4CarrierGap_hiddenRootBoundary_card :
    (hiddenRootBoundary phi4CarrierGapOuter phi4CarrierGapInner).card = 2 := by
  rw [phi4CarrierGap_hiddenRootBoundary]; rfl

/-- **body-653b (Step 4) — the hidden root boundary is nonempty.** -/
theorem phi4CarrierGap_hiddenRootBoundary_ne :
    hiddenRootBoundary phi4CarrierGapOuter phi4CarrierGapInner ≠ 0 := by
  rw [phi4CarrierGap_hiddenRootBoundary]; decide

/-! ## Step 5 — the four degrees + the root-relative divergence failure -/

/-- **body-653b (Step 5) — outer superficial degree `ω(γ) = 4`.**  No external legs and no boundary edges,
so `Eγ = 0` and `ωφ4 = 4 − 0`. -/
theorem phi4CarrierGap_outer_degree :
    phi4CarrierGapOuter.forget.phi4SuperficialDegree = 4 := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [resolvedSubgraph_physicalExternalLegCount_forget, phi4CarrierGap_outer_resolvedBoundaryEdges]
  show (4 : Int) - ((0 : Multiset ResolvedExternalLeg).card + (0 : Multiset ResolvedFeynmanEdge).card) = 4
  simp

/-- **body-653b (Step 5, MARGINAL) — inner superficial degree `ω(δ) = 0`.**  No external legs, four
visible boundary edges, so `Eδ = 4` and `ωφ4 = 4 − 4 = 0` — the logarithmically-divergent φ⁴ triangle. -/
theorem phi4CarrierGap_inner_degree :
    phi4CarrierGapInner.forget.phi4SuperficialDegree = 0 := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [resolvedSubgraph_physicalExternalLegCount_forget, phi4CarrierGap_delta_resolvedBoundaryEdges]
  show (4 : Int) - ((0 : Multiset ResolvedExternalLeg).card + visibleCrossEdges.card) = 0
  rw [show visibleCrossEdges.card = 4 from rfl]
  simp

/-- **body-653b (Step 5, DEGREE DROP) — root-relative superficial degree `ω(R) = −2`.**  From body-599's
UNCONDITIONAL degree correction `ω(R) = ω(δ) − |hiddenRootBoundary|` with `ω(δ) = 0` (marginal) and the
exact hidden card `2`: the two invisible root edges drop the marginal triangle two units below zero. -/
theorem phi4CarrierGap_root_degree :
    (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).forget.phi4SuperficialDegree = -2 := by
  rw [phi4SuperficialDegree_rootRelativeInner_eq phi4CarrierGapOuter phi4CarrierGapInner
      phi4CarrierGap_outer_saturated phi4CarrierGap_inner_saturated,
    phi4CarrierGap_inner_degree, phi4CarrierGap_hiddenRootBoundary]
  rw [show hiddenCrossEdges.card = 2 from rfl]
  decide

/-- **body-653b (Step 5, DEFECT) — the root-relative reconstruction of the marginal triangle is NOT
divergent.**  A marginal inner triangle inside an outer component that omits the two hidden root edges
reconstructs to a CONVERGENT root graph (`ω(R) = −2 < 0`).  Immediate from body-653a's generic marginal
defect criterion, the inner marginality `ω(δ) = 0`, and the nonempty hidden root boundary. -/
theorem phi4CarrierGap_root_not_divergent :
    ¬ (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).forget.IsDivergent :=
  rootRelativeInner_not_isDivergent_of_marginal_of_hiddenRootBoundary_ne
    phi4CarrierGapOuter phi4CarrierGapInner
    phi4CarrierGap_outer_saturated phi4CarrierGap_inner_saturated
    phi4CarrierGap_inner_degree phi4CarrierGap_hiddenRootBoundary_ne

/-! ## HEADLINE (653b-1) — the concrete marginal contraction failure -/

/-- **body-653b (HEADLINE, Figure 1 realized) — the concrete marginal contraction failure.**  On the
named 12-edge φ⁴ graph: the inner triangle is marginal (`ω = 0`), the hidden root boundary is EXACTLY the
two omitted cross edges `{h03, h14}`, and root-relative reconstruction is NOT divergent.  This is the
concrete instance realizing body-653a's generic criterion; the remaining W″/W‴ strictness witness is
653b-2. -/
theorem phi4CarrierGap_marginal_contraction_failure :
    phi4CarrierGapInner.forget.phi4SuperficialDegree = 0
      ∧ hiddenRootBoundary phi4CarrierGapOuter phi4CarrierGapInner = hiddenCrossEdges
      ∧ ¬ (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).forget.IsDivergent :=
  ⟨phi4CarrierGap_inner_degree, phi4CarrierGap_hiddenRootBoundary, phi4CarrierGap_root_not_divergent⟩

end GaugeGeometry.QFT.Combinatorial
