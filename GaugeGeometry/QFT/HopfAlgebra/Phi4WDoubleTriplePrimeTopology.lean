import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeConcreteCounterexample

/-!
# QFT-R1-body-653b-2a — the NATIVE topology of the concrete Figure-1 graphs

Body-653b-1 built the concrete 12-edge φ⁴ graph `phi4CarrierGapAmbient`, its outer subgraph
`phi4CarrierGapOuter` (10 edges, the two hidden root edges `h03,h14` omitted), the inner marginal
triangle `phi4CarrierGapInner`, and all their degree / hidden-defect facts.  Landing the two W″
memberships (653b-2b) requires the SUPPORT-CONNECTIVITY + 1PI + DIVERGENCE of these concrete graphs, and
those facts are *native topology*: they are proved by EXPLICIT reachability chains and per-edge bridge-free
witnesses — never by `decide` on `SimpleGraph.Reachable` (which is not decidable over `VertexId := Nat`),
never by `native_decide`, and never by ambient transport of an abstract divergence class.

This file (the sanctioned SPLIT half `653b-2a`) delivers exactly Step 1 of the plan: the three
`IsConnectedDivergentFor` packages (ambient self, boundary-completed-outer self) plus the two forest-level
`IsConnectedDivergent` facts (outer subgraph, inner subgraph) that the `ofElements` singleton forests will
consume.  The remaining Steps 2–5 (singleton forests, both W″ memberships, the fifth-axis `h03` failure,
and the strictness crown `exists_mem_wDoublePrime_not_mem_wTriplePrime`) are body-653b-2b, which imports
this file.

## The mechanism (native, no `decide` shortcut on reachability)

* One-step support reachability comes from a single `SupportAdj` witness: produce the internal edge,
  discharge `u ≠ v` and the endpoint disjunction by `decide` (finite side-props), and lift through
  `SimpleGraph.Adj.reachable` (`reachOfMem`).
* Support-connectivity of a six-vertex graph is packaged from six explicit `0 ↝ w` chains
  (`connFromReach`); of the inner triangle from three (`connFromReach3`).  Every `u,v` pair routes through
  the hub `0` via `.symm.trans`.
* 1PI is `∀ e ∈ internalEdges, ¬ IsBridge e`; each edge is erased and the erased graph is shown
  support-connected by a rerouted hub whose edges are cited from `Multiset.erase` via
  `mem_erase_of_ne` (`estep`).  The base graph is 2-edge-connected, so exactly one hub spoke ever needs
  rerouting per erased edge.

## HALT compliance / SPLIT NOTE

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
ZERO forbidden divergence classes in ANY declaration type; the topology is built natively, never
transported from an ambient class.  No `HEq` / `cast` / graph-data `▸`; no cross-ambient indexed-subgraph
equality; no coproduct / body-556 / evaluation.  One file-local `local instance` (never global); ZERO new
`structure` / `class` / global `instance`; bodies ≤653b-1 UNEDITED.

**SPLIT (653b-2a delivered; 653b-2b remains).**  The outer-graph 1PI certificate is a bridge-free proof
over ten internal edges, each an independent reachability argument, so the topology is isolated here and
the algebraic W″/W‴ strictness plumbing follows in 653b-2b.  Nothing here is faked to complete the split.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-- **body-653b-2a — file-local φ⁴ divergence-measure family instance** (same value as 653b-1). -/
local instance instPhi4DivergenceMeasureFamily653b2 :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 0 — the reachability primitives (native, `decide`-free on `Reachable`) -/

/-- **body-653b-2a — a single support-reachability step from an explicit internal edge.**  Given a flat
edge `f` in `H.internalEdges` with the two chosen endpoints, lift the `SupportAdj` witness through
`SimpleGraph.Adj.reachable`.  The only `decide` obligations at call sites are the finite side-props
`u ≠ v` and the endpoint disjunction — the reachability structure itself is built here explicitly. -/
private theorem reachOfMem {H : FeynmanGraph} {Mf : Multiset FeynmanEdge}
    (hE : H.internalEdges = Mf) {u v : VertexId} (f : FeynmanEdge)
    (hmem : f ∈ Mf) (hne : u ≠ v)
    (hend : (f.source = u ∧ f.target = v) ∨ (f.source = v ∧ f.target = u)) :
    H.SupportReachable u v :=
  SimpleGraph.Adj.reachable (by
    rw [FeynmanGraph.toSimpleGraph_adj]
    exact ⟨hne, f, hE ▸ hmem, hend⟩)

/-- **body-653b-2a — one base step**, citing a resolved edge of the concrete multiset `M`. -/
private theorem bstep {H : FeynmanGraph} {M : Multiset ResolvedFeynmanEdge}
    (hE : H.internalEdges = M.map ResolvedFeynmanEdge.forget) (u v : VertexId)
    (f : ResolvedFeynmanEdge) (hfB : f ∈ M) (hne : u ≠ v)
    (hend : (f.forget.source = u ∧ f.forget.target = v)
      ∨ (f.forget.source = v ∧ f.forget.target = u)) :
    H.SupportReachable u v :=
  reachOfMem hE f.forget (Multiset.mem_map_of_mem _ hfB) hne hend

/-- **body-653b-2a — one erased step**, citing a resolved edge distinct from the erased flat edge `e`. -/
private theorem estep {H : FeynmanGraph} {M : Multiset ResolvedFeynmanEdge} {e : FeynmanEdge}
    (hE' : (H.eraseInternalEdge e).internalEdges = (M.map ResolvedFeynmanEdge.forget).erase e)
    (u v : VertexId) (f : ResolvedFeynmanEdge) (hfe : f.forget ≠ e) (hfB : f ∈ M) (hne : u ≠ v)
    (hend : (f.forget.source = u ∧ f.forget.target = v)
      ∨ (f.forget.source = v ∧ f.forget.target = u)) :
    (H.eraseInternalEdge e).SupportReachable u v :=
  reachOfMem hE' f.forget ((Multiset.mem_erase_of_ne hfe).mpr (Multiset.mem_map_of_mem _ hfB)) hne hend

/-- **body-653b-2a — six-vertex support-connectivity from six hub chains.**  Given `0 ↝ w` for every
`w ∈ {0,…,5}`, route any pair through the hub. -/
private theorem connFromReach {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId))
    (r0 : H.SupportReachable 0 0) (r1 : H.SupportReachable 0 1)
    (r2 : H.SupportReachable 0 2) (r3 : H.SupportReachable 0 3)
    (r4 : H.SupportReachable 0 4) (r5 : H.SupportReachable 0 5) :
    H.IsSupportConnected := by
  have hub : ∀ w ∈ ({0, 1, 2, 3, 4, 5} : Finset VertexId), H.SupportReachable 0 w := by
    intro w hw; fin_cases hw
    exacts [r0, r1, r2, r3, r4, r5]
  intro u v hu hv
  rw [hV] at hu hv
  exact (hub u hu).symm.trans (hub v hv)

/-- **body-653b-2a — three-vertex support-connectivity from three hub chains.** -/
private theorem connFromReach3 {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2} : Finset VertexId))
    (r0 : H.SupportReachable 0 0) (r1 : H.SupportReachable 0 1)
    (r2 : H.SupportReachable 0 2) :
    H.IsSupportConnected := by
  have hub : ∀ w ∈ ({0, 1, 2} : Finset VertexId), H.SupportReachable 0 w := by
    intro w hw; fin_cases hw
    exacts [r0, r1, r2]
  intro u v hu hv
  rw [hV] at hu hv
  exact (hub u hu).symm.trans (hub v hv)

/-! ## Step 1a — the 12-edge ambient topology (generic in the carrier `H`) -/

/-- Abbreviation for the ambient resolved-edge multiset. -/
private def ambientEdges : Multiset ResolvedFeynmanEdge :=
  innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges

/-- **body-653b-2a — the 12-edge ambient support-connectivity** (0 reaches all six vertices directly or
through the visible/inner edges). -/
private theorem twelveEdge_supportConnected {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId))
    (hE : H.internalEdges = ambientEdges.map ResolvedFeynmanEdge.forget) :
    H.IsSupportConnected :=
  connFromReach hV
    (FeynmanGraph.SupportReachable.refl _ _)
    (bstep hE 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide))
    (bstep hE 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide))
    (bstep hE 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide))
    (bstep hE 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide))
    ((bstep hE 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide)).trans
      (bstep hE 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide)))

/-- **body-653b-2a — the 12-edge ambient is 1PI.**  Support-connected, and no internal edge is a bridge:
each erased graph is reconnected by rerouting the (at most one) broken hub spoke. -/
private theorem twelveEdge_onePI {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId))
    (hE : H.internalEdges = ambientEdges.map ResolvedFeynmanEdge.forget) :
    H.IsOnePI := by
  refine ⟨twelveEdge_supportConnected hV hE, ?_⟩
  intro e he
  rw [hE] at he
  obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
  rintro ⟨-, hbad⟩
  refine hbad ?_
  have hV' : (H.eraseInternalEdge er.forget).vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId) := by
    rw [FeynmanGraph.eraseInternalEdge_vertices, hV]
  have hE' : (H.eraseInternalEdge er.forget).internalEdges
      = (ambientEdges.map ResolvedFeynmanEdge.forget).erase er.forget := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, hE]
  -- standard hub spokes (used verbatim whenever the erased edge is off the spanning tree)
  fin_cases her
  · -- erase a01 (0–1): reroute r1 via 0–2–1
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 1 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase a12 (1–2): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase a20 (2–0): reroute r2 via 0–1–2
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 2 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b34 (3–4): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b45 (4–5): reroute r5 via 0–1–5
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 5 (phi4CarrierGapEdge 7 1 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b53 (5–3): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c04 (0–4): reroute r4 via 0–3–4 and r5 via 0–3–4–5
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 3 4 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide)))
      (((estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 3 4 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide))).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c15 (1–5): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c25 (2–5): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c23 (2–3): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase h03 (0–3): reroute r3 via 0–2–3
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase h14 (1–4): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4CarrierGapEdge 10 0 3) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))

/-! ## Step 1b — the 10-edge outer / boundary-completed topology (generic in `H`) -/

/-- Abbreviation for the outer (10-edge, no hidden) resolved-edge multiset. -/
private def outerEdgesM : Multiset ResolvedFeynmanEdge :=
  innerEdges + outerEdges + visibleCrossEdges

/-- **body-653b-2a — the 10-edge outer support-connectivity.**  Same hub as the ambient except vertex `3`
is reached via `0–2–3` (`h03` is absent). -/
private theorem tenEdge_supportConnected {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId))
    (hE : H.internalEdges = outerEdgesM.map ResolvedFeynmanEdge.forget) :
    H.IsSupportConnected :=
  connFromReach hV
    (FeynmanGraph.SupportReachable.refl _ _)
    (bstep hE 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide))
    (bstep hE 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide))
    ((bstep hE 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide)).trans
      (bstep hE 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide)))
    (bstep hE 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide))
    ((bstep hE 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide)).trans
      (bstep hE 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide)))

/-- **body-653b-2a — the 10-edge outer graph is 1PI.** -/
private theorem tenEdge_onePI {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId))
    (hE : H.internalEdges = outerEdgesM.map ResolvedFeynmanEdge.forget) :
    H.IsOnePI := by
  refine ⟨tenEdge_supportConnected hV hE, ?_⟩
  intro e he
  rw [hE] at he
  obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
  rintro ⟨-, hbad⟩
  refine hbad ?_
  have hV' : (H.eraseInternalEdge er.forget).vertices = ({0, 1, 2, 3, 4, 5} : Finset VertexId) := by
    rw [FeynmanGraph.eraseInternalEdge_vertices, hV]
  have hE' : (H.eraseInternalEdge er.forget).internalEdges
      = (outerEdgesM.map ResolvedFeynmanEdge.forget).erase er.forget := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, hE]
  fin_cases her
  · -- erase a01 (0–1): reroute r1 via 0–2–1
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 1 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase a12 (1–2): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase a20 (2–0): reroute r2 via 0–1–2 and r3 via 0–4–3
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 2 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 3 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b34 (3–4): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b45 (4–5): reroute r5 via 0–1–5
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 5 (phi4CarrierGapEdge 7 1 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase b53 (5–3): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c04 (0–4): reroute r4 via 0–2–3–4 and r5 via 0–2–3–4–5
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide))).trans
        (estep hE' 3 4 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide)))
      ((((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide))).trans
        (estep hE' 3 4 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide))).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c15 (1–5): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c25 (2–5): base tree intact
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 3 (phi4CarrierGapEdge 9 2 3) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))
  · -- erase c23 (2–3): reroute r3 via 0–4–3
    exact connFromReach hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 3 (phi4CarrierGapEdge 3 3 4) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 4 (phi4CarrierGapEdge 6 0 4) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 4 5 (phi4CarrierGapEdge 4 4 5) (by decide) (by decide) (by decide) (by decide)))

/-! ## Step 1c — the 3-edge inner triangle topology (generic in `H`) -/

/-- **body-653b-2a — the inner triangle support-connectivity.** -/
private theorem threeEdge_supportConnected {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2} : Finset VertexId))
    (hE : H.internalEdges = innerEdges.map ResolvedFeynmanEdge.forget) :
    H.IsSupportConnected :=
  connFromReach3 hV
    (FeynmanGraph.SupportReachable.refl _ _)
    (bstep hE 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide))
    (bstep hE 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide))

/-- **body-653b-2a — the inner triangle is 1PI.** -/
private theorem threeEdge_onePI {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2} : Finset VertexId))
    (hE : H.internalEdges = innerEdges.map ResolvedFeynmanEdge.forget) :
    H.IsOnePI := by
  refine ⟨threeEdge_supportConnected hV hE, ?_⟩
  intro e he
  rw [hE] at he
  obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
  rintro ⟨-, hbad⟩
  refine hbad ?_
  have hV' : (H.eraseInternalEdge er.forget).vertices = ({0, 1, 2} : Finset VertexId) := by
    rw [FeynmanGraph.eraseInternalEdge_vertices, hV]
  have hE' : (H.eraseInternalEdge er.forget).internalEdges
      = (innerEdges.map ResolvedFeynmanEdge.forget).erase er.forget := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, hE]
  fin_cases her
  · -- erase a01 (0–1): reroute r1 via 0–2–1
    exact connFromReach3 hV' (FeynmanGraph.SupportReachable.refl _ _)
      ((estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 2 1 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
  · -- erase a12 (1–2): base tree intact
    exact connFromReach3 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4CarrierGapEdge 2 2 0) (by decide) (by decide) (by decide) (by decide))
  · -- erase a20 (2–0): reroute r2 via 0–1–2
    exact connFromReach3 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4CarrierGapEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 2 (phi4CarrierGapEdge 1 1 2) (by decide) (by decide) (by decide) (by decide)))

/-! ## Step 2 — divergence bridge -/

/-- **body-653b-2a — φ⁴ divergence from a nonnegative superficial degree.** -/
private theorem divOfDegree {A : FeynmanGraph} (γ : FeynmanSubgraph A)
    (h : 0 ≤ γ.phi4SuperficialDegree) :
    @FeynmanSubgraph.IsDivergent A (phi4DivergenceMeasure A) γ :=
  (phi4_isDivergent_iff γ).mpr ((FeynmanSubgraph.phi4SuperficialDegree_nonneg_iff γ).mp h)

/-! ## Step 3 — the three `IsConnectedDivergentFor` packages + two forest `IsConnectedDivergent` facts -/

/-- **body-653b-2a — the ambient flat graph is well-formed.** -/
theorem phi4CarrierGapAmbient_forget_wellFormed : phi4CarrierGapAmbient.forget.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [ResolvedFeynmanGraph.forget_internalEdges] at he
    obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
    show er.forget.source ∈ phi4CarrierGapAmbient.forget.vertices
      ∧ er.forget.target ∈ phi4CarrierGapAmbient.forget.vertices
    fin_cases her <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    rw [ResolvedFeynmanGraph.forget_externalLegs] at hℓ
    simp only [show phi4CarrierGapAmbient.externalLegs = 0 from rfl, Multiset.map_zero] at hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-653b-2a (PACKAGE 1) — the ambient is family connected-divergent (as a resolved class).**
The self-subgraph of the flat ambient is support-connected, 1PI, and divergent (`ω = 4 ≥ 0`). -/
theorem phi4CarrierGapAmbient_isConnectedDivergentFor :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily phi4CarrierGapAmbient.toResolvedClass := by
  rw [ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass]
  refine ⟨phi4CarrierGapAmbient_forget_wellFormed, ?_, ?_, ?_⟩
  · exact twelveEdge_supportConnected rfl rfl
  · exact twelveEdge_onePI rfl rfl
  · have hcard : phi4CarrierGapAmbient.forget.externalLegs.card = 0 := by
      rw [ResolvedFeynmanGraph.forget_externalLegs, Multiset.card_map]; rfl
    exact divOfDegree _ (by
      rw [FeynmanSubgraph.phi4SuperficialDegree_self phi4CarrierGapAmbient_forget_wellFormed, hcard]
      norm_num)

/-- **body-653b-2a (FOREST CD 1) — the outer subgraph is connected-divergent** (10-edge, `ω = 4`). -/
theorem phi4CarrierGapOuter_forget_isConnectedDivergent :
    phi4CarrierGapOuter.forget.IsConnectedDivergent := by
  refine ⟨?_, ?_, ?_⟩
  · exact tenEdge_supportConnected rfl rfl
  · exact tenEdge_onePI rfl rfl
  · exact divOfDegree _ (by rw [phi4CarrierGap_outer_degree]; decide)

/-- **body-653b-2a (FOREST CD 2) — the inner triangle is connected-divergent** (3-edge, marginal
`ω = 0 ≥ 0`). -/
theorem phi4CarrierGapInner_forget_isConnectedDivergent :
    phi4CarrierGapInner.forget.IsConnectedDivergent := by
  refine ⟨?_, ?_, ?_⟩
  · exact threeEdge_supportConnected rfl rfl
  · exact threeEdge_onePI rfl rfl
  · exact divOfDegree _ (by rw [phi4CarrierGap_inner_degree])

/-- **body-653b-2a — the boundary-completed outer graph has empty external legs** (outer has no legs and
no boundary edges). -/
theorem phi4CarrierGapOuter_boundaryCompletedResolvedExternalLegs :
    phi4CarrierGapOuter.boundaryCompletedResolvedExternalLegs = 0 := by
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [show phi4CarrierGapOuter.externalLegs = 0 from rfl, phi4CarrierGap_outer_resolvedBoundaryEdges,
    Multiset.map_zero, Multiset.map_zero, add_zero]

/-- **body-653b-2a — the boundary-completed outer flat graph is well-formed.** -/
theorem phi4CarrierGapOuter_boundaryCompleted_forget_wellFormed :
    phi4CarrierGapOuter.boundaryCompletedResolvedGraph.forget.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [ResolvedFeynmanGraph.forget_internalEdges, boundaryCompletedResolvedGraph_internalEdges] at he
    obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
    show er.forget.source ∈ phi4CarrierGapOuter.boundaryCompletedResolvedGraph.forget.vertices
      ∧ er.forget.target ∈ phi4CarrierGapOuter.boundaryCompletedResolvedGraph.forget.vertices
    fin_cases her <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    rw [ResolvedFeynmanGraph.forget_externalLegs, boundaryCompletedResolvedGraph_externalLegs,
      phi4CarrierGapOuter_boundaryCompletedResolvedExternalLegs, Multiset.map_zero] at hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-653b-2a (PACKAGE 2) — the boundary-completed outer graph is family connected-divergent** (the
ambient for the inner forest's W″ membership).  Its self-subgraph is the 10-edge outer topology with empty
legs, so `ω = 4 ≥ 0`. -/
theorem phi4CarrierGapOuter_boundaryCompleted_isConnectedDivergentFor :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily
      phi4CarrierGapOuter.boundaryCompletedResolvedGraph.toResolvedClass := by
  rw [ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass]
  refine ⟨phi4CarrierGapOuter_boundaryCompleted_forget_wellFormed, ?_, ?_, ?_⟩
  · exact tenEdge_supportConnected rfl rfl
  · exact tenEdge_onePI rfl rfl
  · have hcard : phi4CarrierGapOuter.boundaryCompletedResolvedGraph.forget.externalLegs.card = 0 := by
      rw [ResolvedFeynmanGraph.forget_externalLegs, Multiset.card_map,
        boundaryCompletedResolvedGraph_externalLegs,
        phi4CarrierGapOuter_boundaryCompletedResolvedExternalLegs]
      rfl
    exact divOfDegree _ (by
      rw [FeynmanSubgraph.phi4SuperficialDegree_self
        phi4CarrierGapOuter_boundaryCompleted_forget_wellFormed, hcard]
      norm_num)

end GaugeGeometry.QFT.Combinatorial
