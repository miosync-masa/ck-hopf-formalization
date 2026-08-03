import GaugeGeometry.QFT.HopfAlgebra.Phi4BubbleWitnessGeometry
import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeTopology

/-!
# QFT-R2-body-665b — native topology + connected-divergent certificates for the bubble witness

Native topology + connected-divergent certificates for the bubble witness: the ambient φ⁴ vacuum graph
`phi4BubbleAmbient` (8 edges, 4 vertices `{0,1,2,3}`, valence-4, `L = 5`) is support-connected + 1PI +
divergent (`ω = 4`), and the one-loop four-point bubble subgraph `phi4BubbleInner` on `{0,1}` (edges
`{e0,e1}`) is connected-divergent (`ω = 0`, marginal).  Explicit reachability (no `native_decide`;
`SupportReachable` is NOT decidable over `VertexId = ℕ`, so reachability is built from explicit
`SimpleGraph.Adj.reachable` chains, never `decide` on connectivity/bridge-freeness).

Part 2/3 of the concrete non-vacuity witness: **665a** geometry (`Phi4BubbleWitnessGeometry`), **THIS 665b**
topology + CD certificates, **665c** the singleton admissible forest + W‴ membership + forest-sum ≠ 0 +
non-primitive coproduct.  Mirrors Figure-1's 653b-2a (`Phi4WDoubleTriplePrimeTopology`); its native engine
(`reachOfMem`/`connFromReach`/`estep`/`divOfDegree`) is `private`, so the analogues are REBUILT here for the
smaller, denser graph (4 vertices / 8 edges ambient; 2 vertices / 2 edges bubble).

## The mechanism (native, no `decide` shortcut on reachability)

* One-step support reachability comes from a single `SupportAdj` witness (`reachOfMem`/`bstep`/`estep`):
  produce the internal edge, discharge `u ≠ v` and the endpoint disjunction by `decide` (finite side-props),
  lift through `SimpleGraph.Adj.reachable`.
* Support-connectivity is packaged from hub-`0` spoke chains: `0 ↝ 1` via `e0`, `0 ↝ 2` via `e2`, `0 ↝ 3`
  via `e3` (`connFromReach4`); the bubble from `0 ↝ 1` via `e0` (`connFromReach2`).  Every pair routes
  through hub `0` via `.symm.trans`.
* 1PI is `∀ e ∈ internalEdges, ¬ IsBridge e`.  The ambient is 2-edge-connected: only the three spanning-tree
  spokes `e0,e2,e3` need rerouting — `e0(0–1)` reroutes `0↝1` via the parallel `e1`; `e2(0–2)` reroutes
  `0↝2` via `0–1–2` (`e0,e4`); `e3(0–3)` reroutes `0↝3` via `0–1–3` (`e0,e5`); every other erased edge
  leaves the tree intact.  The bubble's two parallel edges `e0,e1` reroute each other.

## HALT compliance / SPLIT NOTE

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
ZERO forbidden divergence classes in ANY declaration type; the topology is built natively, never transported
from an ambient class.  No `HEq` / `cast` / graph-data `▸`; no coproduct / evaluation / symmetry factor.
One file-local `local instance` (never global); ZERO new `structure` / `class` / global `instance`;
bodies ≤665a UNEDITED.

**SPLIT (665b delivered; 665c remains).**  This file is the topology-only half: the ambient
`IsConnectedDivergentFor` class package + the bubble forest-level `IsConnectedDivergent` certificate that
665c's singleton admissible forest will consume.  The admissible forest / W‴ membership / forest-sum /
non-primitive coproduct are NOT built here.  Nothing here is faked to complete the split.  **HALT.**
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-- **body-665b — file-local φ⁴ divergence-measure family instance** (same value as 665a / 653b-2a). -/
local instance instPhi4DivergenceMeasureFamily665b :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 0 — the reachability primitives (native, `decide`-free on `Reachable`) -/

/-- **body-665b — a single support-reachability step from an explicit internal edge.**  Lift a `SupportAdj`
witness through `SimpleGraph.Adj.reachable`; the only `decide` obligations are the finite side-props. -/
private theorem reachOfMem {H : FeynmanGraph} {Mf : Multiset FeynmanEdge}
    (hE : H.internalEdges = Mf) {u v : VertexId} (f : FeynmanEdge)
    (hmem : f ∈ Mf) (hne : u ≠ v)
    (hend : (f.source = u ∧ f.target = v) ∨ (f.source = v ∧ f.target = u)) :
    H.SupportReachable u v :=
  SimpleGraph.Adj.reachable (by
    rw [FeynmanGraph.toSimpleGraph_adj]
    exact ⟨hne, f, hE ▸ hmem, hend⟩)

/-- **body-665b — one base step**, citing a resolved edge of the concrete multiset `M`. -/
private theorem bstep {H : FeynmanGraph} {M : Multiset ResolvedFeynmanEdge}
    (hE : H.internalEdges = M.map ResolvedFeynmanEdge.forget) (u v : VertexId)
    (f : ResolvedFeynmanEdge) (hfB : f ∈ M) (hne : u ≠ v)
    (hend : (f.forget.source = u ∧ f.forget.target = v)
      ∨ (f.forget.source = v ∧ f.forget.target = u)) :
    H.SupportReachable u v :=
  reachOfMem hE f.forget (Multiset.mem_map_of_mem _ hfB) hne hend

/-- **body-665b — one erased step**, citing a resolved edge distinct from the erased flat edge `e`. -/
private theorem estep {H : FeynmanGraph} {M : Multiset ResolvedFeynmanEdge} {e : FeynmanEdge}
    (hE' : (H.eraseInternalEdge e).internalEdges = (M.map ResolvedFeynmanEdge.forget).erase e)
    (u v : VertexId) (f : ResolvedFeynmanEdge) (hfe : f.forget ≠ e) (hfB : f ∈ M) (hne : u ≠ v)
    (hend : (f.forget.source = u ∧ f.forget.target = v)
      ∨ (f.forget.source = v ∧ f.forget.target = u)) :
    (H.eraseInternalEdge e).SupportReachable u v :=
  reachOfMem hE' f.forget ((Multiset.mem_erase_of_ne hfe).mpr (Multiset.mem_map_of_mem _ hfB)) hne hend

/-- **body-665b — four-vertex support-connectivity from four hub chains.**  Route any pair through hub `0`. -/
private theorem connFromReach4 {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3} : Finset VertexId))
    (r0 : H.SupportReachable 0 0) (r1 : H.SupportReachable 0 1)
    (r2 : H.SupportReachable 0 2) (r3 : H.SupportReachable 0 3) :
    H.IsSupportConnected := by
  have hub : ∀ w ∈ ({0, 1, 2, 3} : Finset VertexId), H.SupportReachable 0 w := by
    intro w hw; fin_cases hw
    exacts [r0, r1, r2, r3]
  intro u v hu hv
  rw [hV] at hu hv
  exact (hub u hu).symm.trans (hub v hv)

/-- **body-665b — two-vertex support-connectivity from two hub chains.** -/
private theorem connFromReach2 {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1} : Finset VertexId))
    (r0 : H.SupportReachable 0 0) (r1 : H.SupportReachable 0 1) :
    H.IsSupportConnected := by
  have hub : ∀ w ∈ ({0, 1} : Finset VertexId), H.SupportReachable 0 w := by
    intro w hw; fin_cases hw
    exacts [r0, r1]
  intro u v hu hv
  rw [hV] at hu hv
  exact (hub u hu).symm.trans (hub v hv)

/-! ## Step 1a — the 8-edge ambient topology (generic in the carrier `H`) -/

/-- Abbreviation for the ambient resolved-edge multiset. -/
private def ambientEdges : Multiset ResolvedFeynmanEdge :=
  phi4BubbleBubbleEdges + phi4BubbleCrossEdges

/-- **body-665b — the 8-edge ambient support-connectivity** (hub `0` reaches `1,2,3` via `e0,e2,e3`). -/
private theorem eightEdge_supportConnected {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3} : Finset VertexId))
    (hE : H.internalEdges = ambientEdges.map ResolvedFeynmanEdge.forget) :
    H.IsSupportConnected :=
  connFromReach4 hV
    (FeynmanGraph.SupportReachable.refl _ _)
    (bstep hE 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide))
    (bstep hE 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide))
    (bstep hE 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide))

/-- **body-665b — the 8-edge ambient is 1PI.**  Support-connected, and no internal edge is a bridge: the
graph is 2-edge-connected, so only the three spanning-tree spokes `e0,e2,e3` need a rerouted hub chain. -/
private theorem eightEdge_onePI {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1, 2, 3} : Finset VertexId))
    (hE : H.internalEdges = ambientEdges.map ResolvedFeynmanEdge.forget) :
    H.IsOnePI := by
  refine ⟨eightEdge_supportConnected hV hE, ?_⟩
  intro e he
  rw [hE] at he
  obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
  rintro ⟨-, hbad⟩
  refine hbad ?_
  have hV' : (H.eraseInternalEdge er.forget).vertices = ({0, 1, 2, 3} : Finset VertexId) := by
    rw [FeynmanGraph.eraseInternalEdge_vertices, hV]
  have hE' : (H.eraseInternalEdge er.forget).internalEdges
      = (ambientEdges.map ResolvedFeynmanEdge.forget).erase er.forget := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, hE]
  fin_cases her
  · -- erase e0 (0–1): reroute r1 via the parallel e1 (same flat edge, multiplicity 2 survives the erase)
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (reachOfMem hE' (phi4BubbleEdge 1 0 1).forget (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e1 (0–1): reroute r1 via the parallel e0 (same flat edge, multiplicity 2 survives the erase)
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (reachOfMem hE' (phi4BubbleEdge 0 0 1).forget (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e2 (0–2): reroute r2 via 0–1–2 (e0, e4)
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 2 (phi4BubbleEdge 4 1 2) (by decide) (by decide) (by decide) (by decide)))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e3 (0–3): reroute r3 via 0–1–3 (e0, e5)
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      ((estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide)).trans
        (estep hE' 1 3 (phi4BubbleEdge 5 1 3) (by decide) (by decide) (by decide) (by decide)))
  · -- erase e4 (1–2): base tree intact
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e5 (1–3): base tree intact
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e6 (2–3): base tree intact
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))
  · -- erase e7 (2–3): base tree intact
    exact connFromReach4 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (estep hE' 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 2 (phi4BubbleEdge 2 0 2) (by decide) (by decide) (by decide) (by decide))
      (estep hE' 0 3 (phi4BubbleEdge 3 0 3) (by decide) (by decide) (by decide) (by decide))

/-! ## Step 1b — the 2-edge bubble topology (generic in `H`) -/

/-- **body-665b — the 2-edge bubble support-connectivity** (hub `0` reaches `1` via `e0`). -/
private theorem twoEdge_supportConnected {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1} : Finset VertexId))
    (hE : H.internalEdges = phi4BubbleBubbleEdges.map ResolvedFeynmanEdge.forget) :
    H.IsSupportConnected :=
  connFromReach2 hV
    (FeynmanGraph.SupportReachable.refl _ _)
    (bstep hE 0 1 (phi4BubbleEdge 0 0 1) (by decide) (by decide) (by decide))

/-- **body-665b — the 2-edge bubble is 1PI.**  The two parallel `0–1` edges reroute each other. -/
private theorem twoEdge_onePI {H : FeynmanGraph}
    (hV : H.vertices = ({0, 1} : Finset VertexId))
    (hE : H.internalEdges = phi4BubbleBubbleEdges.map ResolvedFeynmanEdge.forget) :
    H.IsOnePI := by
  refine ⟨twoEdge_supportConnected hV hE, ?_⟩
  intro e he
  rw [hE] at he
  obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
  rintro ⟨-, hbad⟩
  refine hbad ?_
  have hV' : (H.eraseInternalEdge er.forget).vertices = ({0, 1} : Finset VertexId) := by
    rw [FeynmanGraph.eraseInternalEdge_vertices, hV]
  have hE' : (H.eraseInternalEdge er.forget).internalEdges
      = (phi4BubbleBubbleEdges.map ResolvedFeynmanEdge.forget).erase er.forget := by
    rw [FeynmanGraph.eraseInternalEdge_internalEdges, hE]
  fin_cases her
  · -- erase e0 (0–1): reroute r1 via the parallel e1 (same flat edge, multiplicity 2 survives the erase)
    exact connFromReach2 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (reachOfMem hE' (phi4BubbleEdge 1 0 1).forget (by decide) (by decide) (by decide))
  · -- erase e1 (0–1): reroute r1 via the parallel e0 (same flat edge, multiplicity 2 survives the erase)
    exact connFromReach2 hV' (FeynmanGraph.SupportReachable.refl _ _)
      (reachOfMem hE' (phi4BubbleEdge 0 0 1).forget (by decide) (by decide) (by decide))

/-! ## Step 2 — divergence bridge -/

/-- **body-665b — φ⁴ divergence from a nonnegative superficial degree.** -/
private theorem divOfDegree {A : FeynmanGraph} (γ : FeynmanSubgraph A)
    (h : 0 ≤ γ.phi4SuperficialDegree) :
    @FeynmanSubgraph.IsDivergent A (phi4DivergenceMeasure A) γ :=
  (phi4_isDivergent_iff γ).mpr ((FeynmanSubgraph.phi4SuperficialDegree_nonneg_iff γ).mp h)

/-! ## Step 3 — the bubble boundary + degree (`ω = 0`, marginal) -/

/-- The four bubble boundary edges `e2,e3,e4,e5` — each straddles `{0,1}` (exactly one endpoint inside). -/
private def phi4BubbleBoundaryEdges : Multiset ResolvedFeynmanEdge :=
  {phi4BubbleEdge 2 0 2, phi4BubbleEdge 3 0 3, phi4BubbleEdge 4 1 2, phi4BubbleEdge 5 1 3}

/-- **body-665b — the bubble's boundary edges are exactly the four straddling cross edges `{e2,e3,e4,e5}`.**
The two bubble edges `e0,e1` keep both endpoints inside `{0,1}`; of the six cross edges only `e2,e3,e4,e5`
straddle (each with one endpoint in `{0,1}` and one in `{2,3}`), while `e6,e7` stay entirely in `{2,3}`. -/
theorem phi4BubbleInner_resolvedBoundaryEdges :
    phi4BubbleInner.resolvedBoundaryEdges = phi4BubbleBoundaryEdges := by
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
  show (phi4BubbleBubbleEdges + phi4BubbleCrossEdges).filter
      phi4BubbleInner.resolvedIsBoundaryEdge = phi4BubbleBoundaryEdges
  have hcross : phi4BubbleCrossEdges
      = phi4BubbleBoundaryEdges + {phi4BubbleEdge 6 2 3, phi4BubbleEdge 7 2 3} := rfl
  rw [hcross, Multiset.filter_add, Multiset.filter_add]
  have hb : phi4BubbleBubbleEdges.filter phi4BubbleInner.resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4BubbleInner; decide
  have hbd : phi4BubbleBoundaryEdges.filter phi4BubbleInner.resolvedIsBoundaryEdge
      = phi4BubbleBoundaryEdges := by
    rw [Multiset.filter_eq_self]
    intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4BubbleInner; decide
  have h67 : ({phi4BubbleEdge 6 2 3, phi4BubbleEdge 7 2 3} : Multiset ResolvedFeynmanEdge).filter
      phi4BubbleInner.resolvedIsBoundaryEdge = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    fin_cases he <;>
      · unfold ResolvedFeynmanSubgraph.resolvedIsBoundaryEdge phi4BubbleInner; decide
  rw [hb, hbd, h67, zero_add, add_zero]

/-- **body-665b (MARGINAL) — the bubble superficial degree `ω(δ) = 0`.**  No external legs, four boundary
edges, so `Eδ = 4` and `ωφ4 = 4 − 4 = 0` — the logarithmically-divergent φ⁴ four-point bubble. -/
theorem phi4BubbleInner_degree :
    phi4BubbleInner.forget.phi4SuperficialDegree = 0 := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [resolvedSubgraph_physicalExternalLegCount_forget, phi4BubbleInner_resolvedBoundaryEdges]
  show (4 : Int) - ((0 : Multiset ResolvedExternalLeg).card + phi4BubbleBoundaryEdges.card) = 0
  rw [show phi4BubbleBoundaryEdges.card = 4 from rfl]
  simp

/-! ## Step 4 — the packages: ambient class-CD + bubble forest-CD -/

/-- **body-665b — the ambient flat graph is well-formed.**  Mirrors
`phi4CarrierGapAmbient_forget_wellFormed`. -/
theorem phi4BubbleAmbient_forget_wellFormed : phi4BubbleAmbient.forget.WellFormed := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [ResolvedFeynmanGraph.forget_internalEdges] at he
    obtain ⟨er, her, rfl⟩ := Multiset.mem_map.mp he
    show er.forget.source ∈ phi4BubbleAmbient.forget.vertices
      ∧ er.forget.target ∈ phi4BubbleAmbient.forget.vertices
    fin_cases her <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    rw [ResolvedFeynmanGraph.forget_externalLegs] at hℓ
    simp only [show phi4BubbleAmbient.externalLegs = 0 from rfl, Multiset.map_zero] at hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-665b (PACKAGE) — the ambient is family connected-divergent (as a resolved class).**  The
self-subgraph of the flat ambient is support-connected, 1PI, and divergent (`ω = 4 ≥ 0`).  Mirrors
`phi4CarrierGapAmbient_isConnectedDivergentFor`. -/
theorem phi4BubbleAmbient_isConnectedDivergentFor :
    ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily phi4BubbleAmbient.toResolvedClass := by
  rw [ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass]
  refine ⟨phi4BubbleAmbient_forget_wellFormed, ?_, ?_, ?_⟩
  · exact eightEdge_supportConnected rfl rfl
  · exact eightEdge_onePI rfl rfl
  · have hcard : phi4BubbleAmbient.forget.externalLegs.card = 0 := by
      rw [ResolvedFeynmanGraph.forget_externalLegs, Multiset.card_map]; rfl
    exact divOfDegree _ (by
      rw [FeynmanSubgraph.phi4SuperficialDegree_self phi4BubbleAmbient_forget_wellFormed, hcard]
      norm_num)

/-- **body-665b (FOREST CD, the certificate 665c consumes) — the one-loop four-point bubble subgraph is
connected-divergent** (2-edge, marginal `ω = 0 ≥ 0`).  Mirrors
`phi4CarrierGapInner_forget_isConnectedDivergent`. -/
theorem phi4BubbleInner_forget_isConnectedDivergent :
    phi4BubbleInner.forget.IsConnectedDivergent := by
  refine ⟨?_, ?_, ?_⟩
  · exact twoEdge_supportConnected rfl rfl
  · exact twoEdge_onePI rfl rfl
  · exact divOfDegree _ (by rw [phi4BubbleInner_degree])

end GaugeGeometry.QFT.Combinatorial
