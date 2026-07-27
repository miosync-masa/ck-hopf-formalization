import GaugeGeometry.QFT.HopfAlgebra.DivergenceFamilyStrictGenerator
import GaugeGeometry.QFT.Combinatorial.BoundaryCompletedSubgraph

/-!
# QFT-R1-body-568 — boundary-completed φ⁴ left factor

Both screens onto the same `Phi4HopfGen`.  Body-566 built the right factor `[Γ/γ]`; body-567 built the
boundary-completed intrinsic graph.  This body lifts a connected-divergent subgraph `γ` to the **left**
tensor factor `[γ]` as the *same* `Phi4HopfGen`, using the boundary-completed graph as the representative —
so its class is `γ.boundaryCompletedGraph.toClass`, **not** the boundary-forgetting `γ.toFeynmanGraph.toClass`.

Because `boundaryCompletedGraph` shares `γ`'s vertices and internal edges (only the external legs change),
the support topology is unchanged (`Iff.rfl`); divergence is recovered from body-567's degree equality; and
no `IsAmbientInvariantDivergence` is used anywhere.

## Contents

* Step 1 `boundaryCompletedGraph_isSupportConnected_iff` / `_isOnePI_iff` — topology unchanged (`Iff.rfl`).
* Step 2 `boundaryCompletedGraph_self_isDivergent_iff` — divergence recovered from body-567 Step 6.
* Step 3 `boundaryCompletedGraph_exists_self_isConnectedDivergent` — graph-level CD (`∃`-form).
* Step 4 `FeynmanSubgraph.toPhi4HopfGen` — the left factor (value `= γ.boundaryCompletedGraph.toClass`).
* Step 5 `mapPerm_isConnectedDivergent_iff_of_family` (subgraph CD rename) + `toPhi4HopfGen_mapPerm`
  (the left `Quotient.lift` well-definedness certificate).

## Reaching ledger

```text
left boundary payload   CONSTRUCTED (567)
left topology           DERIVED, unchanged
left divergence         DERIVED from degree recovery
left Phi4HopfGen         CONSTRUCTED
left rename coherence   DERIVED
right Phi4HopfGen        CONSTRUCTED (566)
ambient invariance       ZERO on both sides
```

Per the HALT: no equality / `Equiv` / cast to the existing `HopfGen`; no `IsAmbientInvariantDivergence` and
no old Perm/Iso class; the left value is `γ.boundaryCompletedGraph.toClass`, never raw `γ.toFeynmanGraph.toClass`;
no coproduct / polynomial algebra / coassociativity; boundary completion and resolved traceability are not
conflated; no new `class`/`structure`/`instance`; topology is not re-proved — it is carried by the
vertices/internal-edges identity.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — topology is unchanged -/

/-- **R-6c-QFT-R1-body-568 — support-connectivity is unchanged by boundary completion** (`Iff.rfl`: same
vertices and internal edges). -/
theorem FeynmanSubgraph.boundaryCompletedGraph_isSupportConnected_iff (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.IsSupportConnected ↔ γ.IsConnected := Iff.rfl

/-- **R-6c-QFT-R1-body-568 — 1PI is unchanged by boundary completion** (`Iff.rfl`). -/
theorem FeynmanSubgraph.boundaryCompletedGraph_isOnePI_iff (γ : FeynmanSubgraph G) :
    γ.boundaryCompletedGraph.IsOnePI ↔ γ.IsOnePI := Iff.rfl

/-! ## Step 2 — divergence recovery -/

/-- **R-6c-QFT-R1-body-568 — divergence is recovered by boundary completion.**  The boundary-completed
graph's self-divergence (φ⁴) matches `γ`'s, lifting body-567's degree equality to nonnegativity.  No
`IsAmbientInvariantDivergence`. -/
theorem FeynmanSubgraph.boundaryCompletedGraph_self_isDivergent_iff (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent γ.boundaryCompletedGraph
        (phi4DivergenceMeasureFamily γ.boundaryCompletedGraph)
        (FeynmanSubgraph.self γ.boundaryCompletedGraph γ.boundaryCompletedGraph_wellFormed)
      ↔ @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G) γ := by
  show (0 : Int) ≤ (FeynmanSubgraph.self γ.boundaryCompletedGraph
      γ.boundaryCompletedGraph_wellFormed).phi4SuperficialDegree
    ↔ (0 : Int) ≤ γ.phi4SuperficialDegree
  rw [γ.phi4SuperficialDegree_self_boundaryCompletedGraph]

/-! ## Step 3 — graph-level CD assembly -/

/-- **R-6c-QFT-R1-body-568 — the boundary-completed graph is connected-divergent** (`∃`-form), from a
connected-divergent subgraph. -/
theorem FeynmanSubgraph.boundaryCompletedGraph_exists_self_isConnectedDivergent (γ : FeynmanSubgraph G)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ) :
    ∃ hWF : γ.boundaryCompletedGraph.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedGraph
        (phi4DivergenceMeasureFamily γ.boundaryCompletedGraph)
        (FeynmanSubgraph.self γ.boundaryCompletedGraph hWF) := by
  -- `.1/.2.1/.2.2` avoid the `IsConnectedDivergent.is*` accessors' `[DivergenceMeasure G]` synthesis
  -- (the φ⁴ measure is explicit, not an instance).
  refine ⟨γ.boundaryCompletedGraph_wellFormed, ?_, ?_, ?_⟩
  · exact (γ.boundaryCompletedGraph_isSupportConnected_iff).mpr hγCD.1
  · exact (γ.boundaryCompletedGraph_isOnePI_iff).mpr hγCD.2.1
  · exact (γ.boundaryCompletedGraph_self_isDivergent_iff).mpr hγCD.2.2

/-! ## Step 4 — the left factor -/

/-- **R-6c-QFT-R1-body-568 — the φ⁴ left factor `[γ]`.**  A connected-divergent subgraph maps to the same
`Phi4HopfGen` as the right factor, represented by its *boundary-completed* graph. -/
def FeynmanSubgraph.toPhi4HopfGen (γ : FeynmanSubgraph G)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ) :
    Phi4HopfGen :=
  γ.boundaryCompletedGraph.toHopfGenFor
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    (γ.boundaryCompletedGraph_exists_self_isConnectedDivergent hγCD)

/-- **R-6c-QFT-R1-body-568 — left-factor value.**  The class is `γ.boundaryCompletedGraph.toClass`
(`rfl`) — the boundary-completed representative, **not** raw `γ.toFeynmanGraph.toClass`. -/
@[simp] theorem FeynmanSubgraph.toPhi4HopfGen_val (γ : FeynmanSubgraph G)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ) :
    (γ.toPhi4HopfGen hγCD).val = γ.boundaryCompletedGraph.toClass := rfl

/-! ## Step 5 — rename certificate -/

/-- **R-6c-QFT-R1-body-568 — subgraph connected-divergence is rename-invariant for a coherent family.**
Topology via the existing `mapPerm` invariance (`(γ.mapPerm π).toFeynmanGraph = γ.toFeynmanGraph.mapPerm π`
by `rfl`); divergence via body-565. -/
theorem FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsConnectedDivergent (G.mapPerm π) (D (G.mapPerm π)) (γ.mapPerm π)
      ↔ @FeynmanSubgraph.IsConnectedDivergent G (D G) γ := by
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact FeynmanGraph.mapPerm_isSupportConnected_iff π γ.toFeynmanGraph
  · exact FeynmanGraph.mapPerm_isOnePI_iff π γ.toFeynmanGraph
  · exact FeynmanSubgraph.mapPerm_isDivergent_iff_of_family D Inv π γ

/-- **R-6c-QFT-R1-body-568 — the left `Quotient.lift` well-definedness certificate.**  Renaming `γ`
produces the same `Phi4HopfGen` left factor.  `Subtype.ext` on the underlying class + body-567's
`boundaryCompletedGraph_mapPerm` + `toClass` iso-invariance.  Iso class is not needed. -/
theorem FeynmanSubgraph.toPhi4HopfGen_mapPerm (γ : FeynmanSubgraph G) (π : Equiv.Perm VertexId)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ) :
    (γ.mapPerm π).toPhi4HopfGen
        ((FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family
          phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily π γ).mpr hγCD)
      = γ.toPhi4HopfGen hγCD := by
  apply Subtype.ext
  show (γ.mapPerm π).boundaryCompletedGraph.toClass = γ.boundaryCompletedGraph.toClass
  rw [γ.boundaryCompletedGraph_mapPerm π]
  exact ((FeynmanGraph.toClass_eq_iff γ.boundaryCompletedGraph
    (γ.boundaryCompletedGraph.mapPerm π)).mpr ⟨π, rfl⟩).symm

end GaugeGeometry.QFT.Combinatorial
