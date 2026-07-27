import GaugeGeometry.QFT.Combinatorial.Phi4DivergenceMeasure
import GaugeGeometry.QFT.Combinatorial.Permutation

/-!
# QFT-R1-body-564 — φ⁴ boundary permutation invariance + measure-family scope audit

Just before inhabiting `IsPermInvariantDivergence`, a **third scope trap** appears.  The class field

```text
degree_mapPerm : ∀ π [DivergenceMeasure (G.mapPerm π)] γ, degree (γ.mapPerm π) = degree γ
```

re-quantifies the *target* `DivergenceMeasure (G.mapPerm π)` as an **arbitrary** instance.  So fixing the
source to the φ⁴ measure still demands `degree[any target measure] (γ.mapPerm π) = degree[φ⁴] γ`, which is
stronger than the genuine rename coherence of one φ⁴ family.  What is actually true — and what this body
banks — is the two-point naturality of the **same** explicit measure family:

```text
degree[phi4DivergenceMeasure (G.mapPerm π)] (γ.mapPerm π) = degree[phi4DivergenceMeasure G] γ.
```

So body-564 fabricates no instance; it fully banks the rename geometry (boundary equivariance, exact
transport) and the family-level degree equality, then records the class scope precisely.

## Contents

* Step 1 `mapPerm_isBoundaryEdge_iff` — boundary predicate equivariance (via `π` injective + image mem).
* Step 2 `mapPerm_complementEdges` — **exact** (count-preserving) complement-edge transport.
* Step 3 `mapPerm_boundaryEdges` — **exact** boundary-edge transport (the load-bearing step).
* Step 4 `mapPerm_boundaryEdgeCount` / `mapPerm_physicalExternalLegCount` — numerical corollaries.
* Step 5 `mapPerm_phi4SuperficialDegree` — φ⁴ degree rename invariance.
* Step 6 `phi4DivergenceMeasure_degree_mapPerm` + `phi4_mapPerm_isDivergent_iff` — the explicit
  measure-family equality, plus a thin adapter to the current field shape under a coherence hypothesis.

## Class scope verdict (Step 7)

```text
PROVED     : coherence of the explicit φ⁴ measure family under mapPerm.
NOT YET INHABITED : IsPermInvariantDivergence.
REASON     : its target DivergenceMeasure binder is re-quantified independently, rather than
             selected from the same coherent family.
```

Per the HALT: no global/scoped/local permanent instance; the target measure is **not** identified with the
φ⁴ measure by proof irrelevance (`DivergenceMeasure` is a structure, not a `Prop` — no instance
uniqueness); iso invariance is not entered; body-562/563 are not edited; no coproduct / right-factor
specialization is wired; boundary completion is not entered; the boundary transport is exact
(count-preserving), never membership-only; ZERO new `class`/`structure`/`instance`; no HopfAlgebra import.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-- **Auxiliary (no injectivity needed).**  `map` commutes with truncated subtraction when the subtrahend
is `≤` the minuend — `(A - B).map f = A.map f - B.map f`. -/
private theorem multiset_map_sub_of_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {A B : Multiset α} (hBA : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  calc
    (A - B).map f = ((A - B).map f + B.map f) - B.map f := by
      rw [Multiset.add_sub_cancel_right]
    _ = ((A - B + B).map f) - B.map f := by rw [Multiset.map_add]
    _ = A.map f - B.map f := by rw [Multiset.sub_add_cancel hBA]

/-! ## Step 1 — boundary predicate equivariance -/

/-- **R-6c-QFT-R1-body-564 — boundary predicate is `mapPerm`-equivariant.**  An edge is a boundary edge of
the renamed subgraph (at the renamed edge) iff it was one of the original. -/
theorem FeynmanSubgraph.mapPerm_isBoundaryEdge_iff (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) (e : FeynmanEdge) :
    (γ.mapPerm π).IsBoundaryEdge (e.map π) ↔ γ.IsBoundaryEdge e := by
  unfold FeynmanSubgraph.IsBoundaryEdge
  simp only [FeynmanSubgraph.mapPerm_vertices, FeynmanEdge.map_source, FeynmanEdge.map_target,
    π.injective.mem_finset_image]

/-! ## Step 2 — exact complement-edge transport -/

/-- **R-6c-QFT-R1-body-564 — complement edges transport exactly under `mapPerm`.**  Count-preserving
multiset equality, not merely a membership iff. -/
theorem FeynmanSubgraph.mapPerm_complementEdges (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).complementEdges = γ.complementEdges.map (FeynmanEdge.map π) := by
  unfold FeynmanSubgraph.complementEdges
  rw [FeynmanGraph.mapPerm_internalEdges, FeynmanSubgraph.mapPerm_internalEdges,
    multiset_map_sub_of_le (FeynmanEdge.map π) γ.internalEdges_le]

/-! ## Step 3 — exact boundary-edge transport (load-bearing) -/

/-- **R-6c-QFT-R1-body-564 — boundary edges transport exactly under `mapPerm`.**  Combines the exact
complement transport (Step 2) with `filter`/`map` commutation and the boundary predicate equivariance
(Step 1).  This is the heart of the body. -/
theorem FeynmanSubgraph.mapPerm_boundaryEdges (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).boundaryEdges = γ.boundaryEdges.map (FeynmanEdge.map π) := by
  unfold FeynmanSubgraph.boundaryEdges
  rw [FeynmanSubgraph.mapPerm_complementEdges, Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro e _
  exact FeynmanSubgraph.mapPerm_isBoundaryEdge_iff π γ e

/-! ## Step 4 — numerical corollaries -/

@[simp] theorem FeynmanSubgraph.mapPerm_boundaryEdgeCount (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).boundaryEdgeCount = γ.boundaryEdgeCount := by
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [FeynmanSubgraph.mapPerm_boundaryEdges, Multiset.card_map]

@[simp] theorem FeynmanSubgraph.mapPerm_physicalExternalLegCount (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).physicalExternalLegCount = γ.physicalExternalLegCount := by
  unfold FeynmanSubgraph.physicalExternalLegCount
  rw [FeynmanSubgraph.mapPerm_externalLegCount, FeynmanSubgraph.mapPerm_boundaryEdgeCount]

/-! ## Step 5 — φ⁴ degree rename invariance -/

@[simp] theorem FeynmanSubgraph.mapPerm_phi4SuperficialDegree (π : Equiv.Perm VertexId)
    (γ : FeynmanSubgraph G) :
    (γ.mapPerm π).phi4SuperficialDegree = γ.phi4SuperficialDegree := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [FeynmanSubgraph.mapPerm_physicalExternalLegCount]

/-! ## Step 6 — explicit measure-family equality -/

/-- **R-6c-QFT-R1-body-564 — φ⁴ family rename naturality.**  The two-point equality of the explicit φ⁴
measure family: `degree[φ⁴ on G.mapPerm π] (γ.mapPerm π) = degree[φ⁴ on G] γ`.  No instance inference —
both measures are named explicitly. -/
theorem phi4DivergenceMeasure_degree_mapPerm (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    @DivergenceMeasure.degree (G.mapPerm π) (phi4DivergenceMeasure (G.mapPerm π)) (γ.mapPerm π)
      = @DivergenceMeasure.degree G (phi4DivergenceMeasure G) γ := by
  rw [phi4DivergenceMeasure_degree, phi4DivergenceMeasure_degree]
  exact FeynmanSubgraph.mapPerm_phi4SuperficialDegree π γ

/-- **R-6c-QFT-R1-body-564 — φ⁴ divergence is rename-invariant (explicit family).** -/
theorem phi4_mapPerm_isDivergent_iff (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G) :
    @FeynmanSubgraph.IsDivergent (G.mapPerm π) (phi4DivergenceMeasure (G.mapPerm π)) (γ.mapPerm π)
      ↔ @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasure G) γ := by
  rw [phi4_isDivergent_iff, phi4_isDivergent_iff, FeynmanSubgraph.mapPerm_physicalExternalLegCount]

/-- **R-6c-QFT-R1-body-564 — thin adapter to the current class-field shape.**  Under the *hypothesis* that
the target measure is the φ⁴ family member on `G.mapPerm π` (coherence — NOT proof irrelevance, since
`DivergenceMeasure` is a structure), the field-shaped equality `degree[target] (γ.mapPerm π) = degree[φ⁴] γ`
follows.  This is what a coherent-family interface (a future parallel to `IsPermInvariantDivergence`) would
consume; the current class instead re-quantifies the target independently. -/
theorem phi4_degree_mapPerm_of_target_measure_eq (π : Equiv.Perm VertexId) (γ : FeynmanSubgraph G)
    (inst : DivergenceMeasure (G.mapPerm π)) (hinst : inst = phi4DivergenceMeasure (G.mapPerm π)) :
    @DivergenceMeasure.degree (G.mapPerm π) inst (γ.mapPerm π)
      = @DivergenceMeasure.degree G (phi4DivergenceMeasure G) γ := by
  subst hinst
  exact phi4DivergenceMeasure_degree_mapPerm π γ

end GaugeGeometry.QFT.Combinatorial
