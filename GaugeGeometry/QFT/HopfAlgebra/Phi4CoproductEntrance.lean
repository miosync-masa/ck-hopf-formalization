import GaugeGeometry.QFT.HopfAlgebra.Phi4LeftFactor

/-!
# QFT-R1-body-569 — family-indexed φ⁴ coproduct entrance

The old coproduct had three fixed points: the index predicate (via an old `DivergenceMeasure` instance),
the factor constructors (via the old `HopfGen`), and the class lift (via old representative ownership).
This body re-issues the first two in the family-indexed φ⁴ world and assembles the coproduct **at the
representative level**.  The class lift stays for the next body.

## Contents

* Step 1 `properConnectedDivergentSubgraphsFor` — the family-indexed finite index (`Fintype` is
  bookkeeping; zero `DivergenceMeasure` instance binders) + accessors + `phi4…` specialization.
* Step 2 `mapPerm_mem_properConnectedDivergentSubgraphsFor_iff` — the index rename certificate (for the
  next body's `Finset.sum_bij`).
* Step 3 `HopfHFor` / `Phi4HopfH` / `phi4Gen` — the polynomial carrier (no bridge to old `HopfH`).
* Step 4 `FeynmanGraph.toPhi4HopfGen` — the ambient generator (value `= G.toClass`).
* Step 5 `phi4ConnectedStrictSummand` — the connected summand `[γ] ⊗ [Γ/γ]` (left = body-568
  boundary-completed factor, right = body-566 direct quotient factor).
* Step 6 `coproductGen_phi4` — the representative-level coproduct formula.

## Reaching

```text
family finite index         CONSTRUCTED
Phi4HopfH                   CONSTRUCTED
ambient generator           CONSTRUCTED
left/right summand          WIRED
representative coproduct    CONSTRUCTED
representative independence OPEN   (next body)
class lift / aeval          OPEN
forest coproduct            NOT ENTERED
```

Per the HALT: no return to the old `HopfH` / old generator constructors; no `IsAmbientInvariantDivergence`
/ preservation / old Perm/Iso divergence classes; no `Quotient.lift` / `MvPolynomial.aeval`; no coproduct
algebra hom or coassociativity; no admissible forest / W″; no new `class`/`structure`/`instance`; the only
explicit physics root is the φ⁴ family; `Fintype (FeynmanSubgraph …)` is infrastructure, not physics.
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-- A subgraph with `0 < internalEdges.card` is nonempty (an edge pins its endpoints inside the vertex
set).  Replicated here to avoid importing the old coproduct layer. -/
private theorem isNonempty_of_internalEdges_pos {γ : FeynmanSubgraph G}
    (h : 0 < γ.internalEdges.card) : γ.IsNonempty := by
  rw [Multiset.card_pos] at h
  rcases Multiset.exists_mem_of_ne_zero h with ⟨e, he⟩
  have hsupp := γ.edges_supported e he
  unfold FeynmanSubgraph.IsNonempty FeynmanSubgraph.vertexCount
  rw [Finset.card_pos]
  refine ⟨e.source, ?_⟩
  simp [FeynmanEdge.SupportedOn] at hsupp
  exact hsupp.1

/-! ## Step 1 — family-indexed finite index -/

open Classical in
/-- **R-6c-QFT-R1-body-569 — the family-indexed proper connected-divergent index.**  Connected-divergent
(under the family measure `D G`), with a nonempty internal-edge set and a nonempty complement (so the
subgraph is proper).  `Fintype` is bookkeeping; there is **no** `DivergenceMeasure` instance binder. -/
noncomputable def FeynmanGraph.properConnectedDivergentSubgraphsFor
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)] :
    Finset (FeynmanSubgraph G) :=
  (Finset.univ : Finset (FeynmanSubgraph G)).filter fun γ =>
    @FeynmanSubgraph.IsConnectedDivergent G (D G) γ
      ∧ 0 < γ.internalEdges.card ∧ 0 < γ.complementEdges.card

@[simp] theorem FeynmanGraph.mem_properConnectedDivergentSubgraphsFor
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (γ : FeynmanSubgraph G) :
    γ ∈ G.properConnectedDivergentSubgraphsFor D ↔
      @FeynmanSubgraph.IsConnectedDivergent G (D G) γ
        ∧ 0 < γ.internalEdges.card ∧ 0 < γ.complementEdges.card := by
  unfold FeynmanGraph.properConnectedDivergentSubgraphsFor
  simp

theorem FeynmanGraph.properConnectedDivergentSubgraphsFor_isConnectedDivergent
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.properConnectedDivergentSubgraphsFor D) :
    @FeynmanSubgraph.IsConnectedDivergent G (D G) γ :=
  ((FeynmanGraph.mem_properConnectedDivergentSubgraphsFor D G γ).mp hγ).1

theorem FeynmanGraph.properConnectedDivergentSubgraphsFor_internalEdges_pos
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.properConnectedDivergentSubgraphsFor D) :
    0 < γ.internalEdges.card :=
  (((FeynmanGraph.mem_properConnectedDivergentSubgraphsFor D G γ).mp hγ).2).1

theorem FeynmanGraph.properConnectedDivergentSubgraphsFor_complementEdges_pos
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.properConnectedDivergentSubgraphsFor D) :
    0 < γ.complementEdges.card :=
  (((FeynmanGraph.mem_properConnectedDivergentSubgraphsFor D G γ).mp hγ).2).2

/-- The φ⁴ specialization of the family-indexed index. -/
noncomputable def FeynmanGraph.phi4ProperConnectedDivergentSubgraphs
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)] : Finset (FeynmanSubgraph G) :=
  G.properConnectedDivergentSubgraphsFor phi4DivergenceMeasureFamily

theorem FeynmanGraph.mem_phi4ProperConnectedDivergentSubgraphs
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)] (γ : FeynmanSubgraph G) :
    γ ∈ G.phi4ProperConnectedDivergentSubgraphs ↔
      @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ
        ∧ 0 < γ.internalEdges.card ∧ 0 < γ.complementEdges.card :=
  FeynmanGraph.mem_properConnectedDivergentSubgraphsFor phi4DivergenceMeasureFamily G γ

theorem FeynmanGraph.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.phi4ProperConnectedDivergentSubgraphs) :
    @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ :=
  FeynmanGraph.properConnectedDivergentSubgraphsFor_isConnectedDivergent phi4DivergenceMeasureFamily G hγ

theorem FeynmanGraph.phi4ProperConnectedDivergentSubgraphs_internalEdges_pos
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.phi4ProperConnectedDivergentSubgraphs) :
    0 < γ.internalEdges.card :=
  FeynmanGraph.properConnectedDivergentSubgraphsFor_internalEdges_pos phi4DivergenceMeasureFamily G hγ

/-! ## Step 2 — index rename certificate -/

/-- **R-6c-QFT-R1-body-569 — the index is rename-stable for a coherent family.**  Certificate for the next
body's `Finset.sum_bij`; the coproduct invariance itself is not yet entered. -/
theorem FeynmanGraph.mapPerm_mem_properConnectedDivergentSubgraphsFor_iff
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (π : Equiv.Perm VertexId) (G : FeynmanGraph)
    [Fintype (FeynmanSubgraph G)] [Fintype (FeynmanSubgraph (G.mapPerm π))]
    (γ : FeynmanSubgraph G) :
    γ.mapPerm π ∈ (G.mapPerm π).properConnectedDivergentSubgraphsFor D
      ↔ γ ∈ G.properConnectedDivergentSubgraphsFor D := by
  rw [FeynmanGraph.mem_properConnectedDivergentSubgraphsFor,
    FeynmanGraph.mem_properConnectedDivergentSubgraphsFor]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact FeynmanSubgraph.mapPerm_isConnectedDivergent_iff_of_family D Inv π γ
  · rw [FeynmanSubgraph.mapPerm_internalEdges, Multiset.card_map]
  · rw [FeynmanSubgraph.mapPerm_complementEdges, Multiset.card_map]

/-! ## Step 3 — polynomial carrier -/

/-- The family-indexed strict Hopf polynomial algebra. -/
noncomputable abbrev HopfHFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) : Type :=
  MvPolynomial (HopfGenFor D Inv) ℚ

/-- The canonical φ⁴ strict Hopf polynomial algebra. -/
noncomputable abbrev Phi4HopfH : Type :=
  HopfHFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily

/-- A family generator as a polynomial variable. -/
noncomputable def genFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (g : HopfGenFor D Inv) : HopfHFor D Inv :=
  MvPolynomial.X g

/-- A φ⁴ generator as a polynomial variable. -/
noncomputable def phi4Gen (g : Phi4HopfGen) : Phi4HopfH :=
  MvPolynomial.X g

/-! ## Step 4 — ambient generator -/

/-- **R-6c-QFT-R1-body-569 — the ambient φ⁴ generator.**  A well-formed 1PI divergent graph is itself a
`Phi4HopfGen` (represented by its own class). -/
def FeynmanGraph.toPhi4HopfGen (G : FeynmanGraph) (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    Phi4HopfGen :=
  G.toHopfGenFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    ⟨hWF, h1PI.isSupportConnected, h1PI, hDiv⟩

@[simp] theorem FeynmanGraph.toPhi4HopfGen_val (G : FeynmanGraph) (hWF : G.WellFormed)
    (h1PI : G.IsOnePI)
    (hDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    (G.toPhi4HopfGen hWF h1PI hDiv).val = G.toClass := rfl

/-! ## Step 5 — connected summand -/

/-- **R-6c-QFT-R1-body-569 — the φ⁴ connected coproduct summand `[γ] ⊗ [Γ/γ]`.**  Left factor = body-568's
boundary-completed left factor; right factor = body-566's direct quotient factor.  `0` off the index. -/
noncomputable def FeynmanGraph.phi4ConnectedStrictSummand
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    (γ : FeynmanSubgraph G) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  if hγ : γ ∈ G.phi4ProperConnectedDivergentSubgraphs then
    phi4Gen (γ.toPhi4HopfGen (G.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent hγ))
      ⊗ₜ[ℚ]
    phi4Gen (γ.contractToPhi4HopfGen hWF h1PI
      (G.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent hγ).2.1
      (isNonempty_of_internalEdges_pos
        (G.phi4ProperConnectedDivergentSubgraphs_internalEdges_pos hγ))
      hGDiv)
  else 0

theorem FeynmanGraph.phi4ConnectedStrictSummand_of_not_mem
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    {γ : FeynmanSubgraph G} (hγ : γ ∉ G.phi4ProperConnectedDivergentSubgraphs) :
    G.phi4ConnectedStrictSummand hWF h1PI hGDiv γ = 0 := by
  unfold FeynmanGraph.phi4ConnectedStrictSummand
  rw [dif_neg hγ]

theorem FeynmanGraph.phi4ConnectedStrictSummand_of_mem
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    {γ : FeynmanSubgraph G} (hγ : γ ∈ G.phi4ProperConnectedDivergentSubgraphs) :
    G.phi4ConnectedStrictSummand hWF h1PI hGDiv γ =
      phi4Gen (γ.toPhi4HopfGen (G.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent hγ))
        ⊗ₜ[ℚ]
      phi4Gen (γ.contractToPhi4HopfGen hWF h1PI
        (G.phi4ProperConnectedDivergentSubgraphs_isConnectedDivergent hγ).2.1
        (isNonempty_of_internalEdges_pos
          (G.phi4ProperConnectedDivergentSubgraphs_internalEdges_pos hγ))
        hGDiv) := by
  unfold FeynmanGraph.phi4ConnectedStrictSummand
  rw [dif_pos hγ]

/-! ## Step 6 — representative formula -/

/-- **R-6c-QFT-R1-body-569 — the representative-level φ⁴ coproduct.**  `[G] ⊗ 1 + 1 ⊗ [G] + ∑ [γ] ⊗ [Γ/γ]`
over the proper connected-divergent φ⁴ index.  Representative independence (descent to the class) is the
next body. -/
noncomputable def FeynmanGraph.coproductGen_phi4
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  let genG := phi4Gen (G.toPhi4HopfGen hWF h1PI hGDiv)
  genG ⊗ₜ[ℚ] (1 : Phi4HopfH)
    + (1 : Phi4HopfH) ⊗ₜ[ℚ] genG
    + ∑ γ ∈ G.phi4ProperConnectedDivergentSubgraphs, G.phi4ConnectedStrictSummand hWF h1PI hGDiv γ

theorem FeynmanGraph.coproductGen_phi4_eq
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    G.coproductGen_phi4 hWF h1PI hGDiv =
      phi4Gen (G.toPhi4HopfGen hWF h1PI hGDiv) ⊗ₜ[ℚ] (1 : Phi4HopfH)
        + (1 : Phi4HopfH) ⊗ₜ[ℚ] phi4Gen (G.toPhi4HopfGen hWF h1PI hGDiv)
        + ∑ γ ∈ G.phi4ProperConnectedDivergentSubgraphs,
            G.phi4ConnectedStrictSummand hWF h1PI hGDiv γ := rfl

end GaugeGeometry.QFT.Combinatorial
