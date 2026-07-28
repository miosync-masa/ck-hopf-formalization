import GaugeGeometry.QFT.Combinatorial.DivergenceMeasureFamily
import GaugeGeometry.QFT.HopfAlgebra.SubgraphClass

/-!
# QFT-R1-body-576 — coherent iso-invariance for divergence-measure families

The φ⁴ landing root (body-577+) needs an *iso*-coherence interface alongside body-565's permutation one.
Body-575's audit fixed the shape: the old `IsIsoInvariantDivergence` blanket is uninhabitable in the family
world (its target measure is re-quantified independently), so — exactly as body-565 did for `mapPerm` — we
build a coherent **family** interface and inhabit it for φ⁴, with the boundary carried *before* intrinsifying.

## Contents

* Step 1 `IsoInvariantDivergenceMeasureFamily` — the coherent iso interface (one `Prop` structure, consumed
  explicitly; the old `IsIsoInvariantDivergence` class is not edited or inhabited).
* Step 2 `IsIso.boundaryEdgeCount_eq` / `IsIso.physicalExternalLegCount_eq` — boundary-aware iso transport,
  by unpacking the ambient-fixing witness directly (**not** via `toFeynmanGraph`, which forgets the induced
  boundary); the induced-boundary multiplicity is preserved exactly (`Multiset.map`, not membership).
* Step 3 `IsIso.phi4SuperficialDegree_eq` / `phi4DivergenceMeasure_degree_iso` /
  `phi4IsoInvariantDivergenceMeasureFamily` — the φ⁴ inhabitant (explicit `@DivergenceMeasure.degree`).
* Step 4 `IsIso.isDivergent_iff_of_family` / `IsIso.isConnectedDivergent_iff_of_family` — predicate transport
  for the later carrier re-key (connectivity / 1PI reuse the existing `IsIso.isConnected_iff`/`.isOnePI_iff`).

Per the HALT: zero new `class`/`instance` (exactly one new `Prop` structure); the old `IsIsoInvariantDivergence`
is not edited/inhabited; no W″ carrier/root; no ambient bridge; no forest-preservation re-proof; no reflection;
no forest coproduct invariance; no coassociativity realization.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-- **Auxiliary (no injectivity needed).**  `map` commutes with truncated subtraction when the subtrahend
is `≤` the minuend. -/
private theorem multiset_map_sub_of_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {A B : Multiset α} (hBA : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  calc
    (A - B).map f = ((A - B).map f + B.map f) - B.map f := by
      rw [Multiset.add_sub_cancel_right]
    _ = ((A - B + B).map f) - B.map f := by rw [Multiset.map_add]
    _ = A.map f - B.map f := by rw [Multiset.sub_add_cancel hBA]

/-! ## Step 1 — coherent iso-invariance interface -/

/-- **R-6c-QFT-R1-body-576 — coherent iso-invariance interface.**  A divergence-measure family whose per-graph
member is invariant under the Path-B (ambient-fixing) subgraph iso.  A `Prop` structure consumed as an
explicit argument — the intra-ambient counterpart of body-565's `PermInvariantDivergenceMeasureFamily`, and
NOT the old `IsIsoInvariantDivergence` class. -/
structure IsoInvariantDivergenceMeasureFamily (D : DivergenceMeasureFamily) : Prop where
  degree_iso :
    ∀ {G : FeynmanGraph} {γ₁ γ₂ : FeynmanSubgraph G}, γ₁.IsIso γ₂ →
      @DivergenceMeasure.degree G (D G) γ₁ = @DivergenceMeasure.degree G (D G) γ₂

/-! ## Step 2 — boundary-aware iso transport (load-bearing) -/

/-- **R-6c-QFT-R1-body-576 — boundary-edge count is iso-invariant.**  Proved by unpacking the ambient-fixing
witness (`G.mapPerm π = G` makes `G.internalEdges` `map π`-invariant), transporting `complementEdges` and
`boundaryEdges` exactly, and taking cardinalities.  No `toFeynmanGraph` (it would drop the induced boundary);
multiplicity preserved. -/
theorem FeynmanSubgraph.IsIso.boundaryEdgeCount_eq {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₂.boundaryEdgeCount = γ₁.boundaryEdgeCount := by
  obtain ⟨π, hG, hv, hi, _he⟩ := h
  have hGinv : G.internalEdges.map (FeynmanEdge.map π) = G.internalEdges := by
    have hgi : (G.mapPerm π).internalEdges = G.internalEdges :=
      congrArg FeynmanGraph.internalEdges hG
    rwa [FeynmanGraph.mapPerm_internalEdges] at hgi
  have hcomp : γ₂.complementEdges = γ₁.complementEdges.map (FeynmanEdge.map π) := by
    unfold FeynmanSubgraph.complementEdges
    rw [hi, multiset_map_sub_of_le (FeynmanEdge.map π) γ₁.internalEdges_le, hGinv]
  have hbe : γ₂.boundaryEdges = γ₁.boundaryEdges.map (FeynmanEdge.map π) := by
    unfold FeynmanSubgraph.boundaryEdges
    rw [hcomp, Multiset.filter_map]
    congr 1
    apply Multiset.filter_congr
    intro e _
    show γ₂.IsBoundaryEdge (e.map π) ↔ γ₁.IsBoundaryEdge e
    unfold FeynmanSubgraph.IsBoundaryEdge
    rw [hv]
    simp only [FeynmanEdge.map_source, FeynmanEdge.map_target, π.injective.mem_finset_image]
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [hbe, Multiset.card_map]

/-- **R-6c-QFT-R1-body-576 — physical external valence is iso-invariant.** -/
theorem FeynmanSubgraph.IsIso.physicalExternalLegCount_eq {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₂.physicalExternalLegCount = γ₁.physicalExternalLegCount := by
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [h.boundaryEdgeCount_eq]
  obtain ⟨π, _hG, _hv, _hi, he⟩ := h
  rw [he, Multiset.card_map]

/-! ## Step 3 — φ⁴ inhabitant -/

/-- **R-6c-QFT-R1-body-576 — φ⁴ degree is iso-invariant.** -/
theorem FeynmanSubgraph.IsIso.phi4SuperficialDegree_eq {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    γ₂.phi4SuperficialDegree = γ₁.phi4SuperficialDegree := by
  unfold FeynmanSubgraph.phi4SuperficialDegree
  rw [h.physicalExternalLegCount_eq]

/-- **R-6c-QFT-R1-body-576 — φ⁴ measure iso-invariance (explicit measure).** -/
theorem phi4DivergenceMeasure_degree_iso {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    @DivergenceMeasure.degree G (phi4DivergenceMeasure G) γ₁
      = @DivergenceMeasure.degree G (phi4DivergenceMeasure G) γ₂ := by
  rw [phi4DivergenceMeasure_degree, phi4DivergenceMeasure_degree]
  exact (h.phi4SuperficialDegree_eq).symm

/-- **R-6c-QFT-R1-body-576 — the φ⁴ family is iso-coherent.**  A `def`, not an `instance` — inhabited by the
explicit φ⁴ iso equality. -/
def phi4IsoInvariantDivergenceMeasureFamily :
    IsoInvariantDivergenceMeasureFamily phi4DivergenceMeasureFamily where
  degree_iso h := phi4DivergenceMeasure_degree_iso h

/-! ## Step 4 — predicate transport -/

/-- **R-6c-QFT-R1-body-576 — subgraph divergence is iso-invariant for a coherent family.** -/
theorem FeynmanSubgraph.IsIso.isDivergent_iff_of_family
    (D : DivergenceMeasureFamily) (Inv : IsoInvariantDivergenceMeasureFamily D)
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    @FeynmanSubgraph.IsDivergent G (D G) γ₁ ↔ @FeynmanSubgraph.IsDivergent G (D G) γ₂ := by
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree
  rw [Inv.degree_iso h]

/-- **R-6c-QFT-R1-body-576 — subgraph connected-divergence is iso-invariant for a coherent family.**
Connectivity / 1PI reuse the existing `IsIso.isConnected_iff` / `.isOnePI_iff` (no new topology). -/
theorem FeynmanSubgraph.IsIso.isConnectedDivergent_iff_of_family
    (D : DivergenceMeasureFamily) (Inv : IsoInvariantDivergenceMeasureFamily D)
    {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.IsIso γ₂) :
    @FeynmanSubgraph.IsConnectedDivergent G (D G) γ₁
      ↔ @FeynmanSubgraph.IsConnectedDivergent G (D G) γ₂ := by
  unfold FeynmanSubgraph.IsConnectedDivergent
  exact and_congr h.isConnected_iff
    (and_congr h.isOnePI_iff (FeynmanSubgraph.IsIso.isDivergent_iff_of_family D Inv h))

end GaugeGeometry.QFT.Combinatorial
