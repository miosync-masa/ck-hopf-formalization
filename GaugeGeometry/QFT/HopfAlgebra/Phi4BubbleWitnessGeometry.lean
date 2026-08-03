import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeConcreteCounterexample

/-!
# QFT-R2-body-665a — the concrete NON-VACUITY witness graph + its raw geometry (Figure-1's positive counterpart)

The concrete non-vacuity witness: a φ⁴ VACUUM graph (8 edges, 4 vertices, `L = E − V + 1 = 8 − 4 + 1 = 5`)
containing a ONE-LOOP FOUR-POINT BUBBLE subdivergence on `{0,1}` that — unlike Figure 1's dropped outer
forest — IS edge-complete, so it will pass the fifth (edge-completeness) axis into W‴.  This file = the
graph + raw geometry + exact counts + edge-completeness + id-uniqueness + support + saturation-input;
topology/CD is 665b, W‴ membership + forest-sum ≠ 0 + non-primitive coproduct is 665c.  Positive
counterpart to the Figure-1 negative example.

## The concrete graph (build exactly this)

`VertexId := Nat`; vertices `{0,1,2,3}` (all valence 4); NO external legs (vacuum).  Eight distinct-`edgeId`
internal edges (all sector `.hypercharge`):

```text
  bubble :  e0 (0–1) [id 0]   e1 (0–1) [id 1]
  cross  :  e2 (0–2) [id 2]   e3 (0–3) [id 3]   e4 (1–2) [id 4]
            e5 (1–3) [id 5]   e6 (2–3) [id 6]   e7 (2–3) [id 7]
```

Quartic incidence (every vertex valence 4):
`0:{e0,e1,e2,e3}  1:{e0,e1,e4,e5}  2:{e2,e4,e6,e7}  3:{e3,e5,e6,e7}`.

* `phi4BubbleAmbient` `G` — all 8 edges, vertices `{0,1,2,3}`, no legs.  `E = 8, V = 4, L = 5`.
* `phi4BubbleInner` `δ ⊆ G` — the one-loop four-point bubble on `{0,1}`; internal edges `{e0,e1}` (the two
  `0–1` edges).  `E_F = 2, V_F = 2, L_F = 1, ω_F = 0` (marginal).

## Figure 1 (the caption, INVERTED into a positive witness)

> Figure 1's outer forest was DROPPED by W‴: its hidden root edge `h03` had both endpoints inside `γ` but
> was not an internal edge of `γ`, so vertex-induced edge-completeness FAILED (`count 1 ≤ count 0` false).
> Here the bubble is engineered so the ambient edges with BOTH endpoints in `{0,1}` are EXACTLY the two
> bubble edges `{e0,e1}` (every other edge touches vertex 2 or 3), so
> `filter (both ∈ {0,1}) G.internalEdges = {e0,e1} = δ.internalEdges` and edge-completeness PASSES.  This is
> the load-bearing "passes the fifth axis" fact — the exact inverse of Figure-1's failing `h03`.

## Steps (this file = 665a)

1. Ambient `phi4BubbleAmbient`, bubble subgraph `phi4BubbleInner`; the named edge multisets
   `phi4BubbleBubbleEdges = {e0,e1}` and `phi4BubbleCrossEdges = {e2,…,e7}`,
   `G.internalEdges = phi4BubbleBubbleEdges + phi4BubbleCrossEdges`.
2. Exact counts: `G.internalEdges.card = 8`, `δ.internalEdges.card = 2`.
3. **Edge-completeness (THE POINT)** `phi4BubbleInner_internalEdgeComplete` — via
   `filter_add` + `filter_eq_self` (bubble: both endpoints in `{0,1}`) + `filter_eq_nil` (cross: an
   endpoint in `{2,3}`), the boundary filter reduces to `{e0,e1} = δ.internalEdges`, then `le_refl`.
4. Positive complement: `G.internalEdges − δ.internalEdges = phi4BubbleCrossEdges` (six edges), card `6 > 0`.
5. Id/leg uniqueness + ambient support: `phi4BubbleAmbient.EdgeIdsUnique` (edgeIds `0..7` distinct),
   `phi4BubbleAmbient.LegIdsUnique` (empty legs), `ResolvedAmbientSupported phi4BubbleAmbient`.
6. Bubble external-leg saturation-input `phi4BubbleInner_saturated`
   (`ResolvedExternalLegSaturated phi4BubbleAmbient phi4BubbleInner`; trivial — the vacuum ambient has no
   external legs, so the saturating filter is empty).

## HALT compliance / SPLIT NOTE (honest partial)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only; NO `Lean.ofReduceBool` — every `decide` is
PLAIN decide, NO `native_decide`).  ZERO forbidden divergence classes in ANY declaration type.
Multiplicity-exact (`Multiset`, `filter_add` / `filter_eq_self` / `filter_eq_nil` / `add_tsub_cancel_left`;
the edge-completeness reduction keeps the exact `{e0,e1}` equality, never weakened to card).  No coproduct /
evaluation / symmetry factor; no `HEq` / `cast` / graph-data `▸`; ZERO new `structure` / `class` /
`instance`; bodies UNEDITED.

**SPLIT (665a delivered; 665b, 665c remain).**  This file is the topology-free half: the concrete graph +
subgraph geometry + exact counts + the PASSING edge-completeness + positive complement + id-uniqueness +
ambient support + trivial (empty-leg) saturation input.  The remaining **665b** owns the bubble's
NATIVE topology / connected-divergent certificate (`phi4BubbleInner.forget.IsConnectedDivergent`), and
**665c** owns the singleton admissible forest, its W‴ membership, the forest-sum ≠ 0, and the non-primitive
coproduct.  The admissible forest `singletonResolvedAdmissibleSubgraph` is NOT built here because it
requires the CD certificate (665b); the raw-subgraph saturation input is the honest geometric residue that
665c's forest-level wrapper will consume.  Mirrors the Figure-1 split (653b-1 geometry, 653b-2a topology,
653b-2b membership).  Nothing here is faked to complete the split.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-! ## Step 1 — the concrete 8-edge vacuum ambient + the bubble subgraph -/

/-- A boundary-resolved `.hypercharge` internal edge with the given `edgeId` and endpoints
(mirrors Figure-1's `phi4CarrierGapEdge`). -/
def phi4BubbleEdge (id s t : Nat) : ResolvedFeynmanEdge :=
  ⟨⟨id⟩, s, t, .hypercharge⟩

/-- The two bubble edges `e0, e1` (both `0–1`) — the one-loop four-point subdivergence on `{0,1}`. -/
def phi4BubbleBubbleEdges : Multiset ResolvedFeynmanEdge :=
  {phi4BubbleEdge 0 0 1, phi4BubbleEdge 1 0 1}

/-- The six cograph (complement) edges `e2,…,e7` — each touches vertex `2` or `3`. -/
def phi4BubbleCrossEdges : Multiset ResolvedFeynmanEdge :=
  {phi4BubbleEdge 2 0 2, phi4BubbleEdge 3 0 3, phi4BubbleEdge 4 1 2,
   phi4BubbleEdge 5 1 3, phi4BubbleEdge 6 2 3, phi4BubbleEdge 7 2 3}

/-- **body-665a (Step 1) — the concrete 8-edge boundary-resolved φ⁴ VACUUM ambient graph.**
`E = 8, V = 4, L = E − V + 1 = 5`; every vertex has valence 4; no external legs. -/
def phi4BubbleAmbient : ResolvedFeynmanGraph where
  vertices := {0, 1, 2, 3}
  internalEdges := phi4BubbleBubbleEdges + phi4BubbleCrossEdges
  externalLegs := 0

/-- **body-665a (Step 1) — the one-loop four-point bubble subgraph `δ`.**  Vertices `{0,1}`, internal edges
the two `0–1` bubble edges `{e0,e1}`; no external legs.  `E_F = 2, V_F = 2, L_F = 1, ω_F = 0` (marginal). -/
def phi4BubbleInner : ResolvedFeynmanSubgraph phi4BubbleAmbient where
  vertices := {0, 1}
  internalEdges := phi4BubbleBubbleEdges
  externalLegs := 0
  vertices_subset := by decide
  internalEdges_le := by
    show phi4BubbleBubbleEdges ≤ phi4BubbleBubbleEdges + phi4BubbleCrossEdges
    exact Multiset.le_add_right _ _
  externalLegs_le := Multiset.zero_le _
  edges_supported := by
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  legs_supported := by intro ℓ h; simp at h

/-- `phi4BubbleInner.vertices = {0,1}` (definitional; exposed for the boundary filter). -/
@[simp] theorem phi4BubbleInner_vertices :
    phi4BubbleInner.vertices = ({0, 1} : Finset VertexId) := rfl

/-! ## Step 2 — exact counts -/

/-- **body-665a (Step 2) — the ambient has exactly 8 internal edges.** -/
theorem phi4BubbleAmbient_internalEdges_card :
    phi4BubbleAmbient.internalEdges.card = 8 := by decide

/-- **body-665a (Step 2) — the bubble has exactly 2 internal edges** (`E_F = 2`). -/
theorem phi4BubbleInner_internalEdges_card :
    phi4BubbleInner.internalEdges.card = 2 := by decide

/-! ## Step 3 — edge-completeness of the bubble (THE POINT: passes the fifth axis) -/

/-- **body-665a (Step 3, THE POINT) — the bubble is internal-edge complete.**  The ambient edges with BOTH
endpoints inside `{0,1}` are EXACTLY the two bubble edges `{e0,e1}` (every cross edge touches vertex `2` or
`3`), which equals `δ.internalEdges`.  The boundary filter therefore reduces to `{e0,e1}` and the
edge-completeness `≤` holds by reflexivity — the exact INVERSE of Figure-1's
`phi4CarrierGapOuter_not_internalEdgeComplete` (which fails at the hidden root edge `h03`,
`count 1 ≤ count 0`).  This is the load-bearing "passes the fifth (edge-completeness) axis into W‴" fact. -/
theorem phi4BubbleInner_internalEdgeComplete :
    ResolvedInternalEdgeComplete phi4BubbleInner := by
  unfold ResolvedInternalEdgeComplete
  show (phi4BubbleBubbleEdges + phi4BubbleCrossEdges).filter
      (fun e => e.source ∈ phi4BubbleInner.vertices ∧ e.target ∈ phi4BubbleInner.vertices)
      ≤ phi4BubbleBubbleEdges
  rw [Multiset.filter_add]
  have hb : phi4BubbleBubbleEdges.filter
      (fun e => e.source ∈ phi4BubbleInner.vertices ∧ e.target ∈ phi4BubbleInner.vertices)
      = phi4BubbleBubbleEdges := by
    rw [Multiset.filter_eq_self]
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  have hc : phi4BubbleCrossEdges.filter
      (fun e => e.source ∈ phi4BubbleInner.vertices ∧ e.target ∈ phi4BubbleInner.vertices)
      = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    fin_cases he <;> decide
  rw [hb, hc, add_zero]

/-! ## Step 4 — the positive complement (properness input) -/

/-- **body-665a (Step 4) — the raw complement is exactly the six cograph edges.**
`G.internalEdges − δ.internalEdges = (phi4BubbleBubbleEdges + phi4BubbleCrossEdges) − phi4BubbleBubbleEdges
= phi4BubbleCrossEdges`.  (Stated on the raw multiset difference; the forest-level `complementEdges` wrapper
is 665c — it lives on the admissible subgraph, which needs the CD certificate.) -/
theorem phi4BubbleInner_complementEdges_eq :
    phi4BubbleAmbient.internalEdges - phi4BubbleInner.internalEdges = phi4BubbleCrossEdges := by
  show (phi4BubbleBubbleEdges + phi4BubbleCrossEdges) - phi4BubbleBubbleEdges = phi4BubbleCrossEdges
  rw [add_tsub_cancel_left]

/-- **body-665a (Step 4) — the complement has exactly six edges.** -/
theorem phi4BubbleInner_complementEdges_card :
    (phi4BubbleAmbient.internalEdges - phi4BubbleInner.internalEdges).card = 6 := by
  rw [phi4BubbleInner_complementEdges_eq]; decide

/-- **body-665a (Step 4, PROPERNESS INPUT) — the complement is nonempty** (`6 > 0`; the positive-complement
input the later `IsProperForest` fifth conjunct consumes). -/
theorem phi4BubbleInner_complementEdges_card_pos :
    0 < (phi4BubbleAmbient.internalEdges - phi4BubbleInner.internalEdges).card := by
  rw [phi4BubbleInner_complementEdges_card]; decide

/-! ## Step 5 — id/leg uniqueness + ambient support -/

/-- **body-665a (Step 5) — the ambient has unique edge ids** (edgeIds `0..7` all distinct).  Mirrors
Figure-1's `phi4CarrierGapAmbient_edgeIdsUnique`. -/
theorem phi4BubbleAmbient_edgeIdsUnique : phi4BubbleAmbient.EdgeIdsUnique := by
  intro e₁ h₁ e₂ h₂ hid
  fin_cases h₁ <;> fin_cases h₂ <;> revert hid <;> decide

/-- **body-665a (Step 5) — the ambient has unique leg ids** (no external legs — trivially).  Mirrors
Figure-1's `phi4CarrierGapAmbient_legIdsUnique`. -/
theorem phi4BubbleAmbient_legIdsUnique : phi4BubbleAmbient.LegIdsUnique := by
  intro ℓ₁ h₁ ℓ₂ h₂ hid
  exact absurd h₁ (Multiset.notMem_zero ℓ₁)

/-- **body-665a (Step 5) — the ambient is ambient-supported** (all 8 edges endpoint-supported, no legs).
Mirrors Figure-1's `phi4CarrierGapAmbient_ambientSupported`. -/
theorem phi4BubbleAmbient_ambientSupported :
    ResolvedAmbientSupported phi4BubbleAmbient := by
  refine ⟨?_, ?_⟩
  · intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-! ## Step 6 — the bubble external-leg saturation input -/

/-- **body-665a (Step 6) — the bubble is external-leg saturated** (raw subgraph version).  Trivial: the
vacuum ambient `phi4BubbleAmbient` has NO external legs, so the saturating filter is empty.  This is the
raw-subgraph saturation input; the forest-level `ResolvedForestExternalLegSaturated` wrapper is 665c (it
needs the admissible forest, hence the CD certificate).  Mirrors Figure-1's `phi4CarrierGap_outer_saturated`. -/
theorem phi4BubbleInner_saturated :
    ResolvedExternalLegSaturated phi4BubbleAmbient phi4BubbleInner := by
  unfold ResolvedExternalLegSaturated
  show (0 : Multiset ResolvedExternalLeg).filter _ ≤ _
  rw [Multiset.filter_zero]
  exact Multiset.zero_le _

end GaugeGeometry.QFT.Combinatorial
