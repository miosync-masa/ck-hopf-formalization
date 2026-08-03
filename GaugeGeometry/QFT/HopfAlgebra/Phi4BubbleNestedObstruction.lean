import GaugeGeometry.QFT.HopfAlgebra.Phi4BubbleWitnessTopology
import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeLeftFactorProduct

/-!
# QFT-R2-body-665d — the ∃-no-go witness: the bubble inhabits body-625's nested-completion obstruction

Body-625's no-go `phi4WTriplePrime_nestedLeft_class_ne_of_inheritedOuter` was a UNIVERSAL statement —
vacuous if `inheritedOuter` were always empty.  Figure 1 CANNOT witness it (its `inheritedOuter` is
PROVED empty — `phi4CarrierGap_inheritedOuter`: the outer carries all six vertices, so it has NO
boundary edges; its defect is the HIDDEN channel).  The bubble CAN: `phi4BubbleInner` has 4 boundary
edges (`phi4BubbleInner_resolvedBoundaryEdges`, the four straddling cross edges `e2,e3,e4,e5`), and
the nested copy `phi4BubbleNested` on its boundary completion inherits them.  This file issues the
∃-no-go `exists_nested_completion_obstruction`: a concrete φ⁴ configuration on which the naive nested
completion PROVABLY differs from the root-relative one — the obstruction (paper Thm 2) is inhabited,
exactly as the bubble's non-primitive coproduct (665c) inhabited Thm 5.  The bubble does double duty:
the positive example for the coproduct AND the witness for the no-go.

## Contents

1. **`phi4BubbleNested`** — the nested δ on the bubble's boundary completion
   `phi4BubbleInner.boundaryCompletedResolvedGraph`: vertices `{0,1}`, internal edges the two bubble
   edges `{e0,e1}`, no legs (the `phi4CarrierGapInner` obligation pattern, retargeted at the bcrg).
2. **`phi4BubbleNested_mem_inheritedOuter`** — the load-bearing EXISTENCE fact: the straddling cross
   edge `e2 (0–2)` is an inherited outer boundary edge of the nested pair (its inside endpoint `0`
   lies in `δ.vertices = {0,1}`).  Also `phi4Bubble_inheritedOuter_ne_zero`.
3. **`phi4BubbleNested_class_ne`** — the concrete class-level no-go instance: body-625's ∀-theorem
   applied to the bubble witness (purely combinatorial — NO CD/topology hypotheses).
4. **`exists_nested_completion_obstruction` (HEADLINE)** — the 4-fold ∃: there EXISTS an ambient `G`
   with unique edge ids, a subgraph `γ`, a nested `δ` on `γ`'s boundary completion, and an inherited
   outer edge `e`, such that the local nested completion and the root-relative completion have
   DIFFERENT resolved classes.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only; NO `Lean.ofReduceBool` — every `decide`
is PLAIN decide, NO `native_decide`).  ZERO forbidden divergence classes in ANY declaration type.
Body-625's ∀-theorem and 665a/b are consumed as BLACK BOXES (no re-proof of the leg-id-profile
argument or the boundary-edge computation).  No `HEq` / `cast` / graph-data `▸`; ZERO new
`structure` / `class` / permanent `instance` (`phi4BubbleNested` is a plain `def`); bodies ≤665c
UNEDITED.  **HALT (665d — ∃-no-go delivered).**
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-! ## Step 1 — the nested bubble δ on the bubble's boundary completion -/

/-- **body-665d (Step 1) — the nested bubble δ.**  The copy of the bubble as a subgraph of its OWN
boundary completion `phi4BubbleInner.boundaryCompletedResolvedGraph`: vertices `{0,1}`, internal edges
the two `0–1` bubble edges `{e0,e1}`, no legs.  (The `phi4CarrierGapInner` obligation pattern; the
bcrg has the SAME vertices/internal edges as `phi4BubbleInner` — the completion only adds legs.) -/
def phi4BubbleNested :
    ResolvedFeynmanSubgraph phi4BubbleInner.boundaryCompletedResolvedGraph where
  vertices := {0, 1}
  internalEdges := phi4BubbleBubbleEdges
  externalLegs := 0
  vertices_subset := by
    rw [boundaryCompletedResolvedGraph_vertices]
    exact Finset.Subset.refl _
  internalEdges_le := by
    rw [boundaryCompletedResolvedGraph_internalEdges]
    exact le_refl _
  externalLegs_le := Multiset.zero_le _
  edges_supported := by
    intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  legs_supported := by intro ℓ h; simp at h

/-- `phi4BubbleNested.vertices = {0,1}` (definitional; exposed for the inherited-outer filter). -/
@[simp] theorem phi4BubbleNested_vertices :
    phi4BubbleNested.vertices = ({0, 1} : Finset VertexId) := rfl

/-! ## Step 2 — the inherited-outer membership (the load-bearing existence fact) -/

/-- **body-665d (Step 2, THE EXISTENCE FACT) — the straddling cross edge `e2 (0–2)` is an inherited
outer boundary edge of the nested pair.**  `e2 ∈ phi4BubbleInner.resolvedBoundaryEdges` (one of the
four straddling cross edges, 665b) and its inside endpoint `resolvedInsideEndpoint e2 = 0` lies in
`phi4BubbleNested.vertices = {0,1}`.  This is exactly what Figure 1 canNOT provide
(`phi4CarrierGap_inheritedOuter = 0`). -/
theorem phi4BubbleNested_mem_inheritedOuter :
    phi4BubbleEdge 2 0 2 ∈ inheritedOuter phi4BubbleInner phi4BubbleNested := by
  unfold inheritedOuter
  rw [phi4BubbleInner_resolvedBoundaryEdges]
  exact Multiset.mem_filter.mpr ⟨by decide, by decide⟩

/-- **body-665d (Step 2) — the inherited outer boundary is NONEMPTY** (from the membership).  The
exact inverse of Figure 1's `phi4CarrierGap_inheritedOuter = 0`. -/
theorem phi4Bubble_inheritedOuter_ne_zero :
    inheritedOuter phi4BubbleInner phi4BubbleNested ≠ 0 := by
  intro h
  have hm := phi4BubbleNested_mem_inheritedOuter
  rw [h] at hm
  exact Multiset.notMem_zero (phi4BubbleEdge 2 0 2) hm

/-! ## Step 3 — the concrete class-level no-go instance -/

/-- **body-665d (Step 3) — the concrete no-go instance.**  On the bubble witness the LOCAL nested
completion `phi4BubbleNested.boundaryCompletedResolvedGraph` and the ROOT-relative completion
`(rootRelativeInner …).boundaryCompletedResolvedGraph` have DIFFERENT resolved classes — body-625's
∀-theorem applied to `phi4BubbleAmbient_edgeIdsUnique` + the Step-2 membership (purely combinatorial;
no CD/topology hypotheses enter). -/
theorem phi4BubbleNested_class_ne :
    phi4BubbleNested.boundaryCompletedResolvedGraph.toResolvedClass
      ≠ (rootRelativeInner phi4BubbleInner phi4BubbleNested).boundaryCompletedResolvedGraph.toResolvedClass :=
  phi4WTriplePrime_nestedLeft_class_ne_of_inheritedOuter
    phi4BubbleAmbient_edgeIdsUnique phi4BubbleInner phi4BubbleNested
    phi4BubbleNested_mem_inheritedOuter

/-! ## Step 4 — the ∃-no-go (HEADLINE) -/

/-- **body-665d (Step 4, HEADLINE) — the ∃-no-go.**  There EXISTS a concrete φ⁴ configuration —
an ambient graph with unique edge ids, a subgraph, a nested subgraph of its boundary completion, and
an inherited outer boundary edge — on which the naive nested boundary completion PROVABLY differs
from the root-relative one.  Body-625's obstruction (paper Thm 2) is INHABITED, not vacuous: witness
`(phi4BubbleAmbient, phi4BubbleInner, phi4BubbleNested, e2)`. -/
theorem exists_nested_completion_obstruction :
    ∃ (G : ResolvedFeynmanGraph) (γ : ResolvedFeynmanSubgraph G)
      (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
      (e : ResolvedFeynmanEdge),
      G.EdgeIdsUnique ∧ e ∈ inheritedOuter γ δ ∧
      δ.boundaryCompletedResolvedGraph.toResolvedClass
        ≠ (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass :=
  ⟨phi4BubbleAmbient, phi4BubbleInner, phi4BubbleNested, phi4BubbleEdge 2 0 2,
   phi4BubbleAmbient_edgeIdsUnique, phi4BubbleNested_mem_inheritedOuter,
   phi4BubbleNested_class_ne⟩

end GaugeGeometry.QFT.Combinatorial
