import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# R-6c-body-262 — complement-edges monotonicity infra (PROVED)

Two-hundred-and-sixty-second genuine-body step — the reusable count/monotonicity infrastructure for the last
`IsProperForest` conjunct `0 < A.complementEdges.card` (body-261 verdict: global monotonicity, no deep leaf).  Three
lemmas, all shallow mirrors of the flat originals (`Coassoc.lean:3410`, `Coproduct.lean:3685/3721`):

```lean
complementEdges_card_pos_of_internalEdges_le : A.internalEdges ≤ B.internalEdges → 0 < B.complementEdges.card
                                                 → 0 < A.complementEdges.card
internalEdges_le_of_mem            : γ ∈ A.elements → γ.internalEdges ≤ A.internalEdges
internalEdges_le_of_components_le  : (∀ γ ∈ A.elements, γ.internalEdges ≤ M) → A.internalEdges ≤ M
```

The monotonicity core inlines `count_lt_of_mem_complementEdges` as `Multiset.mem_sub.mp` (since `complementEdges =
G.internalEdges - A.internalEdges`, `ResolvedSubGraph.lean:268`).  `internalEdges_le_of_mem` is `Finset.single_le_sum`
(each component's edge-count ≤ the aggregate sum — no disjointness needed).  `internalEdges_le_of_components_le` mirrors
the resolved `internalEdges_le` count argument (`ResolvedCoproductIndex.lean:165`): pairwise-disjoint components share
no edge, so the aggregate count at `e` is the single containing component's, bounded by `M`.

These are pure edge-count arithmetic; body-263 applies them (X via
`selectedOuterRawOf.internalEdges ≤ s.1.1.internalEdges`, Y via the partition transfer) to finish the conjunct.

Per the HALT: only the monotonicity infra is proved; no `selectedOuter` / `recovered` conjunct is assembled (body-263).
No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace ResolvedAdmissibleSubgraph

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-262 — complement-edge positivity is anti-monotone in internal edges.**  A forest with fewer internal
edges has a larger complement, so its complement stays positive. -/
theorem complementEdges_card_pos_of_internalEdges_le {A B : ResolvedAdmissibleSubgraph G}
    (hAB : A.internalEdges ≤ B.internalEdges) (hB : 0 < B.complementEdges.card) :
    0 < A.complementEdges.card := by
  classical
  rcases Multiset.card_pos_iff_exists_mem.mp hB with ⟨e, he⟩
  have heB : B.internalEdges.count e < G.internalEdges.count e := by
    rw [complementEdges, Multiset.mem_sub] at he; exact he
  refine Multiset.card_pos_iff_exists_mem.mpr ⟨e, ?_⟩
  rw [complementEdges, Multiset.mem_sub]
  exact lt_of_le_of_lt (Multiset.count_le_of_le e hAB) heB

/-- **R-6c-body-262 — a component's internal edges are ≤ the aggregate** (`Finset.single_le_sum`, no disjointness). -/
theorem internalEdges_le_of_mem (A : ResolvedAdmissibleSubgraph G) {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ A.elements) : γ.internalEdges ≤ A.internalEdges := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  show γ.internalEdges.count e ≤ (∑ x ∈ A.elements, x.internalEdges).count e
  rw [multiset_count_finset_sum]
  exact Finset.single_le_sum (f := fun x => Multiset.count e x.internalEdges)
    (fun i _ => Nat.zero_le _) hγ

/-- **R-6c-body-262 — the aggregate internal edges are bounded by any bound on every component** (pairwise-disjoint
components share no edge, so the aggregate count at `e` is the unique containing component's). -/
theorem internalEdges_le_of_components_le (A : ResolvedAdmissibleSubgraph G)
    {M : Multiset ResolvedFeynmanEdge} (hComp : ∀ γ ∈ A.elements, γ.internalEdges ≤ M) :
    A.internalEdges ≤ M := by
  classical
  rw [Multiset.le_iff_count]
  intro e
  by_cases heA : e ∈ A.internalEdges
  · obtain ⟨γ, hγ, heγ⟩ := mem_internalEdges.mp heA
    have hzero : ∀ δ ∈ A.elements, δ ≠ γ → δ.internalEdges.count e = 0 := by
      intro δ hδ hne
      by_cases heδ : e ∈ δ.internalEdges
      · have hdisj : _root_.Disjoint δ.vertices γ.vertices := A.pairwiseDisjoint hδ hγ hne
        obtain ⟨hsδ, _⟩ := δ.edges_supported e heδ
        obtain ⟨hsγ, _⟩ := γ.edges_supported e heγ
        exact absurd hsγ (Finset.disjoint_left.mp hdisj hsδ)
      · exact Multiset.count_eq_zero.mpr heδ
    show (∑ x ∈ A.elements, x.internalEdges).count e ≤ M.count e
    rw [multiset_count_finset_sum,
      Finset.sum_eq_single γ (fun δ hδ hne => hzero δ hδ hne) (fun hγnot => absurd hγ hγnot)]
    exact Multiset.count_le_of_le e (hComp γ hγ)
  · rw [Multiset.count_eq_zero.mpr heA]; exact Nat.zero_le _

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
