import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf

/-!
# R-6c-heart-4 P3 — `promotedCD` (the promoted components are connected-divergent)

The CD half of the promoted-forest admissibility.  A promoted component `δ` comes (via the P2 biUnion)
from some input outer component `γ` with a forest choice `Sum.inr B`, as `δ = γ.promote δ₀` for a
component `δ₀` of the chosen sub-forest `B.1` of the component graph.  Then `δ₀` is connected-divergent
(it is a component of the admissible forest `B.1`), and the P1 promote transports connected-divergence
(`promote_forget_isConnectedDivergent`).  So `promotedCD` is **proved**, removing it from the supply.

Landed:

* `ResolvedCoassocSplitChoice.promotedComponentElements_inl` — the per-component set is empty on a
  primitive choice;
* `ResolvedCoassocSplitChoice.promotedComponentElements_CD` / `promotedElements_CD` — the promoted
  components are connected-divergent (per-component, then global via the biUnion);
* `ResolvedPromotedOfSupply.ofDisjoint` — build the promoted supply from ONLY the disjointness (CD is now
  discharged).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The disjointness (P4) and carrier membership (P5)
are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- On a primitive (`inl`) choice, the per-component promoted set is empty. -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_inl
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}} {b : Bool}
    (h : s.choiceAt γ = Sum.inl b) : s.promotedComponentElements γ = ∅ := by
  unfold ResolvedCoassocSplitChoice.promotedComponentElements
  rw [h]

/-- **R-6c-heart-4 P3 — per-component CD.**  Every component contributed to `promotedElements` by one
input outer component is connected-divergent: on a forest choice it is `γ.promote δ₀` for a component
`δ₀` of the chosen sub-forest `B.1` (CD via `B.1.isConnectedDivergent` + the P1 promote transport). -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_CD
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}} {δ : ResolvedFeynmanSubgraph G}
    (hδ : δ ∈ s.promotedComponentElements γ) : δ.forget.IsConnectedDivergent := by
  rcases hc : s.choiceAt γ with b | B
  · rw [s.promotedComponentElements_inl hc] at hδ
    simp at hδ
  · rw [s.promotedComponentElements_inr hc] at hδ
    exact (ResolvedAdmissibleSubgraph.promote γ.1 B.1).isConnectedDivergent δ hδ

/-- **R-6c-heart-4 P3 — global CD.**  Every promoted component is connected-divergent. -/
theorem ResolvedCoassocSplitChoice.promotedElements_CD (s : ResolvedCoassocSplitChoice D G) :
    ∀ δ ∈ s.promotedElements, δ.forget.IsConnectedDivergent := by
  intro δ hδ
  obtain ⟨γ, hδ'⟩ := s.mem_promotedElements hδ
  exact s.promotedComponentElements_CD hδ'

/-- **R-6c-heart-4 P3 — the promoted supply from disjointness alone.**  Since `promotedCD` is now proved
(`promotedElements_CD`), the promoted-forest supply needs ONLY the pairwise-disjointness. -/
def ResolvedPromotedOfSupply.ofDisjoint
    (promotedDisjoint : ∀ s : ResolvedCoassocSplitChoice D G, ∀ ⦃γ⦄, γ ∈ s.promotedElements →
      ∀ ⦃δ⦄, δ ∈ s.promotedElements → γ ≠ δ → γ.Disjoint δ) :
    ResolvedPromotedOfSupply D G where
  promotedCD := fun s => s.promotedElements_CD
  promotedDisjoint := promotedDisjoint

end GaugeGeometry.QFT.Combinatorial
