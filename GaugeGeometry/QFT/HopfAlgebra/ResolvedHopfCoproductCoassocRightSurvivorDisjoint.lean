import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbedSupport

/-!
# R-6c-heart-6a-3a — right survivor vertex disjointness (`hdisj`)

`survivorReembed` (6a-2) needs `hdisj : Disjoint γ.vertices A.vertices` for an actual right-primitive
component `γ` and `A = selectedOuterRaw`.  5b-2a gives the **pairwise** disjointness (`γ` disjoint from
every *distinct* component of `selectedOuterRaw`); the full vertex-set disjointness additionally needs
`γ ∉ selectedOuterRaw.elements`, which holds once `γ` is **nonempty**: `γ ∉ leftOf` (right-primitive is
not left-selected) and `γ ∉ promotedOf` (a promoted piece sits in a *different* parent, so coinciding
with `γ` would force `γ.vertices = ∅`).  Nonemptiness is the carrier-properness datum, taken here as a
hypothesis (`hne`).

Landed:

* `isRightPrimitive_not_mem_selectedOuterRaw` — a nonempty right-primitive component is not a selected-
  outer component;
* `isRightPrimitive_disjoint_vertices_selectedOuterRaw` — the full vertex disjointness `hdisj`;
* `rightSurvivorComponentOf` (+ `_gen`) — the concrete right survivor component, reduced to the
  per-component nonemptiness `hne` and the edge-domain bound `hcompl`.

No facade, no flat term, no `forgetHopf`, no rep/perm.  Discharging `hne` (nonemptiness) and `hcompl`
(the edge-domain `≤ complementEdges`) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-3a — a nonempty right-primitive component is not a selected-outer component.** -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_not_mem_selectedOuterRaw
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hR : s.isRightPrimitive γ) (hne : γ.1.vertices.Nonempty) :
    γ.1 ∉ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).elements := by
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
  rintro (hL | hP)
  · exact s.isRightPrimitive_not_mem_leftOf hR hL
  · have hP' : γ.1 ∈ s.promotedElements := hP
    obtain ⟨γP, hγP⟩ := s.mem_promotedElements hP'
    obtain ⟨B, hchoice⟩ := s.promotedComponentElements_choiceAt_inr hγP
    have hsub := s.promotedComponentElements_vertices_subset_parent hγP
    have hne_comp : γ.1 ≠ γP.1 := by
      intro heq
      have hγeq : γ = γP := Subtype.ext heq
      have hrp : s.choiceAt γ = Sum.inl false := hR
      subst hγeq
      rw [hrp] at hchoice
      simp at hchoice
    obtain ⟨v, hv⟩ := hne
    exact Finset.disjoint_left.mp (s.1.1.pairwiseDisjoint γ.2 γP.2 hne_comp) hv (hsub hv)

/-- **R-6c-heart-6a-3a — the right survivor vertex disjointness `hdisj`.**  A nonempty right-primitive
component is disjoint (as vertex sets) from the whole selected-outer forest. -/
theorem ResolvedCoassocSplitChoice.isRightPrimitive_disjoint_vertices_selectedOuterRaw
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (hR : s.isRightPrimitive γ) (hne : γ.1.vertices.Nonempty) :
    Disjoint γ.1.vertices ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).vertices := by
  rw [Finset.disjoint_left]
  intro v hvγ hvSO
  rw [ResolvedAdmissibleSubgraph.mem_vertices] at hvSO
  obtain ⟨δ, hδ, hvδ⟩ := hvSO
  by_cases hδγ : γ.1 = δ
  · subst hδγ
    exact s.isRightPrimitive_not_mem_selectedOuterRaw hR hne hδ
  · exact Finset.disjoint_left.mp (s.isRightPrimitive_disjoint_selectedOuterRaw hR hδ hδγ) hvγ hvδ

/-- **R-6c-heart-6a-3a — the concrete right survivor component.**  `survivorReembed` of a right-primitive
component into the selected-outer quotient graph, reduced to the per-component nonemptiness `hne` and the
edge-domain bound `hcompl`. -/
noncomputable def rightSurvivorComponentOf (s : ResolvedCoassocSplitChoice D G)
    (hne : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents},
      γ.1.1.vertices.Nonempty)
    (hcompl : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents},
      γ.1.1.internalEdges
        ≤ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    ResolvedFeynmanSubgraph s.selectedOuterContractGraph :=
  survivorReembed ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
    (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) γ.1.1
    (s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp γ.2).2 (hne γ))
    (hcompl γ)

/-- **R-6c-heart-6a-3a — the right survivor component has its component's own generator.** -/
theorem rightSurvivorComponentOf_gen (s : ResolvedCoassocSplitChoice D G)
    (hne : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents},
      γ.1.1.vertices.Nonempty)
    (hcompl : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents},
      γ.1.1.internalEdges
        ≤ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s).complementEdges)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents})
    (hCD : (rightSurvivorComponentOf s hne hcompl γ).forget.IsConnectedDivergent)
    (hCD' : γ.1.1.forget.IsConnectedDivergent) :
    resolvedComponentGen (rightSurvivorComponentOf s hne hcompl γ) hCD
      = resolvedComponentGen γ.1.1 hCD' := rfl

end GaugeGeometry.QFT.Combinatorial
