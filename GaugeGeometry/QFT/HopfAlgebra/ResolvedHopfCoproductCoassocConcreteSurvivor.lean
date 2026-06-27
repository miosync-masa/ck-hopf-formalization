import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSurvivorEmbedComplement

/-!
# R-6c-heart-6a-3c — the concrete right survivor supply

Assembles `ResolvedRightSurvivorSupply` from `survivorReembedOfDisjoint` (6a-3b), depending only on a
per-component **nonemptiness** datum `rightComponentNonempty` (the carrier-properness fact that gives the
vertex disjointness `hdisj`, 6a-3a; everything else is structural):

* `survivorComponent` — the re-embedded right-primitive component;
* `survivorCD` — its connected-divergence (same intrinsic graph as the input component, so
  `IsConnected`/`IsOnePI` are defeq and `IsDivergent` transports by ambient invariance, as for `promote`);
* `survivorDisjoint` — pairwise disjointness (the re-embedding keeps vertices, so it is the input outer
  forest's pairwise disjointness).

Landed:

* `reembed_forget_isConnectedDivergent` — the re-embedding transports connected-divergence;
* `resolvedConcreteRightSurvivorSupply` — the concrete `ResolvedRightSurvivorSupply` (modulo
  nonemptiness), whose `survivorComponent` has its component's own generator
  (`resolvedComponentGen_survivorReembedOfDisjoint`).

No facade, no flat term, no `forgetHopf`, no rep/perm.  Discharging the nonemptiness (carrier-properness)
and the remnant embedding are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-3c — the re-embedding transports connected-divergence.**  Same intrinsic graph
(`reembed_forget_toFeynmanGraph`), so `IsConnected`/`IsOnePI` are defeq and `IsDivergent` transports via
`IsAmbientInvariantDivergence.degree_self_eq` — exactly the `promote` argument. -/
theorem reembed_forget_isConnectedDivergent {G H : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (hv : γ.vertices ⊆ H.vertices)
    (hi : γ.internalEdges ≤ H.internalEdges) (hl : γ.externalLegs ≤ H.externalLegs)
    (h : γ.forget.IsConnectedDivergent) : (γ.reembed hv hi hl).forget.IsConnectedDivergent := by
  refine ⟨h.1, h.2.1, ?_⟩
  have hdeg : DivergenceMeasure.degree ((γ.reembed hv hi hl).forget)
      = DivergenceMeasure.degree (γ.forget) := by
    rw [← IsAmbientInvariantDivergence.degree_self_eq ((γ.reembed hv hi hl).forget),
      ← IsAmbientInvariantDivergence.degree_self_eq (γ.forget)]
    rfl
  show 0 ≤ FeynmanSubgraph.divergenceDegree _
  unfold FeynmanSubgraph.divergenceDegree
  rw [hdeg]
  exact h.2.2

/-- **R-6c-heart-6a-3c — the concrete right survivor supply.**  Built from `survivorReembedOfDisjoint`,
depending only on the per-component nonemptiness `rightComponentNonempty` (which gives `hdisj`). -/
noncomputable def resolvedConcreteRightSurvivorSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (rightComponentNonempty : ∀ (s : ResolvedCoassocSplitChoice D G)
      (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
      γ.1.1.vertices.Nonempty) :
    ResolvedRightSurvivorSupply D G where
  survivorComponent := fun s γ =>
    survivorReembedOfDisjoint ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)
      (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) γ.1.1
      (s.isRightPrimitive_disjoint_vertices_selectedOuterRaw (Finset.mem_filter.mp γ.2).2
        (rightComponentNonempty s γ))
  survivorCD := fun s γ =>
    reembed_forget_isConnectedDivergent γ.1.1 _ _ _ (s.1.1.isConnectedDivergent γ.1.1 γ.1.2)
  survivorDisjoint := fun s => by
    intro δ hδ δ' hδ' hne_dd
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ
    obtain ⟨γ', -, rfl⟩ := Finset.mem_image.mp hδ'
    by_cases hcc : γ.1.1 = γ'.1.1
    · exact absurd (ResolvedFeynmanSubgraph.ext
        (by show γ.1.1.vertices = γ'.1.1.vertices; rw [hcc])
        (by show γ.1.1.internalEdges = γ'.1.1.internalEdges; rw [hcc])
        (by show γ.1.1.externalLegs = γ'.1.1.externalLegs; rw [hcc])) hne_dd
    · exact s.1.1.pairwiseDisjoint γ.1.2 γ'.1.2 hcc

end GaugeGeometry.QFT.Combinatorial
