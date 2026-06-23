import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelect
import GaugeGeometry.QFT.HopfAlgebra.ResolvedSubgraphPromote

/-!
# R-6c-heart-4 P2 — `promotedOf` biUnion assembly

With the resolved promote (P1) in hand, the promoted forest of a split choice is assembled by the
biUnion over the input outer forest's components: for each component `γ` whose local choice is
`Sum.inr B` (a sub-forest choice `B` of the component graph `γ.toResolvedFeynmanGraph`, since
`(D.supply (γ.toResolvedFeynmanGraph)).ForestIdx = {A // A ∈ D.carrier (γ.toResolvedFeynmanGraph)}`),
include the promoted components `(ResolvedAdmissibleSubgraph.promote γ B.1).elements`; otherwise nothing.

Per the HALT, the admissibility of the resulting component set (CD + pairwise-disjointness, the P3/P4
work) is kept as **supply fields**; only the element set (`promotedElements`) is built concretely here,
and `promotedOf` is `ofElements promotedElements` against those fields.

Landed:

* `ResolvedCoassocSplitChoice.choiceAt` — the local choice at a component (the dependent `s.2`, with the
  trivial `mem_attach`);
* `ResolvedCoassocSplitChoice.promotedComponentElements` — the per-component promoted set
  (`∅` on a primitive choice, promoted components on a forest choice) (+ `_inr` reduction);
* `ResolvedCoassocSplitChoice.promotedElements` (+ `mem_promotedElements`) — the biUnion over components;
* `ResolvedPromotedOfSupply D G` (CD + disjoint fields) + `.promotedOf` (`ofElements promotedElements`) +
  `.toForestPromoteSupply` (assemble the full `ResolvedForestPromoteSupply` from a left selection + a
  supplied cross-disjointness).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The CD/disjoint/cross proofs (P3/P4) and the
carrier membership (P5) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-4 P2 — the local choice at a component.**  The dependent second projection `s.2`
evaluated at a component `γ` of the input outer forest (the `mem_attach` is trivial). -/
noncomputable def ResolvedCoassocSplitChoice.choiceAt (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) :
    Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx :=
  s.2 γ (Finset.mem_attach _ γ)

/-- **R-6c-heart-4 P2 — the promoted components contributed by one component.**  On a primitive (`inl`)
choice, nothing; on a forest (`inr B`) choice, the promoted components of the chosen sub-forest `B.1` of
the component graph. -/
noncomputable def ResolvedCoassocSplitChoice.promotedComponentElements
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) :
    Finset (ResolvedFeynmanSubgraph G) :=
  match s.choiceAt γ with
  | Sum.inl _ => ∅
  | Sum.inr B => (ResolvedAdmissibleSubgraph.promote γ.1 B.1).elements

/-- On a forest choice, the per-component promoted set is the promoted sub-forest's components. -/
theorem ResolvedCoassocSplitChoice.promotedComponentElements_inr
    (s : ResolvedCoassocSplitChoice D G)
    {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    {B : (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx} (h : s.choiceAt γ = Sum.inr B) :
    s.promotedComponentElements γ = (ResolvedAdmissibleSubgraph.promote γ.1 B.1).elements := by
  unfold ResolvedCoassocSplitChoice.promotedComponentElements
  rw [h]

/-- **R-6c-heart-4 P2 — the promoted forest's component set.**  The biUnion over the input outer forest's
components of their per-component promoted sets — the resolved
`forestComponentChoicePromotedForestComponents`. -/
noncomputable def ResolvedCoassocSplitChoice.promotedElements
    (s : ResolvedCoassocSplitChoice D G) : Finset (ResolvedFeynmanSubgraph G) :=
  s.1.1.elements.attach.biUnion s.promotedComponentElements

/-- A promoted component comes from some input outer component's per-component promoted set. -/
theorem ResolvedCoassocSplitChoice.mem_promotedElements {s : ResolvedCoassocSplitChoice D G}
    {δ : ResolvedFeynmanSubgraph G} (hδ : δ ∈ s.promotedElements) :
    ∃ γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}, δ ∈ s.promotedComponentElements γ := by
  obtain ⟨γ, -, hδ⟩ := Finset.mem_biUnion.mp hδ
  exact ⟨γ, hδ⟩

/-- **R-6c-heart-4 P2 — the promoted-forest admissibility supply.**  The connected-divergence and
pairwise-disjointness of the promoted component set, kept as supply fields (the P3/P4 work). -/
structure ResolvedPromotedOfSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- Every promoted component is connected-divergent. -/
  promotedCD : ∀ s : ResolvedCoassocSplitChoice D G, ∀ δ ∈ s.promotedElements,
    δ.forget.IsConnectedDivergent
  /-- The promoted components are pairwise disjoint. -/
  promotedDisjoint : ∀ s : ResolvedCoassocSplitChoice D G, ∀ ⦃γ⦄, γ ∈ s.promotedElements →
    ∀ ⦃δ⦄, δ ∈ s.promotedElements → γ ≠ δ → γ.Disjoint δ

/-- **R-6c-heart-4 P2 — the promoted forest.**  `ofElements` of the concrete `promotedElements` against
the supplied CD + disjoint. -/
noncomputable def ResolvedPromotedOfSupply.promotedOf (P : ResolvedPromotedOfSupply D G)
    (s : ResolvedCoassocSplitChoice D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements s.promotedElements (P.promotedCD s) (P.promotedDisjoint s)

@[simp] theorem ResolvedPromotedOfSupply.promotedOf_elements (P : ResolvedPromotedOfSupply D G)
    (s : ResolvedCoassocSplitChoice D G) : (P.promotedOf s).elements = s.promotedElements := rfl

/-- **R-6c-heart-4 P2 — assemble the forest-promote supply.**  Combine a left-selection supply (concrete
`leftOf`) with this promoted forest and a supplied cross-disjointness into the full
`ResolvedForestPromoteSupply` (whose `selectedOuterRawOf` is `leftOf ∪ promotedOf`). -/
noncomputable def ResolvedPromotedOfSupply.toForestPromoteSupply (P : ResolvedPromotedOfSupply D G)
    (L : ResolvedSplitChoiceLeftSelectionSupply D G)
    (cross : ∀ s, ∀ γ ∈ (L.leftOf s).elements, ∀ δ ∈ (P.promotedOf s).elements,
        γ ≠ δ → γ.Disjoint δ) :
    ResolvedForestPromoteSupply D G :=
  L.toPromoteSupply P.promotedOf cross

end GaugeGeometry.QFT.Combinatorial
