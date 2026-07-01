import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductDisjointLeaves

/-!
# R-6c-leaf-12 — Product `hCross` + `hDisj` from ONE unconditional vertex-cross

Eighth leaf-body discharge.  Since `ResolvedFeynmanSubgraph.Disjoint γ δ` is *by definition*
`Disjoint γ.vertices δ.vertices` (ResolvedSubGraph:100), the remnant / right-survivor separation is really
one **unconditional vertex-cross** — every remnant element is vertex-disjoint from every survivor element,
with no `≠` guard.  From it BOTH Product leaves follow:

* `hCross` — drop the (now redundant) `≠` guard;
* `hDisj` — the `Finset`-disjointness: a shared element `δ` would be self-vertex-disjoint, so empty,
  contradicting nonemptiness of the survivor forest elements.

This is a stronger, cleaner route than leaf-4's `≠`-guarded cross supply (which gave only `hCross`).

Per the HALT, `vertex_cross` (the disjoint-region geometry) is a supply field; the survivor-element
nonemptiness is a hypothesis (mirrors leaf-10/11); `hPD` untouched.

Landed:

* `finset_disjoint_of_vertex_cross_nonempty` — the generic `Finset`-disjointness engine;
* `ResolvedQuotientForestVertexCrossSupply D G R M` — the `vertex_cross` field;
* `.hCross` (guard-free) and `.hDisj` (with nonemptiness).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false in
/-- **R-6c-leaf-12 — the generic `Finset`-disjointness engine.**  If every `A`-element is `Disjoint` (i.e.
vertex-disjoint) from every `B`-element and every `B`-element has nonempty vertices, then `A` and `B` share
no element. -/
theorem finset_disjoint_of_vertex_cross_nonempty {A B : Finset (ResolvedFeynmanSubgraph G)}
    (hcross : ∀ γ ∈ A, ∀ δ ∈ B, γ.Disjoint δ)
    (hne : ∀ δ ∈ B, δ.vertices.Nonempty) :
    Disjoint A B := by
  classical
  rw [Finset.disjoint_left]
  intro δ hδA hδB
  obtain ⟨v, hv⟩ := hne δ hδB
  exact (Finset.disjoint_left.mp (hcross δ hδA δ hδB) hv) hv

/-- **R-6c-leaf-12 — the quotient-forest vertex-cross supply.**  The unconditional vertex-disjointness of
remnant and right-survivor forest elements (disjoint regions of the quotient graph). -/
structure ResolvedQuotientForestVertexCrossSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- Every remnant element is vertex-disjoint from every right-survivor element (no `≠` guard). -/
  vertex_cross : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements, γ.Disjoint δ

variable {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}

/-- **R-6c-leaf-12 — the Product `hCross` leaf (guard-free vertex-cross). -/
theorem ResolvedQuotientForestVertexCrossSupply.hCross
    (V : ResolvedQuotientForestVertexCrossSupply D G R M) :
    ∀ (s : ResolvedCoassocSplitChoice D G),
      ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
        γ ≠ δ → γ.Disjoint δ :=
  fun s γ hγ δ hδ _ => V.vertex_cross s γ hγ δ hδ

/-- **R-6c-leaf-12 — the Product `hDisj` leaf from the vertex-cross + survivor-element nonemptiness. -/
theorem ResolvedQuotientForestVertexCrossSupply.hDisj
    (V : ResolvedQuotientForestVertexCrossSupply D G R M)
    (hne : ∀ (s : ResolvedCoassocSplitChoice D G),
      ∀ δ ∈ (R.rightSurvivorForest s).elements, δ.vertices.Nonempty) :
    ∀ s : ResolvedCoassocSplitChoice D G,
      Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements :=
  fun s => finset_disjoint_of_vertex_cross_nonempty (V.vertex_cross s) (hne s)

end GaugeGeometry.QFT.Combinatorial
