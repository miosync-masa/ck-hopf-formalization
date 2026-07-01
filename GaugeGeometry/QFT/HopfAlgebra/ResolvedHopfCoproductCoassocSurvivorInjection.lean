import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductInjectionLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSurvivor

/-!
# R-6c-leaf-8 — Product `survivorInj` PROVED from the concrete survivor re-embedding

Sixth leaf-body discharge.  `ResolvedProductInjectionSupply.survivorInj` is proved for the concrete
right-survivor supply (6a-3c): the survivor of a right-primitive component is `survivorReembedOfDisjoint`,
which keeps `γ`'s intrinsic resolved graph (`survivorReembed_toResolvedFeynmanGraph = rfl`).  So equal
survivors have equal `toResolvedFeynmanGraph`, hence equal vertices/edges/legs, hence equal components
(`ResolvedFeynmanSubgraph.ext`), hence equal indices (`Subtype.ext` twice — the `rightComponents`-membership
and `elements`-membership proofs are irrelevant).

Per the HALT, `remnantInj` is NOT proved; no disjoint / connector leaves.

Landed:

* `product_survivorInj_of_concreteSurvivor` — the `survivorInj` leaf for `resolvedConcreteRightSurvivorSupply`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-8 — the Product `survivorInj` leaf from the concrete right-survivor supply.**  Distinct
right-primitive components have distinct survivor embeddings: the re-embedding keeps the component's
intrinsic resolved graph, so an equality of survivors forces the components equal. -/
theorem product_survivorInj_of_concreteSurvivor
    (hne : ∀ (s : ResolvedCoassocSplitChoice D G)
      (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
      γ.1.1.vertices.Nonempty)
    (s : ResolvedCoassocSplitChoice D G) :
    ∀ γ₁ ∈ s.rightComponents.attach, ∀ γ₂ ∈ s.rightComponents.attach,
      (resolvedConcreteRightSurvivorSupply D G hne).survivorComponent s γ₁
        = (resolvedConcreteRightSurvivorSupply D G hne).survivorComponent s γ₂ → γ₁ = γ₂ := by
  intro γ₁ _ γ₂ _ heq
  apply Subtype.ext
  apply Subtype.ext
  have h := congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph heq
  have hG : γ₁.1.1.toResolvedFeynmanGraph = γ₂.1.1.toResolvedFeynmanGraph := h
  exact ResolvedFeynmanSubgraph.ext
    (congrArg (·.vertices) hG) (congrArg (·.internalEdges) hG) (congrArg (·.externalLegs) hG)

end GaugeGeometry.QFT.Combinatorial
