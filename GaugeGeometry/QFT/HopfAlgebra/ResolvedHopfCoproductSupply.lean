import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm

/-!
# R-6b-4 — concrete term-level coproduct supply (component product + quotient)

Instantiating `ResolvedCoproductForestSummandSupply` with the actual proper-forest summands:
`leftTerm A = ∏ γ ∈ A.elements, X (component gen of γ)` (the forest's component-generator product —
**not** a single generator, the algebra-level granularity), `rightTerm A = X (quotient gen of
A.contractWithStars starOf)`.  This file builds the component/forest/quotient generators and proves
their `mapPerm` invariance (feeding `sum_eq_of_bij` for `sum_mapPerm`).

R-6b-4a (here): the component subgraph → resolved generator bridge `resolvedComponentGen` and its
`mapPerm` invariance.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable {G : ResolvedFeynmanGraph}
  [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- A connected-divergent component subgraph as a resolved Hopf generator (the component viewed as a
standalone resolved graph, ids kept).  CD of the flat shadow is lifted from the subgraph-level CD via
`toFeynmanGraph_isConnectedDivergent`. -/
noncomputable def resolvedComponentGen (γ : ResolvedFeynmanSubgraph G)
    (hCD : γ.forget.IsConnectedDivergent) : ResolvedHopfGen :=
  γ.toResolvedFeynmanGraph.toResolvedHopfGen (by
    show (γ.toResolvedFeynmanGraph).forget.toClass.IsConnectedDivergent
    rw [← ResolvedFeynmanSubgraph.forget_toFeynmanGraph γ]
    exact (FeynmanGraphClass.isConnectedDivergent_toClass _).mpr
      (γ.forget.toFeynmanGraph_isConnectedDivergent hCD))

/-- The component generator is `mapPerm`-invariant: relabeling a component gives the same resolved
generator (the component-as-graph relabels, and its class is `mapPerm`-invariant). -/
theorem resolvedComponentGen_mapPerm (γ : ResolvedFeynmanSubgraph G) (σ : Equiv.Perm VertexId)
    (hCD : γ.forget.IsConnectedDivergent)
    (hCD' : (γ.mapPerm σ).forget.IsConnectedDivergent) :
    resolvedComponentGen (γ.mapPerm σ) hCD' = resolvedComponentGen γ hCD := by
  apply Subtype.ext
  show (γ.mapPerm σ).toResolvedFeynmanGraph.toResolvedClass
     = γ.toResolvedFeynmanGraph.toResolvedClass
  exact ResolvedFeynmanGraph.toResolvedClass_mapPerm γ.toResolvedFeynmanGraph σ

end GaugeGeometry.QFT.Combinatorial
