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

open scoped TensorProduct Classical

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

/-! ## R-6b-4b — the forest left term (component-generator product) -/

/-- The left tensor factor of a forest summand: the **product of the component generators** of the
forest `A` (the algebra-level granularity — not collapsed to one generator). -/
noncomputable def resolvedForestLeftTerm (A : ResolvedAdmissibleSubgraph G) : ResolvedHopfH :=
  ∏ γ ∈ A.elements.attach, MvPolynomial.X (resolvedComponentGen γ.1 (A.isConnectedDivergent γ.1 γ.2))

/-- The forest left term is `mapPerm`-invariant: relabeling the forest permutes its components by
`mapPerm`, each of which has an invariant generator (`resolvedComponentGen_mapPerm`), so the product
is unchanged. -/
theorem resolvedForestLeftTerm_mapPerm (A : ResolvedAdmissibleSubgraph G) (σ : Equiv.Perm VertexId) :
    resolvedForestLeftTerm A = resolvedForestLeftTerm (A.mapPerm σ) := by
  unfold resolvedForestLeftTerm
  refine Finset.prod_bij
    (fun γ _ => ⟨γ.1.mapPerm σ, by
      rw [ResolvedAdmissibleSubgraph.mapPerm_elements]; exact Finset.mem_image_of_mem _ γ.2⟩)
    (fun γ _ => Finset.mem_attach _ _) (fun γ₁ _ γ₂ _ h => ?_) (fun γ' _ => ?_)
    (fun γ _ => ?_)
  · exact Subtype.ext (ResolvedFeynmanSubgraph.mapPerm_injective σ (Subtype.ext_iff.mp h))
  · obtain ⟨δ, hδ, hδeq⟩ := Finset.mem_image.mp
      (by simpa only [ResolvedAdmissibleSubgraph.mapPerm_elements] using γ'.2)
    exact ⟨⟨δ, hδ⟩, Finset.mem_attach _ _, Subtype.ext hδeq⟩
  · exact congrArg MvPolynomial.X
      (resolvedComponentGen_mapPerm γ.1 σ (A.isConnectedDivergent γ.1 γ.2) _).symm

/-! ## R-6b-4c — the forest right term (quotient generator) -/

/-- The right tensor factor of a forest summand: the generator of the star-contraction quotient
`A.contractWithStars starOf` (a single connected-divergent resolved graph). -/
noncomputable def resolvedForestRightTerm (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : (A.contractWithStars starOf).forget.toClass.IsConnectedDivergent) : ResolvedHopfH :=
  MvPolynomial.X ((A.contractWithStars starOf).toResolvedHopfGen hCD)

/-- The forest right term is `mapPerm`-invariant: the contraction of the relabeled forest has the
same resolved class (`mapPerm_contractWithStars_toResolvedClass`). -/
theorem resolvedForestRightTerm_mapPerm (A : ResolvedAdmissibleSubgraph G)
    (σ : Equiv.Perm VertexId)
    {starOf : ResolvedFeynmanSubgraph G → VertexId}
    {starOf' : ResolvedFeynmanSubgraph (G.mapPerm σ) → VertexId}
    (hstar : ∀ γ ∈ A.elements, starOf' (γ.mapPerm σ) = σ (starOf γ))
    (hCD : (A.contractWithStars starOf).forget.toClass.IsConnectedDivergent)
    (hCD' : ((A.mapPerm σ).contractWithStars starOf').forget.toClass.IsConnectedDivergent) :
    resolvedForestRightTerm A starOf hCD
      = resolvedForestRightTerm (A.mapPerm σ) starOf' hCD' := by
  unfold resolvedForestRightTerm
  refine congrArg MvPolynomial.X (Subtype.ext ?_)
  show (A.contractWithStars starOf).toResolvedClass
     = ((A.mapPerm σ).contractWithStars starOf').toResolvedClass
  exact (ResolvedAdmissibleSubgraph.mapPerm_contractWithStars_toResolvedClass σ A hstar).symm

end GaugeGeometry.QFT.Combinatorial
