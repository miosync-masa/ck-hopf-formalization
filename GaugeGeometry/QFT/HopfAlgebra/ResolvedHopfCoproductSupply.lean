import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfSubgraphMapPerm

/-!
# R-6b-4 — concrete term-level coproduct supply (component product + quotient)

Instantiating `ResolvedCoproductForestSummandSupply` with the actual proper-forest summands:
`leftTerm A = ∏ γ ∈ A.elements, X (component gen of γ)` (the forest's component-generator product —
**not** a single generator, the algebra-level granularity), `rightTerm A = X (quotient gen of
A.contractWithStars starOf)`.  This file builds the component/forest/quotient generators and proves
their `mapPerm` invariance (feeding `sum_eq_of_bij` for `sum_mapPerm`).

Contents (R-6b-4a..d):
* `resolvedComponentGen` (+ `_mapPerm`) — component subgraph → resolved generator;
* `resolvedForestLeftTerm` (+ `_mapPerm`) — the forest's component-generator product (left factor);
* `resolvedForestRightTerm` (+ `_mapPerm`) — the quotient generator (right factor);
* `ResolvedCoproductProperForestData` — an equivariant proper-forest data family (carrier + star +
  contraction-CD, with the `mapPerm` equivariance), and `.toGenSupply : ResolvedCoproductGenSupply`
  (`sum_mapPerm` discharged via `sum_eq_of_bij` + the term invariances).  So from a proper-forest data
  family, `Δᵣ` (`.toGenSupply.gen`) and the algebra hom (`.toGenSupply.coproduct`) are fully
  constructed — facade-free, every factor a `ResolvedHopfGen`.  The actual enumeration filling the
  data is R-6b-5.
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

/-! ## R-6b-4d — bundle into a concrete equivariant `ResolvedCoproductGenSupply` -/

/-- A resolved admissible subgraph is determined by its element set. -/
theorem ResolvedAdmissibleSubgraph.ext_elements {A₁ A₂ : ResolvedAdmissibleSubgraph G}
    (h : A₁.elements = A₂.elements) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-- `ResolvedAdmissibleSubgraph.mapPerm σ` is injective. -/
theorem ResolvedAdmissibleSubgraph.mapPerm_injective (σ : Equiv.Perm VertexId) :
    Function.Injective (ResolvedAdmissibleSubgraph.mapPerm σ (G := G)) := by
  intro A₁ A₂ h
  apply ResolvedAdmissibleSubgraph.ext_elements
  refine Finset.image_injective (ResolvedFeynmanSubgraph.mapPerm_injective σ) ?_
  rw [← ResolvedAdmissibleSubgraph.mapPerm_elements, ← ResolvedAdmissibleSubgraph.mapPerm_elements, h]

/-- An equivariant family of proper-forest coproduct data: per graph a finite forest carrier with a
star assignment and the contraction CD, plus the `mapPerm` equivariance (carrier transports by
relabeling; the star assignment is `mapPerm`-natural).  This is the only remaining input to a
concrete `Δᵣ` — the actual proper-forest enumeration can fill it later (R-6b-5). -/
structure ResolvedCoproductProperForestData where
  /-- The finite forest carrier per graph. -/
  carrier : (G : ResolvedFeynmanGraph) → Finset (ResolvedAdmissibleSubgraph G)
  /-- The star assignment per forest. -/
  starOf : (G : ResolvedFeynmanGraph) → ResolvedAdmissibleSubgraph G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The contraction is connected divergent (the right factor is a generator). -/
  hCD : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G), A ∈ carrier G →
    ((A.contractWithStars (starOf G A)).forget.toClass.IsConnectedDivergent)
  /-- The carrier transports by relabeling. -/
  carrier_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    carrier (G.mapPerm σ) = (carrier G).image (fun A => A.mapPerm σ)
  /-- The forest right term is `mapPerm`-invariant (body-405: replaces the strict `star_mapPerm`, which body-403
  proved inconsistent with `starOf_fresh`; only the right-term class invariance is needed by `sum_mapPerm`). -/
  rightTerm_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) (hA : A ∈ carrier G)
    (hAσ : A.mapPerm σ ∈ carrier (G.mapPerm σ)),
    resolvedForestRightTerm A (starOf G A) (hCD G A hA)
      = resolvedForestRightTerm (A.mapPerm σ) (starOf (G.mapPerm σ) (A.mapPerm σ))
          (hCD (G.mapPerm σ) (A.mapPerm σ) hAσ)

/-- **R-6c-body-412 — the `rightTerm`-free raw core.**  The proper-forest data MINUS `rightTerm_mapPerm` — the honest
primitive on which the correcting-permutation geometry (bodies 407–411) actually depends (it reads only `starOf` /
`carrier`).  Building `rightTerm_mapPerm` from raw facts (freshness / injectivity / ambient support) and only THEN
assembling the full `D` breaks the definitional cycle that `ResolvedCanonicalStarFacts (completed D)` would otherwise
force. -/
structure ResolvedCoproductProperForestRawData where
  /-- The finite forest carrier per graph. -/
  carrier : (G : ResolvedFeynmanGraph) → Finset (ResolvedAdmissibleSubgraph G)
  /-- The star assignment per forest. -/
  starOf : (G : ResolvedFeynmanGraph) → ResolvedAdmissibleSubgraph G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The contraction is connected divergent (the right factor is a generator). -/
  hCD : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G), A ∈ carrier G →
    ((A.contractWithStars (starOf G A)).forget.toClass.IsConnectedDivergent)
  /-- The carrier transports by relabeling. -/
  carrier_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    carrier (G.mapPerm σ) = (carrier G).image (fun A => A.mapPerm σ)

/-- The raw core underlying a full `D` (drops only `rightTerm_mapPerm`). -/
def ResolvedCoproductProperForestData.toRaw (D : ResolvedCoproductProperForestData) :
    ResolvedCoproductProperForestRawData where
  carrier := D.carrier
  starOf := D.starOf
  hCD := D.hCD
  carrier_mapPerm := D.carrier_mapPerm

@[simp] theorem ResolvedCoproductProperForestData.toRaw_carrier (D : ResolvedCoproductProperForestData) :
    D.toRaw.carrier = D.carrier := rfl

@[simp] theorem ResolvedCoproductProperForestData.toRaw_starOf (D : ResolvedCoproductProperForestData) :
    D.toRaw.starOf = D.starOf := rfl

@[simp] theorem ResolvedCoproductProperForestData.toRaw_hCD (D : ResolvedCoproductProperForestData) :
    D.toRaw.hCD = D.hCD := rfl

@[simp] theorem ResolvedCoproductProperForestData.toRaw_carrier_mapPerm
    (D : ResolvedCoproductProperForestData) :
    D.toRaw.carrier_mapPerm = D.carrier_mapPerm := rfl

variable (D : ResolvedCoproductProperForestData)

/-- The summand supply from the forest data (`ForestIdx` = the carrier subtype, so the right term
gets its CD via membership). -/
noncomputable def ResolvedCoproductProperForestData.supply (G : ResolvedFeynmanGraph) :
    ResolvedCoproductForestSummandSupply G where
  ForestIdx := {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}
  forestCarrier := (D.carrier G).attach
  leftTerm := fun A => resolvedForestLeftTerm A.1
  rightTerm := fun A => resolvedForestRightTerm A.1 (D.starOf G A.1) (D.hCD G A.1 A.2)

/-- The forest sum is `mapPerm`-invariant (the `sum_mapPerm` obligation), via `sum_eq_of_bij` with the
landed left/right term invariances. -/
theorem ResolvedCoproductProperForestData.sum_mapPerm (G : ResolvedFeynmanGraph)
    (σ : Equiv.Perm VertexId) :
    (D.supply (G.mapPerm σ)).sum = (D.supply G).sum := by
  symm
  refine ResolvedCoproductForestSummandSupply.sum_eq_of_bij (D.supply G) (D.supply (G.mapPerm σ))
    (fun A _ => ⟨A.1.mapPerm σ, by
      rw [D.carrier_mapPerm]; exact Finset.mem_image_of_mem _ A.2⟩)
    (fun _ _ => Finset.mem_attach _ _) (fun A₁ _ A₂ _ h => ?_) (fun B _ => ?_)
    (fun A _ => ?_) (fun A _ => ?_)
  · exact Subtype.ext (ResolvedAdmissibleSubgraph.mapPerm_injective σ (Subtype.ext_iff.mp h))
  · obtain ⟨A, hA, hAeq⟩ := Finset.mem_image.mp
      (by simpa only [D.carrier_mapPerm] using B.2)
    exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, Subtype.ext hAeq⟩
  · exact resolvedForestLeftTerm_mapPerm A.1 σ
  · exact D.rightTerm_mapPerm G σ A.1 A.2
      (by rw [D.carrier_mapPerm]; exact Finset.mem_image_of_mem _ A.2)

/-- **R-6b-4d — a concrete equivariant `ResolvedCoproductGenSupply`** from proper-forest data, hence a
concrete `Δᵣ` (`.toGenSupply.coproduct`).  Given the proper-forest data family, the resolved-target
coproduct on `ResolvedHopfH` is fully constructed — facade-free, every factor a `ResolvedHopfGen`. -/
noncomputable def ResolvedCoproductProperForestData.toGenSupply : ResolvedCoproductGenSupply where
  supply := D.supply
  sum_mapPerm := D.sum_mapPerm

end GaugeGeometry.QFT.Combinatorial