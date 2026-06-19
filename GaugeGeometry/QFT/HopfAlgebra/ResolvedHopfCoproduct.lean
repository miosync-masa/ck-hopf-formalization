import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCarrier

/-!
# R-6b-1 — resolved-target coproduct generator scaffold

This file fixes the **shape** of the resolved-native coproduct on generators,
`Δᵣ : ResolvedHopfH →ₐ[ℚ] ResolvedHopfH ⊗ ResolvedHopfH`, **without** yet proving the
quotient well-definedness (that is R-6b-2) and **without** the full proper-forest
enumeration.

The decisive design constraint is the codomain: every tensor factor is a
`ResolvedHopfGen` (an id-preserving class), *not* a flat `HopfGen`.  That is what lets
R-6c plug in the facade-free `h58_resolved_carrier_double_sum_reindex` (the quotient
index is now id-bearing, so the R-5 `hQuotBij` wall dissolves).

Landed here:

* `ResolvedFeynmanGraph.toResolvedHopfGen` — a connected-divergent resolved graph as a
  resolved generator (the right-factor constructor, ids kept);
* `resolvedCoproductGenPrimitive` — the primitive part `X x ⊗ 1 + 1 ⊗ X x`, well defined
  on the generator `x` directly (no representative needed);
* `ResolvedCoproductForestSummandSupply` — the forest-sum **as a supplied finite family of
  resolved (left, right) algebra-term pairs** (left = the forest's component-generator product,
  NOT a single generator), with its sum `∑ leftTerm A ⊗ rightTerm A`;
* `resolvedCoproductGenOfGraph` — the representative-level generator formula
  (primitive + forest sum);
* `ResolvedCoproductGenWellDef` — the **isolated well-definedness obligation**
  (`mapPerm_invariant`).

R-6b-3 then discharges the lift: given a `mapPerm`-equivariant forest-summand supply family
(`ResolvedCoproductGenSupply`, one field `sum_mapPerm` — the R-6b-2e geometry through
`sum_eq_of_bij`), the forest sum descends through `ResolvedFeynmanGraphClass` by `Quotient.liftOn`,
and `Δᵣ` on generators (`ResolvedCoproductGenSupply.gen`) and the algebra hom
(`ResolvedCoproductGenSupply.coproduct : ResolvedHopfH →ₐ[ℚ] ResolvedHopfH ⊗ ResolvedHopfH`) are
defined — every tensor factor a `ResolvedHopfGen`.  No coassociativity, no flat `HopfGen` in the
codomain, no gated theorem, no `sorry`.  The only remaining input is a *concrete* equivariant supply
(R-6b-4); the geometric `sum_mapPerm` ingredients are all landed.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]

/-! ## Graph → resolved generator (the id-keeping right factor) -/

/-- A connected-divergent resolved graph, as a resolved Hopf generator.  Its class retains
the persistent edge/leg ids; only its **flat shadow** must be connected divergent. -/
noncomputable def ResolvedFeynmanGraph.toResolvedHopfGen
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    ResolvedHopfGen :=
  Subtype.mk G.toResolvedClass hCD

@[simp] theorem ResolvedFeynmanGraph.toResolvedHopfGen_val
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    (G.toResolvedHopfGen hCD).val = G.toResolvedClass := rfl

/-- The flat shadow of `G.toResolvedHopfGen` is exactly the flat generator of `G.forget`. -/
@[simp] theorem ResolvedFeynmanGraph.forget_toResolvedHopfGen
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    (G.toResolvedHopfGen hCD).forget = ⟨G.forget.toClass, hCD⟩ := rfl

/-- **R-6b-2d — the resolved generator is `mapPerm`-invariant.**  A relabeled graph yields the same
resolved generator (the class is `mapPerm`-invariant, `toResolvedClass_mapPerm`; the differing CD
proofs are irrelevant by `Subtype.ext`). -/
theorem ResolvedFeynmanGraph.toResolvedHopfGen_mapPerm (G : ResolvedFeynmanGraph)
    (σ : Equiv.Perm VertexId)
    (hCD : G.forget.toClass.IsConnectedDivergent)
    (hCD' : (G.mapPerm σ).forget.toClass.IsConnectedDivergent) :
    (G.mapPerm σ).toResolvedHopfGen hCD' = G.toResolvedHopfGen hCD :=
  Subtype.ext (ResolvedFeynmanGraph.toResolvedClass_mapPerm G σ)

/-! ## The primitive part (well defined on the generator directly) -/

/-- The primitive part of the resolved coproduct on a generator: `X x ⊗ 1 + 1 ⊗ X x`.
Defined on `x : ResolvedHopfGen` directly — no representative choice, hence no
well-definedness obligation. -/
noncomputable def resolvedCoproductGenPrimitive (x : ResolvedHopfGen) :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  MvPolynomial.X x ⊗ₜ[ℚ] (1 : ResolvedHopfH) + (1 : ResolvedHopfH) ⊗ₜ[ℚ] MvPolynomial.X x

/-! ## The forest-sum part as a supplied finite family

The forest sum is supplied as a finite family of resolved `(left, right)` **terms** in
`ResolvedHopfH ⊗ ResolvedHopfH`.  Crucially the factors are *terms* (`ResolvedHopfH`), **not** single
generators: the left factor of a CK forest summand is the **product of its connected-divergent
component generators** (`A.toHopfH = ∏ γ ∈ A.elements, gen γ`), which collapses to one generator only
for a single-component forest.  Keeping `leftTerm`/`rightTerm` at the algebra level avoids that
collapse (the algebra analogue of the "don't discard granularity" lesson).  Every factor still lives
in the resolved-generator algebra `ResolvedHopfH`, pinning the id-preserving target. -/

/-- A finite family of resolved coproduct forest summands for a representative graph `G`: each index
contributes `leftTerm A ⊗ rightTerm A`, with **both factors resolved-algebra terms** (the left is the
forest's component-generator product, not a single generator). -/
structure ResolvedCoproductForestSummandSupply (G : ResolvedFeynmanGraph) where
  /-- The forest index type. -/
  ForestIdx : Type
  /-- The finite forest carrier. -/
  forestCarrier : Finset ForestIdx
  /-- The left (outer forest) resolved-algebra term of each summand (the component-generator
  product). -/
  leftTerm : ForestIdx → ResolvedHopfH
  /-- The right (quotient/remnant) resolved-algebra term of each summand. -/
  rightTerm : ForestIdx → ResolvedHopfH

/-- The forest-sum tensor term of a summand supply. -/
noncomputable def ResolvedCoproductForestSummandSupply.sum {G : ResolvedFeynmanGraph}
    (S : ResolvedCoproductForestSummandSupply G) : ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  ∑ A ∈ S.forestCarrier, S.leftTerm A ⊗ₜ[ℚ] S.rightTerm A

/-- **R-6b-2 abstraction (graph-free).**  If two summand supplies have a carrier bijection that
preserves both the left and the right resolved-algebra terms, their forest sums are equal.  This
isolates the `mapPerm`-invariance of the forest sum into a pure `Finset.sum_bij` fact, so the later
geometric work only has to *supply the bijection + term equalities*, not re-run the sum algebra. -/
theorem ResolvedCoproductForestSummandSupply.sum_eq_of_bij {G G' : ResolvedFeynmanGraph}
    (S : ResolvedCoproductForestSummandSupply G) (T : ResolvedCoproductForestSummandSupply G')
    (i : (a : S.ForestIdx) → a ∈ S.forestCarrier → T.ForestIdx)
    (hmaps : ∀ a (ha : a ∈ S.forestCarrier), i a ha ∈ T.forestCarrier)
    (i_inj : ∀ a₁ (ha₁ : a₁ ∈ S.forestCarrier) a₂ (ha₂ : a₂ ∈ S.forestCarrier),
      i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ T.forestCarrier, ∃ a, ∃ (ha : a ∈ S.forestCarrier), i a ha = b)
    (hleft : ∀ a (ha : a ∈ S.forestCarrier), S.leftTerm a = T.leftTerm (i a ha))
    (hright : ∀ a (ha : a ∈ S.forestCarrier), S.rightTerm a = T.rightTerm (i a ha)) :
    S.sum = T.sum := by
  unfold ResolvedCoproductForestSummandSupply.sum
  exact Finset.sum_bij i hmaps i_inj i_surj
    (fun a ha => by rw [hleft a ha, hright a ha])

/-! ## The representative-level generator formula -/

/-- **R-6b-1 — the representative-level resolved coproduct on a generator**: primitive part
plus the supplied forest sum, all in `ResolvedHopfH ⊗ ResolvedHopfH`.  This is the formula
on a *representative graph* `G`; lifting it to a map out of the quotient `ResolvedHopfGen`
needs the well-definedness obligation below (R-6b-2). -/
noncomputable def resolvedCoproductGenOfGraph (G : ResolvedFeynmanGraph)
    (hCD : G.forget.toClass.IsConnectedDivergent)
    (S : ResolvedCoproductForestSummandSupply G) :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  resolvedCoproductGenPrimitive (G.toResolvedHopfGen hCD) + S.sum

/-! ## The isolated well-definedness obligation (R-6b-2 target)

To define `Δᵣ` out of `ResolvedHopfGen` (a `Quotient` of resolved graphs by id-preserving
iso), the representative-level formula must be invariant under `mapPerm` — the genuine R-6b-2
goal.  It is healthy (id-preserving relabeling sends forests to forests and each resolved
generator factor is a class, hence `mapPerm`-invariant), but it needs a lemma chain, so we
isolate it as a structure field rather than guess it now.  **No `Quotient.lift` is taken
until this is supplied.** -/

/-- The well-definedness datum for the resolved coproduct generator formula: a
representative-level generator formula together with its `mapPerm`-invariance (the obligation
R-6b-2 discharges, after which `Quotient.lift` yields `Δᵣ` on generators). -/
structure ResolvedCoproductGenWellDef where
  /-- The representative-level generator formula. -/
  genOfGraph : (G : ResolvedFeynmanGraph) →
    G.forget.toClass.IsConnectedDivergent → ResolvedHopfH ⊗[ℚ] ResolvedHopfH
  /-- **The obligation**: the formula is invariant under id-preserving relabeling, so it
  descends to the quotient `ResolvedHopfGen`. -/
  mapPerm_invariant : ∀ (σ : Equiv.Perm VertexId) (G : ResolvedFeynmanGraph)
    (h : G.forget.toClass.IsConnectedDivergent)
    (h' : (G.mapPerm σ).forget.toClass.IsConnectedDivergent),
    genOfGraph G h = genOfGraph (G.mapPerm σ) h'

/-! ## R-6b-3 — `Δᵣ` on generators by `Quotient.lift`

The primitive part `X x ⊗ 1 + 1 ⊗ X x` is already defined on the generator `x` directly
(`resolvedCoproductGenPrimitive`, no representative).  So only the **forest sum** needs to descend
through the quotient `ResolvedFeynmanGraphClass`.  That descent needs exactly one datum: a
`mapPerm`-equivariant forest-summand supply family — `(supply (G.mapPerm σ)).sum = (supply G).sum`
(the invariance the R-6b-2e ingredients `toResolvedHopfGen_mapPerm` / `mapPerm_contractWithStars_
toResolvedClass` / `sum_eq_of_bij` discharge for a concrete supply, R-6b-4).  Given it, `Δᵣ` on
generators is `Quotient.lift`. -/

/-- A `mapPerm`-equivariant family of resolved coproduct forest-summand supplies: one supply per
representative graph, with the forest sum invariant under id-preserving relabeling.  The single
field `sum_mapPerm` is what `Quotient.lift` needs (its proof, for the canonical supply, is the
R-6b-2e geometry fed through `sum_eq_of_bij`). -/
structure ResolvedCoproductGenSupply where
  /-- A forest-summand supply for every representative graph. -/
  supply : (G : ResolvedFeynmanGraph) → ResolvedCoproductForestSummandSupply G
  /-- **Equivariance**: the forest sum is invariant under id-preserving relabeling. -/
  sum_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    (supply (G.mapPerm σ)).sum = (supply G).sum

/-- The forest sum descended through the resolved graph class (well defined by `sum_mapPerm`). -/
noncomputable def ResolvedCoproductGenSupply.forestSum (S : ResolvedCoproductGenSupply)
    (c : ResolvedFeynmanGraphClass) : ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  Quotient.liftOn c (fun G => (S.supply G).sum) (by
    intro G₁ G₂ h
    obtain ⟨σ, rfl⟩ := h
    exact (S.sum_mapPerm G₁ σ).symm)

@[simp] theorem ResolvedCoproductGenSupply.forestSum_mk (S : ResolvedCoproductGenSupply)
    (G : ResolvedFeynmanGraph) :
    S.forestSum G.toResolvedClass = (S.supply G).sum := rfl

/-- **R-6b-3 — `Δᵣ` on generators.**  The primitive part (on `x` directly) plus the forest sum
descended from the class.  Defined out of the quotient `ResolvedHopfGen` with no facade, no flat
`HopfGen`, no coassociativity. -/
noncomputable def ResolvedCoproductGenSupply.gen (S : ResolvedCoproductGenSupply)
    (x : ResolvedHopfGen) : ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  resolvedCoproductGenPrimitive x + S.forestSum x.1

/-- **R-6b-3 — the resolved-target coproduct as an algebra hom** `ResolvedHopfH →ₐ ResolvedHopfH ⊗
ResolvedHopfH`, the `MvPolynomial.aeval` extension of `Δᵣ` on generators.  Codomain is the
resolved-generator algebra throughout (every factor a `ResolvedHopfGen`). -/
noncomputable def ResolvedCoproductGenSupply.coproduct (S : ResolvedCoproductGenSupply) :
    ResolvedHopfH →ₐ[ℚ] ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  MvPolynomial.aeval S.gen

@[simp] theorem ResolvedCoproductGenSupply.coproduct_X (S : ResolvedCoproductGenSupply)
    (x : ResolvedHopfGen) : S.coproduct (MvPolynomial.X x) = S.gen x := by
  simp [ResolvedCoproductGenSupply.coproduct]

/-- The representative-level generator formula is `mapPerm`-invariant (primitive via
`toResolvedHopfGen_mapPerm`, forest sum via `sum_mapPerm`) — the `ResolvedCoproductGenWellDef`
obligation, discharged for an equivariant supply. -/
theorem resolvedCoproductGenOfGraph_mapPerm_invariant (S : ResolvedCoproductGenSupply)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (hCD : G.forget.toClass.IsConnectedDivergent)
    (hCD' : (G.mapPerm σ).forget.toClass.IsConnectedDivergent) :
    resolvedCoproductGenOfGraph (G.mapPerm σ) hCD' (S.supply (G.mapPerm σ))
      = resolvedCoproductGenOfGraph G hCD (S.supply G) := by
  unfold resolvedCoproductGenOfGraph
  rw [S.sum_mapPerm G σ, ResolvedFeynmanGraph.toResolvedHopfGen_mapPerm G σ hCD hCD']

end GaugeGeometry.QFT.Combinatorial