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
  resolved (left, right) generator pairs** (abstraction avoiding the full enumeration), with
  its sum `∑ X (leftGen A) ⊗ X (rightGen A)`;
* `resolvedCoproductGenOfGraph` — the representative-level generator formula
  (primitive + forest sum);
* `ResolvedCoproductGenWellDef` — the **isolated well-definedness obligation**
  (`mapPerm_invariant`) that R-6b-2 must discharge before `Quotient.lift`ing to a map out of
  `ResolvedHopfGen`.

No `Quotient.lift` of the generator formula, no coassociativity, no flat `HopfGen` in the
codomain, no gated theorem, no `sorry`.
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

/-! ## The primitive part (well defined on the generator directly) -/

/-- The primitive part of the resolved coproduct on a generator: `X x ⊗ 1 + 1 ⊗ X x`.
Defined on `x : ResolvedHopfGen` directly — no representative choice, hence no
well-definedness obligation. -/
noncomputable def resolvedCoproductGenPrimitive (x : ResolvedHopfGen) :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  MvPolynomial.X x ⊗ₜ[ℚ] (1 : ResolvedHopfH) + (1 : ResolvedHopfH) ⊗ₜ[ℚ] MvPolynomial.X x

/-! ## The forest-sum part as a supplied finite family

To fix the codomain shape without committing to the full resolved proper-forest enumeration
yet, the forest sum is supplied as a finite family of resolved `(left, right)` generator
pairs.  Every factor is a `ResolvedHopfGen`, pinning the id-preserving target. -/

/-- A finite family of resolved coproduct forest summands for a representative graph `G`:
each index contributes `X (leftGen A) ⊗ X (rightGen A)` with **both factors resolved
generators**. -/
structure ResolvedCoproductForestSummandSupply (G : ResolvedFeynmanGraph) where
  /-- The forest index type. -/
  ForestIdx : Type
  /-- The finite forest carrier. -/
  forestCarrier : Finset ForestIdx
  /-- The left (outer forest) resolved generator of each summand. -/
  leftGen : ForestIdx → ResolvedHopfGen
  /-- The right (quotient/remnant) resolved generator of each summand. -/
  rightGen : ForestIdx → ResolvedHopfGen

/-- The forest-sum tensor term of a summand supply. -/
noncomputable def ResolvedCoproductForestSummandSupply.sum {G : ResolvedFeynmanGraph}
    (S : ResolvedCoproductForestSummandSupply G) : ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  ∑ A ∈ S.forestCarrier,
    MvPolynomial.X (S.leftGen A) ⊗ₜ[ℚ] MvPolynomial.X (S.rightGen A)

/-- **R-6b-2 abstraction (graph-free).**  If two summand supplies have a carrier bijection that
preserves both the left and the right resolved generators, their forest sums are equal.  This
isolates the `mapPerm`-invariance of the forest sum into a pure `Finset.sum_bij` fact, so the
later geometric work (R-6b-2) only has to *supply the bijection + generator-class equalities*,
not re-run the sum algebra. -/
theorem ResolvedCoproductForestSummandSupply.sum_eq_of_bij {G G' : ResolvedFeynmanGraph}
    (S : ResolvedCoproductForestSummandSupply G) (T : ResolvedCoproductForestSummandSupply G')
    (i : (a : S.ForestIdx) → a ∈ S.forestCarrier → T.ForestIdx)
    (hmaps : ∀ a (ha : a ∈ S.forestCarrier), i a ha ∈ T.forestCarrier)
    (i_inj : ∀ a₁ (ha₁ : a₁ ∈ S.forestCarrier) a₂ (ha₂ : a₂ ∈ S.forestCarrier),
      i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ T.forestCarrier, ∃ a, ∃ (ha : a ∈ S.forestCarrier), i a ha = b)
    (hleft : ∀ a (ha : a ∈ S.forestCarrier), S.leftGen a = T.leftGen (i a ha))
    (hright : ∀ a (ha : a ∈ S.forestCarrier), S.rightGen a = T.rightGen (i a ha)) :
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

end GaugeGeometry.QFT.Combinatorial