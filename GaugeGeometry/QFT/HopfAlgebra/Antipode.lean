import GaugeGeometry.QFT.HopfAlgebra.Counit

/-!
# Antipode on `HopfH`  [Sprint E — H6.1–H6.5]

This file constructs the Connes–Kreimer antipode for the strict forest
Hopf algebra structure assembled in `Bialgebra.lean`. The antipode is
defined by well-founded recursion on the canonical representative of a
`HopfGen` element, using the strict forest carrier
`forestCoproductProperForestIndex` shared with `coproduct_strict_forest`.

## Recursion shape

For a generator `g : HopfGen` with representative `repG g`, the antipode
formula on the underlying `MvPolynomial.X g` reads

```
S(X g) = - X g
       - ∑_{A ∈ forestCoproductProperForestIndex g}
            (∏ γ ∈ A.elements, S(X (γ.toHopfGen hγ))) · forestRight g A
```

Each recursive call `S(X (γ.toHopfGen hγ))` is on a strictly smaller
edge-count target via `component_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex`,
which provides the well-founded relation. The first tensor factor of
each summand is `∏ γ ∈ A.elements, S(...)` — note that admissible
forests with disjoint components contribute *products* of antipode
values, mirroring the disjoint-admissible CK formula.

## Key design choice — `LinearMap` not `AlgHom`

The Hopf antipode is **anti-multiplicative** in general, so the
public `antipode : HopfH →ₗ[ℚ] HopfH` is a `LinearMap`. Mathlib's
`HopfAlgebra` field also requires this shape. Building `antipode` as
an `AlgHom` would over-commit and fail when wired into the `HopfAlgebra`
instance.

## Sprint E pipeline (H6 stages)

* **H6.1** `antipodeGen_forest : HopfGen → HopfH` via well-founded recursion
  (this file, below).
* **H6.2** `antipodeGen_forest_emptyGraph` — vacuous for strict `HopfGen`
  (empty graph excluded).
* **H6.3** `antipodeGen_forest_isomorphism_invariant` — should follow
  from `repG`-canonical representative choice avoiding explicit lifting.
* **H6.4** `antipode : HopfH →ₗ[ℚ] HopfH` via `MvPolynomial`-based
  `LinearMap` extension.
* **H6.5** `antipode_one`, basic compatibility.
* **H6.6/H6.7** antipode axioms (left/right) — induction over
  `coassoc_strict_forest_linearMap` (will pull in `Bialgebra.lean`).
* **H6.8** `HopfAlgebra ℚ HopfH` instance.

## Imports policy

Sprint E early stages (H6.1–H6.5) import only `Coproduct.lean` to keep
elaboration light. `Bialgebra.lean` is pulled in only when H6.6/H6.7
need the `Coalgebra`/`Bialgebra` instances. -/

namespace GaugeGeometry.QFT.Combinatorial

open MvPolynomial

section Antipode

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
         [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

/-! ### Antipode-side wrappers (Sprint E local API)

`antipodeForestCanonicalHCD` and `antipodeForestRightHopfH` are local
wrappers reconstructed from `Coproduct.lean`'s public API. They mirror
the `forestCanonicalHCD` / `forestRightHopfH` shapes in `Coassoc.lean`
without taking a dependency on that file. -/

/-- Canonical connected-divergent preservation package for the forest
quotient of the representative of `g`. Reconstructed from `repG_*` and
`admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation`. -/
def antipodeForestCanonicalHCD (g : HopfGen) :
    ∀ A : AdmissibleSubgraph (repG g).toFeynmanGraph,
      ∀ hA : A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars
          (repG g).toFeynmanGraph A
          (FeynmanGraph.admissibleForestCanonicalStarOf
            (repG g).toFeynmanGraph A hA)).IsConnectedDivergent :=
  FeynmanGraph.admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation
    (repG g).toFeynmanGraph
    (repG_wellFormed g)
    (repG_isOnePI g)
    (repG_isConnectedDivergent g)

/-- Right tensor factor (canonical contraction generator) packaged as a
single `HopfH` element for the antipode recursion. -/
noncomputable def antipodeForestRightHopfH (g : HopfGen)
    (A : AdmissibleSubgraph (repG g).toFeynmanGraph)
    (hA : A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs) :
    HopfH :=
  gen (FeynmanGraph.admissibleForestRightWithCanonicalStars
    (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hA)

/-! ### H6.1 — `antipodeGen_forest` via well-founded recursion

The recursion measure is `(repG g).toFeynmanGraph.internalEdges.card`,
which strictly decreases at every recursive call thanks to
`component_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex`.

The recursion target is `HopfGen` itself: each component
`γ ∈ A.elements` (where `A ∈ forestCoproductProperForestIndex g`)
produces a smaller `HopfGen` via `γ.toHopfGen hγ` whose `repG` has
fewer internal edges than `repG g`. -/

/-- The Connes–Kreimer antipode on a strict CK generator, defined by
well-founded recursion on the internal-edge count of the canonical
representative graph. -/
noncomputable def antipodeGen_forest (g : HopfGen) : HopfH :=
  - (MvPolynomial.X g : HopfH)
  - ∑ A ∈ forestCoproductProperForestIndex g,
      if hA : A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
          ∧ 0 < A.complementEdges.card then
        (∏ γ ∈ A.elements.attach,
          have hγlt :
              (repG (γ.1.toHopfGen (A.isConnectedDivergent_of_mem γ.2))).toFeynmanGraph.internalEdges.card <
                (repG g).toFeynmanGraph.internalEdges.card :=
            repG_toHopfGen_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex
              (by rw [mem_forestCoproductProperForestIndex]; exact hA) γ.2
              (A.isConnectedDivergent_of_mem γ.2)
          antipodeGen_forest (γ.1.toHopfGen
            (A.isConnectedDivergent_of_mem γ.2)))
        * antipodeForestRightHopfH g A hA.1
      else 0
termination_by (repG g).toFeynmanGraph.internalEdges.card
decreasing_by
  simp_wf
  exact hγlt

/-! ### H6.4 — `antipode : HopfH →ₐ[ℚ] HopfH` and `→ₗ[ℚ] HopfH`

`HopfH := MvPolynomial HopfGen ℚ` is a commutative polynomial algebra,
so even though the Hopf antipode is anti-multiplicative in general, on
this commutative carrier it descends to a genuine algebra map.
`MvPolynomial.aeval` on `antipodeGen_forest` is the canonical extension.

Mathlib's `HopfAlgebra` field consumes a `LinearMap`, so the public
`antipode` is the underlying linear map of the AlgHom. -/

/-- The Connes–Kreimer antipode as an AlgHom — well-defined here because
`HopfH` is a commutative polynomial algebra. -/
noncomputable def antipodeAlgHom_forest : HopfH →ₐ[ℚ] HopfH :=
  MvPolynomial.aeval antipodeGen_forest

/-- The Connes–Kreimer antipode in Mathlib's `HopfAlgebra`-compatible
LinearMap shape. -/
noncomputable def antipode_forest : HopfH →ₗ[ℚ] HopfH :=
  antipodeAlgHom_forest.toLinearMap

/-! ### H6.5 — `antipode_forest 1 = 1` and basic compatibility -/

/-- Antipode preserves `1` (algebra-map preservation). -/
@[simp] theorem antipode_forest_one : antipode_forest (1 : HopfH) = 1 :=
  map_one antipodeAlgHom_forest

/-- Antipode acts on a generator `X g` by the well-founded recursion
formula `antipodeGen_forest g`. -/
@[simp] theorem antipode_forest_X (g : HopfGen) :
    antipode_forest (MvPolynomial.X g : HopfH) = antipodeGen_forest g := by
  unfold antipode_forest antipodeAlgHom_forest
  simp [AlgHom.toLinearMap_apply, MvPolynomial.aeval_X]

/-- Antipode is multiplicative on the commutative polynomial carrier. -/
theorem antipode_forest_mul (a b : HopfH) :
    antipode_forest (a * b) = antipode_forest a * antipode_forest b :=
  map_mul antipodeAlgHom_forest a b

/-! ### H6.6/H6.7 prep — antipode on `A.toHopfH` decomposes as a component product

`A.toHopfH = ∏ γ ∈ A.elements, componentToHopfH A γ` ([Coproduct.lean:1650](Coproduct.lean#L1650)),
and `componentToHopfH A γ = gen (γ.toHopfGen ...)` on `γ ∈ A.elements`.
Pushing `antipode_forest` (a `MvPolynomial.aeval`-extended AlgHom) through
the product gives the component-by-component antipode. -/

private theorem antipode_forest_componentToHopfH
    {G : FeynmanGraph} (A : AdmissibleSubgraph G)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    antipode_forest (A.componentToHopfH γ) =
      antipodeGen_forest (γ.toHopfGen (A.isConnectedDivergent_of_mem hγ)) := by
  unfold AdmissibleSubgraph.componentToHopfH
  rw [dif_pos hγ]
  -- gen g = MvPolynomial.X g, so antipode_forest_X applies.
  unfold gen
  exact antipode_forest_X _

/-- Antipode on the admissible-subgraph product `A.toHopfH` factors through
the component generators. This is the left-side decomposition needed for
H6.6 generator-level cancellation. -/
theorem antipode_forest_toHopfH_admissibleSubgraph
    {G : FeynmanGraph} (A : AdmissibleSubgraph G) :
    antipode_forest A.toHopfH =
      ∏ γ ∈ A.elements.attach,
        antipodeGen_forest
          (γ.1.toHopfGen (A.isConnectedDivergent_of_mem γ.2)) := by
  unfold AdmissibleSubgraph.toHopfH
  -- Push antipode through the product via the AlgHom.
  rw [show antipode_forest = antipodeAlgHom_forest.toLinearMap from rfl]
  rw [AlgHom.toLinearMap_apply, map_prod]
  rw [← Finset.prod_attach A.elements
        (fun γ => antipodeAlgHom_forest (A.componentToHopfH γ))]
  apply Finset.prod_congr rfl
  intro γ _
  -- antipode (componentToHopfH A γ) = antipodeGen_forest (γ.toHopfGen ...)
  have := antipode_forest_componentToHopfH A γ.2
  simpa [show antipode_forest = antipodeAlgHom_forest.toLinearMap from rfl,
    AlgHom.toLinearMap_apply] using this

/-! ### H6.6a auxiliary — antipode through a single forest summand

For each `A ∈ forestCoproductProperForestIndex g`, the summand
`admissibleForestStrictSummandWithCanonicalStars (repG g) hCD A` equals
`A.toHopfH ⊗ gen(right A)`. Pushing `mul' ∘ S.rTensor` gives:

```
mul' (S A.toHopfH ⊗ gen(right A))
  = S(A.toHopfH) * gen(right A)
  = (∏ γ ∈ A.elements.attach, antipodeGen_forest (γ.toHopfGen ...)) * antipodeForestRightHopfH g A hAprop
```

This is the per-summand identity reused inside the `H6.6a` Σ-rewriting. -/
theorem antipode_forest_admissibleForestStrictSummandWithCanonicalStars_of_mem
    (g : HopfGen)
    (A : AdmissibleSubgraph (repG g).toFeynmanGraph)
    (hA : A ∈ forestCoproductProperForestIndex g) :
    ((LinearMap.mul' ℚ HopfH).comp
        (antipode_forest.rTensor HopfH))
        (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A)
      =
    (∏ γ ∈ A.elements.attach,
       antipodeGen_forest
         (γ.1.toHopfGen (A.isConnectedDivergent_of_mem γ.2)))
      * antipodeForestRightHopfH g A
        ((mem_forestCoproductProperForestIndex g A).mp hA).1 := by
  have hAproper :
      A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs :=
    ((mem_forestCoproductProperForestIndex g A).mp hA).1
  -- Unfold the summand to its tmul form.
  rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAproper]
  -- mul' ∘ S.rTensor (a ⊗ b) = S a * b
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearMap.rTensor_tmul, LinearMap.mul'_apply]
  -- Now LHS = antipode_forest A.toHopfH * gen(right A).
  -- Push antipode through A.toHopfH.
  rw [antipode_forest_toHopfH_admissibleSubgraph]
  -- Right factor: gen (admissibleForestRightWithCanonicalStars _ _ A hAproper)
  --             = antipodeForestRightHopfH g A hAproper  (defeq)
  rfl

/-- Sprint Track D-wrapper-1a: `lTensor` per-summand identity (right-axiom
sibling of the rTensor lemma above).  Pushing `mul' ∘ S.lTensor` through the
summand `A.toHopfH ⊗ gen(right A)` gives `A.toHopfH * S(gen(right A))`
= `A.toHopfH * antipodeGen_forest(right A)`. -/
theorem antipode_forest_lTensor_admissibleForestStrictSummandWithCanonicalStars_of_mem
    (g : HopfGen)
    (A : AdmissibleSubgraph (repG g).toFeynmanGraph)
    (hA : A ∈ forestCoproductProperForestIndex g) :
    ((LinearMap.mul' ℚ HopfH).comp
        (antipode_forest.lTensor HopfH))
        (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A)
      =
    A.toHopfH *
      antipodeGen_forest
        (FeynmanGraph.admissibleForestRightWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A
          ((mem_forestCoproductProperForestIndex g A).mp hA).1) := by
  have hAproper :
      A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs :=
    ((mem_forestCoproductProperForestIndex g A).mp hA).1
  rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAproper]
  simp only [LinearMap.coe_comp, Function.comp_apply,
    LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  -- LHS = A.toHopfH * antipode_forest (gen(right A))
  -- gen(right A) = X(right A); antipode_forest_X gives antipodeGen_forest(right A).
  rw [show (gen (FeynmanGraph.admissibleForestRightWithCanonicalStars
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAproper) : HopfH) =
      MvPolynomial.X (FeynmanGraph.admissibleForestRightWithCanonicalStars
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAproper) from rfl,
    antipode_forest_X]

/-! ### H6.6a — Generator-level left antipode axiom -/

/-- Helper: the canonical-stars body of `coproduct_strict_forest (X g)` rebuilt
in terms of the user-facing `gen g` and `forestCoproductProperForestIndex g`. -/
theorem coproduct_strict_forest_X_canonicalBody_eq (g : HopfGen) :
    coproduct_strict_forest (MvPolynomial.X g)
      =
    (gen g ⊗ₜ[ℚ] (1 : HopfH))
    + ((1 : HopfH) ⊗ₜ[ℚ] gen g)
    + ∑ A ∈ forestCoproductProperForestIndex g,
        FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A := by
  rw [coproduct_strict_forest_X, coproductGenClass_strict_forest_eq]
  -- Beta-reduce all `let`s to expose the body, then identify gen and carrier.
  show
      (gen ⟨(repG g).toFeynmanGraph.toClass, _⟩ ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] gen ⟨(repG g).toFeynmanGraph.toClass, _⟩)
      + ∑ A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs.filter
          (fun A => 0 < A.complementEdges.card),
          FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
            (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A
        =
      (gen g ⊗ₜ[ℚ] (1 : HopfH))
      + ((1 : HopfH) ⊗ₜ[ℚ] gen g)
      + ∑ A ∈ forestCoproductProperForestIndex g,
          FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
            (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A
  -- gen ⟨(repG g).toClass, _⟩ = gen g.
  have hgen :
      (gen ⟨(repG g).toFeynmanGraph.toClass,
        (FeynmanGraphClass.isConnectedDivergent_toClass (repG g).toFeynmanGraph).mpr
          (repG_isConnectedDivergent g)⟩ : HopfH) = gen g := by
    congr 1
    exact Subtype.ext (repG_toClass g)
  rw [hgen]
  -- The two carriers are definitionally equal.
  rfl

set_option maxHeartbeats 1200000 in
theorem mul_antipode_rTensor_coproduct_strict_forest_X (g : HopfGen) :
    ((LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.rTensor HopfH).comp
          coproduct_strict_forest.toLinearMap)) (MvPolynomial.X g)
      =
    ((Algebra.linearMap ℚ HopfH).comp counit.toLinearMap) (MvPolynomial.X g) := by
  -- RHS: counit (X g) = 0, then algebraMap of 0 = 0.
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    counit_X, map_zero]
  -- LHS: expand coproduct on a generator via the helper.
  rw [coproduct_strict_forest_X_canonicalBody_eq g]
  -- Push antipode.rTensor and mul' through (a + b + Σ).
  rw [map_add, map_add, map_add, map_add,
    LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
    LinearMap.mul'_apply, LinearMap.mul'_apply,
    mul_one, map_sum, map_sum]
  -- antipode_forest is an AlgHom, so antipode_forest 1 = 1.
  rw [show (antipode_forest (1 : HopfH)) = 1 from antipode_forest_one, one_mul]
  -- Each summand: replace via the per-summand helper. Bridge composed vs
  -- applied form with LinearMap.coe_comp. Use attach-Σ so the membership
  -- proof is available inside the binder.
  rw [show
      ∑ A ∈ forestCoproductProperForestIndex g,
          (LinearMap.mul' ℚ HopfH)
            ((LinearMap.rTensor HopfH antipode_forest)
              (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
                (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A))
        =
      ∑ A ∈ (forestCoproductProperForestIndex g).attach,
          (∏ γ ∈ A.1.elements.attach,
            antipodeGen_forest
              (γ.1.toHopfGen (A.1.isConnectedDivergent_of_mem γ.2)))
          * antipodeForestRightHopfH g A.1
              ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1
      from by
        rw [← Finset.sum_attach]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        have h := antipode_forest_admissibleForestStrictSummandWithCanonicalStars_of_mem
          g A.1 A.2
        simpa [LinearMap.coe_comp, Function.comp_apply] using h]
  -- Left antipode on generator.
  rw [show gen g = MvPolynomial.X g from rfl, antipode_forest_X]
  -- Unfold antipodeGen_forest g once.
  rw [antipodeGen_forest]
  -- Replace the `if hA`-guarded Σ inside antipodeGen_forest with the
  -- attach-Σ of (∏ γ, antipodeGen_forest ...) * antipodeForestRightHopfH,
  -- so the membership proof is locally available inside the binder and the
  -- shape matches the previously-rewritten Σ.
  rw [show
      (∑ A ∈ forestCoproductProperForestIndex g,
        if hA : A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
            ∧ 0 < A.complementEdges.card then
          (∏ γ ∈ A.elements.attach,
            antipodeGen_forest
              (γ.1.toHopfGen (A.isConnectedDivergent_of_mem γ.2)))
          * antipodeForestRightHopfH g A hA.1
        else 0)
        =
      ∑ A ∈ (forestCoproductProperForestIndex g).attach,
        (∏ γ ∈ A.1.elements.attach,
          antipodeGen_forest
            (γ.1.toHopfGen (A.1.isConnectedDivergent_of_mem γ.2)))
        * antipodeForestRightHopfH g A.1
            ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1
      from by
        rw [← Finset.sum_attach (forestCoproductProperForestIndex g)]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        have hAcond :
            A.1 ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
              ∧ 0 < A.1.complementEdges.card :=
          (mem_forestCoproductProperForestIndex g A.1).mp A.2
        rw [dif_pos hAcond]]
  -- Final: (-X g - Σ_attach) + X g + Σ_attach = 0
  ring

/-! ### H6.6b — Globalize the rTensor antipode axiom to a LinearMap equality

The generator-level theorem above lifts to a full `LinearMap` equality in
Mathlib's `mul_antipode_rTensor_comul` shape because `HopfH` is the
**commutative** polynomial algebra `MvPolynomial HopfGen ℚ`:

* `coproduct_strict_forest : HopfH →ₐ[ℚ] HopfH ⊗[ℚ] HopfH` is an AlgHom.
* `Algebra.TensorProduct.map antipodeAlgHom_forest (AlgHom.id ℚ HopfH)` is
  an AlgHom, and its `.toLinearMap` is `antipode_forest.rTensor HopfH`
  (since `AlgebraTensorModule.map_eq = TensorProduct.map` and
  `LinearMap.rTensor f = TensorProduct.map f LinearMap.id` definitionally).
* `Algebra.TensorProduct.lmul' ℚ : HopfH ⊗[ℚ] HopfH →ₐ[ℚ] HopfH` has
  `.toLinearMap = LinearMap.mul' ℚ HopfH`.
* `Algebra.ofId ℚ HopfH : ℚ →ₐ[ℚ] HopfH` and `counit : HopfH →ₐ[ℚ] ℚ` are
  AlgHoms whose composite has `.toLinearMap = (Algebra.linearMap ℚ HopfH) ∘ₗ
  counit.toLinearMap`.

So both sides of the axiom are AlgHoms `HopfH →ₐ[ℚ] HopfH`. By
`MvPolynomial.algHom_ext` it suffices to compare on each generator
`X g`, which is exactly H6.6a above. -/

/-- AlgHom-level packaging of the LHS of the left antipode axiom. -/
private noncomputable def axiomLHS_alg : HopfH →ₐ[ℚ] HopfH :=
  (Algebra.TensorProduct.lmul' ℚ).comp
    ((Algebra.TensorProduct.map antipodeAlgHom_forest (AlgHom.id ℚ HopfH)).comp
      coproduct_strict_forest)

/-- AlgHom-level packaging of the RHS of the left antipode axiom. -/
private noncomputable def axiomRHS_alg : HopfH →ₐ[ℚ] HopfH :=
  (Algebra.ofId ℚ HopfH).comp counit

private theorem axiomLHS_alg_eq_axiomRHS_alg : axiomLHS_alg = axiomRHS_alg := by
  refine MvPolynomial.algHom_ext (fun g => ?_)
  -- Reduce to the H6.6a generator-level equation.
  unfold axiomLHS_alg axiomRHS_alg
  -- LHS at X g: lmul' (map S id (Δ (X g))) = mul' (rTensor S (Δ (X g)))
  -- RHS at X g: ofId (counit (X g)) = algebraMap ℚ HopfH (counit (X g))
  -- The H6.6a theorem is exactly this in LinearMap-applied form.
  have h := mul_antipode_rTensor_coproduct_strict_forest_X g
  simpa [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply] using h

/-- **H6.6b — Mathlib `mul_antipode_rTensor_comul`-shape left antipode axiom.**
This is the LinearMap equality that the `HopfAlgebra` field demands. -/
theorem mul_antipode_rTensor_coproduct_strict_forest :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.rTensor HopfH).comp
          coproduct_strict_forest.toLinearMap)
      =
    (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap := by
  -- Both sides are `.toLinearMap` of the AlgHoms `axiomLHS_alg` and
  -- `axiomRHS_alg`; the AlgHom equality lifts via `congrArg`.
  have h := axiomLHS_alg_eq_axiomRHS_alg
  -- Project the AlgHom equality to a LinearMap equality.
  have hLM : axiomLHS_alg.toLinearMap = axiomRHS_alg.toLinearMap :=
    congrArg AlgHom.toLinearMap h
  -- Both `.toLinearMap` reduce to the desired shapes.
  simpa [axiomLHS_alg, axiomRHS_alg, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, LinearMap.rTensor_def,
    Algebra.TensorProduct.lmul'_toLinearMap] using hLM

/-! ### H6.7 — Right antipode axiom (Sprint E facade)

The `mul_antipode_lTensor_comul` axiom requires a forest-decomposition
recombination that does NOT mirror the left side: pushing `mul' ∘ S.lTensor`
through a summand `A.toHopfH ⊗ gen(right A)` gives `A.toHopfH * S(gen(right A))`,
where the right factor is `antipodeGen_forest(right A)`. Cancelling this
against the recursive antipode definition requires a **different**
forest-summation identity than the left axiom uses, with a flavor
analogous to Sprint D's H5.8 admissible-forest redesign.

To keep Sprint E focused on assembling the `HopfAlgebra` instance, the
right axiom is isolated as a Sprint E facade typeclass
`AntipodeStrictForestRightReady`. The conditional `HopfAlgebra` instance
in `HopfAlgebra.lean` will require both `[CoassocStrictForestH58Ready]`
and `[AntipodeStrictForestRightReady]`.

**Discharge plan (pre-final-audit):** prove the right summation identity
along the lines of CK 1998 §3, leveraging the same
`forestComponentSplitPhi*` infrastructure that closed H5.8. -/

/-- **Track D-core-1 — measure-decrease lemma.**  For `A ∈ forestCoproductProperForestIndex g`,
the right quotient `right A = G/A` has strictly fewer internal edges than `g`.
This is the well-founded measure that lets `AntipodeForestRightCoreIdentity`
be attacked by strong induction on `(repG g).internalEdges.card`.

Proof: `repG(right A)` edge count = `(contractGraphWithStars).internalEdges.card`
(via `repG_internalEdges_card_eq_of_toClass` + the `_val` simp), which equals
`A.complementEdges.card` (`contractWithStars_internalEdges` + `card_map`).
Then `A.complementEdges.card = G.I.card − A.I.card < G.I.card` because
`0 < A.I.card` (proper-disjoint condition). -/
theorem antipodeForestRight_internalEdges_card_lt
    (g : HopfGen)
    (A : AdmissibleSubgraph (repG g).toFeynmanGraph)
    (hA : A ∈ forestCoproductProperForestIndex g) :
    (repG (FeynmanGraph.admissibleForestRightWithCanonicalStars
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A
        ((mem_forestCoproductProperForestIndex g A).mp hA).1)).toFeynmanGraph.internalEdges.card <
      (repG g).toFeynmanGraph.internalEdges.card := by
  have hAproper := ((mem_forestCoproductProperForestIndex g A).mp hA).1
  set starOf := FeynmanGraph.admissibleForestCanonicalStarOf (repG g).toFeynmanGraph A hAproper
    with hstarOf
  -- repG(right A) edge count = contractGraphWithStars edge count.
  have hRepCard :
      (repG (FeynmanGraph.admissibleForestRightWithCanonicalStars
        (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A hAproper)).toFeynmanGraph.internalEdges.card =
      (FeynmanGraph.admissibleForestContractGraphWithStars (repG g).toFeynmanGraph A starOf).internalEdges.card := by
    apply repG_internalEdges_card_eq_of_toClass
    rw [FeynmanGraph.admissibleForestRightWithCanonicalStars_val]
  rw [hRepCard, FeynmanGraph.admissibleForestContractGraphWithStars_eq,
      AdmissibleSubgraph.contractWithStars_internalEdges, Multiset.card_map]
  -- Now: A.complementEdges.card < (repG g).I.card.
  have hAIpos : 0 < A.internalEdges.card :=
    (((repG g).toFeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs A).mp
      hAproper).2.2.1
  have hAIle : A.internalEdges ≤ (repG g).toFeynmanGraph.internalEdges :=
    admissibleSubgraph_internalEdges_le_of_pairwise A
      ((repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint
        hAproper)
  have hComplCard : A.complementEdges.card =
      (repG g).toFeynmanGraph.internalEdges.card - A.internalEdges.card := by
    show ((repG g).toFeynmanGraph.internalEdges - A.internalEdges).card = _
    exact Multiset.card_sub hAIle
  have hAIcardLe : A.internalEdges.card ≤ (repG g).toFeynmanGraph.internalEdges.card :=
    Multiset.card_le_card hAIle
  rw [hComplCard]
  omega

/-! ### Track D-1 — `AntipodeForestRightCoreIdentity` facade

The right antipode axiom reduces (via generator expansion + recursive
substitution of `antipodeGen_forest g`) to a single forest-summation
cancellation, the CK 1998 §3 core identity:

```
∑_A A.toHopfH * S(gen(right A))  =  ∑_A (∏γ S(γ)) * gen(right A)
```

This is isolated below as `AntipodeForestRightCoreIdentity`, so that
`AntipodeStrictForestRightReady` can be discharged by the wrapper layer
(generator reduction + `MvPolynomial.algHom_ext` globalization) from this
single facade — mirroring the hBP structural decomposition.  The two sides
are given explicit `def`s so the wrapper proof can `rw` cleanly. -/

/-- LHS of the right-antipode core identity: `∑_A A.toHopfH * S(gen(right A))`,
the `(id ⊗ S)`-image of the forest summand after `mul`. -/
private noncomputable def antipodeForestRightCoreLHS (g : HopfGen) : HopfH :=
  ∑ A ∈ (forestCoproductProperForestIndex g).attach,
    A.1.toHopfH *
      antipodeGen_forest
        (FeynmanGraph.admissibleForestRightWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A.1
          ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1)

/-- RHS of the right-antipode core identity: `∑_A (∏γ S(γ)) * gen(right A)`,
the recursive-definition expansion of `antipodeGen_forest g`'s sum term. -/
private noncomputable def antipodeForestRightCoreRHS (g : HopfGen) : HopfH :=
  ∑ A ∈ (forestCoproductProperForestIndex g).attach,
    (∏ γ ∈ A.1.elements.attach,
      antipodeGen_forest
        (γ.1.toHopfGen (A.1.isConnectedDivergent_of_mem γ.2)))
    * antipodeForestRightHopfH g A.1
        ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1

/-- **Track D-1 facade** — the CK §3 right-antipode forest-summation core
identity, isolated as a typeclass payload.  Discharge requires the forest
re-indexing cancellation analogous to (but distinct from) H5.8. -/
class AntipodeForestRightCoreIdentity : Prop where
  right_core : ∀ g : HopfGen, antipodeForestRightCoreLHS g = antipodeForestRightCoreRHS g

/-- Track D-1: expose the core identity as a direct theorem from the facade. -/
private theorem antipode_forest_right_core_identity
    [AntipodeForestRightCoreIdentity] (g : HopfGen) :
    antipodeForestRightCoreLHS g = antipodeForestRightCoreRHS g :=
  AntipodeForestRightCoreIdentity.right_core g

set_option maxHeartbeats 1200000 in
/-- **Track D-wrapper-1b — Generator-level right antipode axiom** from the
core-identity facade.  Mirror of `mul_antipode_rTensor_coproduct_strict_forest_X`
with `lTensor` (S on the right tensor factor).  After expanding the coproduct
and pushing `mul' ∘ S.lTensor`, the boundary terms give `gen g + S(gen g)`
and the forest summand gives `antipodeForestRightCoreLHS g`; unfolding
`S(gen g) = antipodeGen_forest g` exposes `-gen g - antipodeForestRightCoreRHS g`,
so the total collapses to `LHS-core − RHS-core`, closed by the facade. -/
private theorem mul_antipode_lTensor_coproduct_strict_forest_X
    [AntipodeForestRightCoreIdentity] (g : HopfGen) :
    ((LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.lTensor HopfH).comp
          coproduct_strict_forest.toLinearMap)) (MvPolynomial.X g)
      =
    ((Algebra.linearMap ℚ HopfH).comp counit.toLinearMap) (MvPolynomial.X g) := by
  -- RHS: counit (X g) = 0.
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    counit_X, map_zero]
  -- LHS: expand coproduct on a generator.
  rw [coproduct_strict_forest_X_canonicalBody_eq g]
  -- Push S.lTensor and mul' through (a + b + Σ).
  rw [map_add, map_add, map_add, map_add,
    LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
    LinearMap.mul'_apply, LinearMap.mul'_apply,
    map_sum, map_sum]
  -- Boundary terms: gen g * S(1) = gen g, and 1 * S(gen g) = S(gen g).
  rw [show (antipode_forest (1 : HopfH)) = 1 from antipode_forest_one,
    mul_one, one_mul]
  -- Forest summand Σ → antipodeForestRightCoreLHS.
  rw [show
      ∑ A ∈ forestCoproductProperForestIndex g,
          (LinearMap.mul' ℚ HopfH)
            ((LinearMap.lTensor HopfH antipode_forest)
              (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
                (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A))
        =
      antipodeForestRightCoreLHS g
      from by
        unfold antipodeForestRightCoreLHS
        rw [← Finset.sum_attach (forestCoproductProperForestIndex g)
          (fun A => (LinearMap.mul' ℚ HopfH)
            ((LinearMap.lTensor HopfH antipode_forest)
              (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars
                (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A)))]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        exact antipode_forest_lTensor_admissibleForestStrictSummandWithCanonicalStars_of_mem
          g A.1 A.2]
  -- S(gen g) = antipodeGen_forest g.
  rw [show gen g = MvPolynomial.X g from rfl, antipode_forest_X, antipodeGen_forest]
  -- The dif-guarded Σ inside antipodeGen_forest → antipodeForestRightCoreRHS.
  rw [show
      (∑ A ∈ forestCoproductProperForestIndex g,
        if hA : A ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
            ∧ 0 < A.complementEdges.card then
          (∏ γ ∈ A.elements.attach,
            antipodeGen_forest
              (γ.1.toHopfGen (A.isConnectedDivergent_of_mem γ.2)))
          * antipodeForestRightHopfH g A hA.1
        else 0)
        =
      antipodeForestRightCoreRHS g
      from by
        unfold antipodeForestRightCoreRHS
        rw [← Finset.sum_attach (forestCoproductProperForestIndex g)]
        refine Finset.sum_congr rfl (fun A _ => ?_)
        have hAcond :
            A.1 ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
              ∧ 0 < A.1.complementEdges.card :=
          (mem_forestCoproductProperForestIndex g A.1).mp A.2
        rw [dif_pos hAcond]]
  -- Now: gen g + (-gen g - RHS-core) + LHS-core = 0, i.e. LHS-core = RHS-core.
  rw [antipode_forest_right_core_identity g]
  ring

/-- AlgHom-level packaging of the LHS of the **right** antipode axiom.
Mirror of `axiomLHS_alg` with the tensor map order flipped:
`map (id) S` (= `id ⊗ S` = `lTensor S`) instead of `map S (id)`. -/
private noncomputable def axiomLHS_alg_right : HopfH →ₐ[ℚ] HopfH :=
  (Algebra.TensorProduct.lmul' ℚ).comp
    ((Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) antipodeAlgHom_forest).comp
      coproduct_strict_forest)

private theorem axiomLHS_alg_right_eq_axiomRHS_alg
    [AntipodeForestRightCoreIdentity] :
    axiomLHS_alg_right = axiomRHS_alg := by
  refine MvPolynomial.algHom_ext (fun g => ?_)
  unfold axiomLHS_alg_right axiomRHS_alg
  have h := mul_antipode_lTensor_coproduct_strict_forest_X g
  simpa [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    Algebra.linearMap_apply] using h

/-- **Track D-wrapper-2 — Mathlib `mul_antipode_lTensor_comul`-shape right
antipode axiom**, derived from the core-identity facade.  LinearMap equality
the `HopfAlgebra` right-antipode field demands. -/
theorem mul_antipode_lTensor_coproduct_strict_forest
    [AntipodeForestRightCoreIdentity] :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.lTensor HopfH).comp
          coproduct_strict_forest.toLinearMap)
      =
    (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap := by
  have h := axiomLHS_alg_right_eq_axiomRHS_alg
  have hLM : axiomLHS_alg_right.toLinearMap = axiomRHS_alg.toLinearMap :=
    congrArg AlgHom.toLinearMap h
  simpa [axiomLHS_alg_right, axiomRHS_alg, AlgHom.comp_toLinearMap,
    Algebra.TensorProduct.toLinearMap_map,
    TensorProduct.AlgebraTensorModule.map_eq, LinearMap.lTensor_def,
    Algebra.TensorProduct.lmul'_toLinearMap] using hLM

/-- **Sprint E facade** — the right antipode axiom in Mathlib's
`mul_antipode_lTensor_comul` shape, isolated as a typeclass payload.
Discharge requires a forest-summation identity analogous to (but
mathematically distinct from) H5.8. -/
class AntipodeStrictForestRightReady : Prop where
  mul_antipode_lTensor_coproduct_strict_forest :
    (LinearMap.mul' ℚ HopfH).comp
        ((antipode_forest.lTensor HopfH).comp
          coproduct_strict_forest.toLinearMap)
      =
    (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap

/-- **Track D connector** — `AntipodeStrictForestRightReady` is discharged
from the single core-identity facade `AntipodeForestRightCoreIdentity` via the
D-wrapper-1/2 layer.  This reduces the Sprint-E right-antipode facade to the
CK §3 forest-summation core identity, mirroring the hBP decomposition: the
remaining mathematical content is fully isolated in one named interface. -/
instance AntipodeStrictForestRightReady_of_coreIdentity
    [AntipodeForestRightCoreIdentity] : AntipodeStrictForestRightReady where
  mul_antipode_lTensor_coproduct_strict_forest :=
    mul_antipode_lTensor_coproduct_strict_forest

/-! ### Track D-core-2 — CK §3 reindexing infrastructure

Expose the core identity's LHS as `boundary + double-sum`, making the
CK §3 forest re-indexing target a concrete Lean expression.  The enabler
is `antipodeGen_forest_eq`: the recursive antipode equals
`-gen − antipodeForestRightCoreRHS`, with the recursion's `dif`-guarded sum
identified with the canonical attach-form `antipodeForestRightCoreRHS`. -/

/-- **Track D-core-2a enabler** — closed form of the recursive antipode:
`antipodeGen_forest g = -gen g − antipodeForestRightCoreRHS g`.  The `dif`-guarded
sum in the recursive definition is converted to the canonical attach-form
`antipodeForestRightCoreRHS`. -/
private theorem antipodeGen_forest_eq (g : HopfGen) :
    antipodeGen_forest g
      = - (MvPolynomial.X g : HopfH) - antipodeForestRightCoreRHS g := by
  rw [antipodeGen_forest]
  congr 1
  unfold antipodeForestRightCoreRHS
  rw [← Finset.sum_attach (forestCoproductProperForestIndex g)]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  have hAcond :
      A.1 ∈ (repG g).toFeynmanGraph.properDisjointAdmissibleDivergentSubgraphs
        ∧ 0 < A.1.complementEdges.card :=
    (mem_forestCoproductProperForestIndex g A.1).mp A.2
  rw [dif_pos hAcond]

/-- Boundary term of the expanded core-identity LHS:
`∑_A A.toHopfH * gen(right A)`. -/
private noncomputable def antipodeForestRightBoundaryTerm (g : HopfGen) : HopfH :=
  ∑ A ∈ (forestCoproductProperForestIndex g).attach,
    A.1.toHopfH *
      antipodeForestRightHopfH g A.1
        ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1

/-- Double-sum term of the expanded core-identity LHS:
`∑_A A.toHopfH * antipodeForestRightCoreRHS(right A)` — the nested forest sum
that the CK §3 re-indexing must cancel against the boundary + RHS. -/
private noncomputable def antipodeForestRightDoubleSumTerm (g : HopfGen) : HopfH :=
  ∑ A ∈ (forestCoproductProperForestIndex g).attach,
    A.1.toHopfH *
      antipodeForestRightCoreRHS
        (FeynmanGraph.admissibleForestRightWithCanonicalStars
          (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A.1
          ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1)

/-- **Track D-core-2b — core-identity LHS expanded once.**  Unfolds the
recursive antipode (via `antipodeGen_forest_eq`) inside each summand and
distributes, exposing `antipodeForestRightCoreLHS` as `−boundary − double-sum`.
The double-sum term `antipodeForestRightDoubleSumTerm` is now the concrete
CK §3 re-indexing target. -/
private theorem antipodeForestRightCoreLHS_expand_once (g : HopfGen) :
    antipodeForestRightCoreLHS g =
      - antipodeForestRightBoundaryTerm g - antipodeForestRightDoubleSumTerm g := by
  -- Show the combined sum vanishes termwise: a·(−X−C) + a·X + a·C = 0.
  have key : antipodeForestRightCoreLHS g + antipodeForestRightBoundaryTerm g
      + antipodeForestRightDoubleSumTerm g = 0 := by
    unfold antipodeForestRightCoreLHS antipodeForestRightBoundaryTerm
      antipodeForestRightDoubleSumTerm
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro A _
    rw [antipodeGen_forest_eq,
      show antipodeForestRightHopfH g A.1
          ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1
        = MvPolynomial.X (FeynmanGraph.admissibleForestRightWithCanonicalStars
            (repG g).toFeynmanGraph (antipodeForestCanonicalHCD g) A.1
            ((mem_forestCoproductProperForestIndex g A.1).mp A.2).1) from rfl]
    ring
  rw [← sub_eq_zero,
    show antipodeForestRightCoreLHS g -
        (- antipodeForestRightBoundaryTerm g - antipodeForestRightDoubleSumTerm g)
      = antipodeForestRightCoreLHS g + antipodeForestRightBoundaryTerm g
        + antipodeForestRightDoubleSumTerm g from by ring]
  exact key

end Antipode

end GaugeGeometry.QFT.Combinatorial
