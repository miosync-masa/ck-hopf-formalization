import GaugeGeometry.QFT.HopfAlgebra.Coproduct
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Counit on `HopfH`  [Sprint D — H5.1–H5.5]

This file defines the Connes–Kreimer counit

```
ε : HopfH →ₐ[ℚ] ℚ
```

determined by `ε([emptyGraph]) = 1` and `ε([Γ]) = 0` for every other
generator. The strict `HopfGen` subtype excludes the empty graph by
construction (`IsConnectedDivergent` requires `IsSupportConnected`,
hence `IsNonempty`), so the generator function is the **constant zero**;
the unit `1 ∈ HopfH = MvPolynomial HopfGen ℚ` carries the `ε(1) = 1`
behaviour automatically through `MvPolynomial.aeval`.

## Statement-table coverage (HOPF_DECOMPOSITION.md § H5)

* **H5.1** `counitGen : HopfGen → ℚ` ≡ 0 (constant; the empty-graph
  branch is vacuous since `emptyGraph ∉ HopfGen`)
* **H5.2** `counit : HopfH →ₐ[ℚ] ℚ` via `MvPolynomial.aeval`
* **H5.3** `counit_one : counit 1 = 1`
* **H5.4** *(vacuous)* — `X [emptyGraph]` is not typeable: `HopfGen`
  excludes the empty graph by `IsConnectedDivergent`, so no `X` term
  for it exists. The corresponding ε-on-unit value is captured by H5.3.
* **H5.5** `counit_X : ∀ g : HopfGen, counit (X g) = 0`

## Design rationale

In Connes–Kreimer 1998 the counit is defined on the *unstrict* generator
set as `ε([emptyGraph]) = 1, ε(otherwise) = 0`. The strict `HopfGen`
artifact (Sprint C1) excludes `[emptyGraph]` by *type* — the
`IsConnectedDivergent` predicate fails on it. Thus `counitGen` collapses
to a constant. The semantic content "ε(empty) = 1" is preserved as
"ε(1 : HopfH) = 1" via `AlgHom.map_one`, since `[emptyGraph]`
corresponds to the unit element under the standard identification.

This is an instance of the 21c-ontology principle: *the strict
representation may collapse a defining clause that is structurally
encoded elsewhere*. No information is lost; the constraint moves from
generator-level (ε on `[emptyGraph]`) to algebra-level (ε on `1`).
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

section PathW

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
         [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
         [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]

/-! ### H5.1 — `counitGen` -/

/-- **H5.1** — The Connes–Kreimer counit on strict generators is
constant zero. The "ε([emptyGraph]) = 1" clause from the unstrict CK
formulation is absorbed into `counit 1 = 1` (H5.3) since the strict
`HopfGen` subtype excludes the empty graph by construction. -/
def counitGen : HopfGen → ℚ := fun _ => 0

/-! ### H5.2 — `counit` via `MvPolynomial.aeval` -/

/-- **H5.2** — The Connes–Kreimer counit `ε : HopfH →ₐ[ℚ] ℚ`,
extended algebraically from `counitGen` via `MvPolynomial.aeval`. -/
noncomputable def counit : HopfH →ₐ[ℚ] ℚ :=
  MvPolynomial.aeval counitGen

/-! ### H5.3 — `counit_one` -/

/-- **H5.3** — `counit 1 = 1`, immediate from `AlgHom.map_one`. This
is the place where the Connes–Kreimer condition `ε([emptyGraph]) = 1`
lives, since `1 : HopfH = MvPolynomial.C 1` corresponds to the empty
graph under the standard generator identification. -/
@[simp] theorem counit_one : counit (1 : HopfH) = 1 := map_one _

/-! ### H5.5 — `counit_X` -/

/-- **H5.5** — On any generator `X g` (i.e. any nontrivial connected
1PI divergent class `g : HopfGen`), the counit returns 0. -/
@[simp] theorem counit_X (g : HopfGen) :
    counit (MvPolynomial.X g) = 0 := by
  unfold counit
  rw [MvPolynomial.aeval_X]
  rfl

/-- `counit (gen g) = 0` — `gen` is `MvPolynomial.X` definitionally. -/
@[simp] theorem counit_gen (g : HopfGen) : counit (gen g) = 0 := counit_X g

/-! ### Multiplicativity (free from `AlgHom`) -/

/-- `counit` is multiplicative — direct from `AlgHom.map_mul`. Used in
H5.6/H5.7 (counit axioms) downstream. -/
theorem counit_mul (a b : HopfH) :
    counit (a * b) = counit a * counit b := map_mul _ _ _

/-! ### H5.6 / H5.7 — counit axioms (P1: AlgHom equality + algHom_ext)

Mathlib's `Coalgebra` requires LinearMap equalities:

* `rTensor_counit_comp_comul : counit.rTensor A ∘ₗ comul = TensorProduct.mk R R A 1`
* `lTensor_counit_comp_comul : counit.lTensor A ∘ₗ comul = (TensorProduct.mk R A R).flip 1`

**Strategy P1 (AlgHom pivot):** both sides admit AlgHom upgrades:

* LHS: `(Algebra.TensorProduct.map counit (.id _ _)).comp coproduct_strict`,
  composing `counit : HopfH →ₐ[ℚ] ℚ` with `id : HopfH →ₐ[ℚ] HopfH` via the
  Algebra tensor product, all AlgHoms. Composition with the AlgHom
  `coproduct_strict` keeps it AlgHom.
* RHS: `Algebra.TensorProduct.includeRight : HopfH →ₐ[ℚ] ℚ ⊗[ℚ] HopfH`
  sends `a ↦ 1 ⊗ₜ a`, an AlgHom by construction.

The two AlgHoms agree on generators `X g` for `g : HopfGen`:

* `coproduct_strict (X g) = coproductGenClass_strict g` (H4.9-strict)
* unfold to the body `genG ⊗ 1 + 1 ⊗ genG + Σ [γ] ⊗ [Γ/γ]`
* apply `(ε ⊗ id)`: three terms collapse to `0 ⊗ 1 + 1 ⊗ genG + Σ 0 = 1 ⊗ genG`
* `genG = X g` via `Subtype.ext` on `HopfGen.toConnectedWF_toFeynmanGraph_toClass`
* matches `includeRight (X g) = 1 ⊗ X g`

`MvPolynomial.algHom_ext` then promotes the generator-level equality to
the full AlgHom equality. Finally we extract the LinearMap form via
`congrArg AlgHom.toLinearMap` and the identifications
`includeRight.toLinearMap = TensorProduct.mk ℚ ℚ HopfH 1` and
`(Algebra.TensorProduct.map counit id).toLinearMap = counit.toLinearMap.rTensor HopfH`. -/

section CounitAxioms

variable [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]

open MvPolynomial

omit [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract] in
/-- The internal `gen ⟨G.toFeynmanGraph.toClass, _⟩` in
`coproductGenClass_strict g` (where `G = (HopfGen.toConnectedWF g).1`)
equals `MvPolynomial.X g` modulo `Subtype.ext` (witness-irrelevant). -/
theorem genG_eq_X (g : HopfGen)
    (hCD : ((HopfGen.toConnectedWF g).1.toFeynmanGraph.toClass).IsConnectedDivergent) :
    gen ⟨(HopfGen.toConnectedWF g).1.toFeynmanGraph.toClass, hCD⟩
      = (MvPolynomial.X g : HopfH) := by
  unfold gen
  congr 1
  apply Subtype.ext
  exact HopfGen.toConnectedWF_toFeynmanGraph_toClass g

/-- **H5.6 generator-level** — On a generator `X g`, the AlgHom
`(Algebra.TensorProduct.map counit (.id _ _)).comp coproduct_strict`
agrees with `Algebra.TensorProduct.includeRight`. -/
private theorem rTensor_counit_coproduct_strict_X (g : HopfGen) :
    Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)
        (coproduct_strict (MvPolynomial.X g)) =
      (1 : ℚ) ⊗ₜ[ℚ] (MvPolynomial.X g : HopfH) := by
  rw [coproduct_strict_X]
  unfold coproductGenClass_strict coproductGen_strict
  -- After unfold the body is `genG ⊗ 1 + 1 ⊗ genG + ∑_γ (if hγ then ... else 0)`.
  -- `Algebra.TensorProduct.map counit id` distributes through `+` and `⊗ₜ`.
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    map_one, counit_gen, TensorProduct.zero_tmul, zero_add]
  -- Goal now: 1 ⊗ gen ⟨G.toFG.toClass, _⟩ + (Algebra.TensorProduct.map counit id) ∑_γ ... = 1 ⊗ X g
  -- The Σ collapses term-by-term: if-pos branch gives `counit (gen _) ⊗ gen _ = 0 ⊗ _ = 0`,
  -- if-neg branch is `0` already.
  rw [show (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH))
        (∑ γ ∈ _, _ : HopfH ⊗[ℚ] HopfH) = 0 from ?sumZero]
  case sumZero =>
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro γ _
    split_ifs with hγ
    · rw [Algebra.TensorProduct.map_tmul, counit_gen, TensorProduct.zero_tmul]
    · rw [map_zero]
  rw [add_zero]
  rw [genG_eq_X g _]

/-- **H5.6 AlgHom form** — Left counit axiom as an AlgHom equality. -/
theorem rTensor_counit_comp_coproduct_strict_algHom :
    (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)).comp coproduct_strict =
      Algebra.TensorProduct.includeRight := by
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, rTensor_counit_coproduct_strict_X]
  rfl

/-- **H5.7 generator-level** — On a generator `X g`, the AlgHom
`(Algebra.TensorProduct.map (.id _ _) counit).comp coproduct_strict`
agrees with `Algebra.TensorProduct.includeLeft`. -/
private theorem lTensor_counit_coproduct_strict_X (g : HopfGen) :
    Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit
        (coproduct_strict (MvPolynomial.X g)) =
      (MvPolynomial.X g : HopfH) ⊗ₜ[ℚ] (1 : ℚ) := by
  rw [coproduct_strict_X]
  unfold coproductGenClass_strict coproductGen_strict
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    map_one, counit_gen, TensorProduct.tmul_zero, add_zero]
  rw [show (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit)
        (∑ γ ∈ _, _ : HopfH ⊗[ℚ] HopfH) = 0 from ?sumZero]
  case sumZero =>
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro γ _
    split_ifs with hγ
    · rw [Algebra.TensorProduct.map_tmul, counit_gen, TensorProduct.tmul_zero]
    · rw [map_zero]
  rw [add_zero]
  rw [genG_eq_X g _]

/-- **H5.7 AlgHom form** — Right counit axiom as an AlgHom equality. -/
theorem lTensor_counit_comp_coproduct_strict_algHom :
    (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit).comp coproduct_strict =
      Algebra.TensorProduct.includeLeft := by
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, lTensor_counit_coproduct_strict_X]
  rfl

/-! ### LinearMap form (Mathlib `Coalgebra` field shape) -/

/-- `(Algebra.TensorProduct.map counit id).toLinearMap` agrees with
`counit.toLinearMap.rTensor HopfH` as LinearMaps `HopfH ⊗ HopfH →ₗ[ℚ] ℚ ⊗ HopfH`. -/
private theorem map_counit_id_toLinearMap_eq_rTensor :
    (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)).toLinearMap =
      counit.toLinearMap.rTensor HopfH := by
  ext a b
  simp [LinearMap.rTensor_tmul]

/-- `(Algebra.TensorProduct.map id counit).toLinearMap` agrees with
`counit.toLinearMap.lTensor HopfH` as LinearMaps. -/
private theorem map_id_counit_toLinearMap_eq_lTensor :
    (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit).toLinearMap =
      counit.toLinearMap.lTensor HopfH := by
  ext a b
  simp [LinearMap.lTensor_tmul]

/-- `Algebra.TensorProduct.includeRight.toLinearMap = TensorProduct.mk ℚ ℚ HopfH 1`. -/
private theorem includeRight_toLinearMap_eq_mk :
    (Algebra.TensorProduct.includeRight : HopfH →ₐ[ℚ] ℚ ⊗[ℚ] HopfH).toLinearMap =
      TensorProduct.mk ℚ ℚ HopfH 1 := by
  ext a
  simp [Algebra.TensorProduct.includeRight_apply, TensorProduct.mk_apply]

/-- `Algebra.TensorProduct.includeLeft.toLinearMap = (TensorProduct.mk ℚ HopfH ℚ).flip 1`. -/
private theorem includeLeft_toLinearMap_eq_mk_flip :
    (Algebra.TensorProduct.includeLeft : HopfH →ₐ[ℚ] HopfH ⊗[ℚ] ℚ).toLinearMap =
      (TensorProduct.mk ℚ HopfH ℚ).flip 1 := by
  ext a
  simp [TensorProduct.mk_apply]

/-- **H5.6** — Left counit axiom in Mathlib `Coalgebra` LinearMap form. -/
theorem rTensor_counit_comp_coproduct_strict :
    counit.toLinearMap.rTensor HopfH ∘ₗ coproduct_strict.toLinearMap =
      TensorProduct.mk ℚ ℚ HopfH 1 := by
  have h := congrArg AlgHom.toLinearMap rTensor_counit_comp_coproduct_strict_algHom
  rw [AlgHom.comp_toLinearMap, map_counit_id_toLinearMap_eq_rTensor,
      includeRight_toLinearMap_eq_mk] at h
  exact h

/-- **H5.7** — Right counit axiom in Mathlib `Coalgebra` LinearMap form. -/
theorem lTensor_counit_comp_coproduct_strict :
    counit.toLinearMap.lTensor HopfH ∘ₗ coproduct_strict.toLinearMap =
      (TensorProduct.mk ℚ HopfH ℚ).flip 1 := by
  have h := congrArg AlgHom.toLinearMap lTensor_counit_comp_coproduct_strict_algHom
  rw [AlgHom.comp_toLinearMap, map_id_counit_toLinearMap_eq_lTensor,
      includeLeft_toLinearMap_eq_mk_flip] at h
  exact h

end CounitAxioms

/-! ### H5.6F / H5.7F — Forest counit axioms

Mirror of `H5.6` / `H5.7` for the admissible-forest strict coproduct
`coproduct_strict_forest`. The counit absorbs every forest summand
because each summand is a tensor of two generators, both of which the
counit sends to zero.

Strategy (forest version):

1. **First-factor zero**: for `A ∈ properDisjointAdmissibleDivergentSubgraphs`,
   `counit (A.toHopfH) = 0` because `A.elements` is nonempty (from
   `0 < A.internalEdges.card`) and every component contributes a
   `gen γ.toHopfGen` factor whose counit is `0`.
2. **Generator-level expand**: `coproduct_strict_forest (X g)` expands as
   `X g ⊗ 1 + 1 ⊗ X g + ∑_{A ∈ ...} A.toHopfH ⊗ gen (right A)`.
3. **(counit ⊗ id) collapse**: first term drops by `counit (X g) = 0`,
   each forest summand drops by step 1, only `1 ⊗ X g` survives.
4. AlgHom equality is then upgraded to LinearMap equality through the
   same `Algebra.TensorProduct.includeRight/Left` bridge as connected. -/

section ForestCounitAxioms

variable [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

open MvPolynomial

/-- **Forest counit on a component product.** For an admissible subgraph
whose `elements` carrier is nonempty, the counit annihilates the product
`A.toHopfH = ∏ γ ∈ A.elements.attach, gen γ.toHopfGen`. -/
private theorem counit_admissibleSubgraph_toHopfH_eq_zero
    {G : FeynmanGraph} (A : AdmissibleSubgraph G)
    (hNe : A.elements.Nonempty) :
    counit A.toHopfH = 0 := by
  unfold AdmissibleSubgraph.toHopfH
  rw [map_prod]
  obtain ⟨γ, hγ⟩ := hNe
  apply Finset.prod_eq_zero (i := γ) hγ
  -- componentToHopfH on γ ∈ A.elements yields a single generator, hence
  -- counit returns 0.
  unfold AdmissibleSubgraph.componentToHopfH
  rw [dif_pos hγ]
  exact counit_gen _

/-- A proper-disjoint admissible divergent subgraph has nonempty `elements`,
because `0 < A.internalEdges.card` forces at least one component. -/
private theorem AdmissibleSubgraph.elements_nonempty_of_internalEdges_pos
    {G : FeynmanGraph} {A : AdmissibleSubgraph G}
    (hCard : 0 < A.internalEdges.card) :
    A.elements.Nonempty := by
  by_contra hEmpty
  rw [Finset.not_nonempty_iff_eq_empty] at hEmpty
  -- `A.internalEdges = ∑ γ ∈ A.elements, γ.internalEdges`; with empty elements,
  -- the sum is 0 and its card is 0, contradicting `hCard`.
  have : A.internalEdges = 0 := by
    show (∑ γ ∈ A.elements, γ.internalEdges) = 0
    rw [hEmpty, Finset.sum_empty]
  rw [this] at hCard
  simp at hCard

/-- Forest summand annihilation by `(counit ⊗ id)`. -/
private theorem counit_admissibleForestStrictSummand_eq_zero
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G A
          (FeynmanGraph.admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)
        (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars G hCD A) =
      0 := by
  rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
    G hCD A hA]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  rw [counit_admissibleSubgraph_toHopfH_eq_zero A
    (AdmissibleSubgraph.elements_nonempty_of_internalEdges_pos
      (((G.mem_properDisjointAdmissibleDivergentSubgraphs A).mp hA).2.2.1))]
  rw [TensorProduct.zero_tmul]

/-- Forest summand annihilation by `(id ⊗ counit)`: the right factor is a
single `gen (...)`, which the counit sends to 0. -/
private theorem lTensor_counit_admissibleForestStrictSummand_eq_zero
    (G : FeynmanGraph)
    (hCD : ∀ A : AdmissibleSubgraph G,
      ∀ hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G A
          (FeynmanGraph.admissibleForestCanonicalStarOf G A hA)).IsConnectedDivergent)
    (A : AdmissibleSubgraph G)
    (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphs) :
    Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit
        (FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars G hCD A) =
      0 := by
  rw [FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars_of_mem
    G hCD A hA]
  rw [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
  rw [counit_gen]
  rw [TensorProduct.tmul_zero]

/-- **H5.6F generator-level** — On a generator `X g`, the AlgHom
`(map counit id).comp coproduct_strict_forest` sends `X g` to `1 ⊗ X g`. -/
private theorem rTensor_counit_coproduct_strict_forest_X (g : HopfGen) :
    Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)
        (coproduct_strict_forest (MvPolynomial.X g)) =
      (1 : ℚ) ⊗ₜ[ℚ] (MvPolynomial.X g : HopfH) := by
  rw [coproduct_strict_forest_X, coproductGenClass_strict_forest_eq]
  unfold coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
    coproductGen_strict_forestWithCanonicalStars
  -- Body: genG ⊗ 1 + 1 ⊗ genG + ∑_{A ∈ ...} forestSummand. Distribute (counit ⊗ id).
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    map_one, counit_gen, TensorProduct.zero_tmul, zero_add]
  -- Forest sum: each summand is annihilated by counit ⊗ id (first factor is A.toHopfH).
  rw [show (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH))
        (∑ A ∈ _, _ : HopfH ⊗[ℚ] HopfH) = 0 from ?sumZero]
  case sumZero =>
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro A hA
    rw [Finset.mem_filter] at hA
    exact counit_admissibleForestStrictSummand_eq_zero _ _ A hA.1
  rw [add_zero]
  rw [genG_eq_X g _]

/-- **H5.6F AlgHom form** — Forest left counit axiom as an AlgHom equality. -/
theorem rTensor_counit_comp_coproduct_strict_forest_algHom :
    (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)).comp coproduct_strict_forest =
      Algebra.TensorProduct.includeRight := by
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, rTensor_counit_coproduct_strict_forest_X]
  rfl

/-- **H5.7F generator-level** — On a generator `X g`, the AlgHom
`(map id counit).comp coproduct_strict_forest` sends `X g` to `X g ⊗ 1`. -/
private theorem lTensor_counit_coproduct_strict_forest_X (g : HopfGen) :
    Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit
        (coproduct_strict_forest (MvPolynomial.X g)) =
      (MvPolynomial.X g : HopfH) ⊗ₜ[ℚ] (1 : ℚ) := by
  rw [coproduct_strict_forest_X, coproductGenClass_strict_forest_eq]
  unfold coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation
    coproductGen_strict_forestWithCanonicalStars
  simp only [map_add, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
    map_one, counit_gen, TensorProduct.tmul_zero, add_zero]
  rw [show (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit)
        (∑ A ∈ _, _ : HopfH ⊗[ℚ] HopfH) = 0 from ?sumZero]
  case sumZero =>
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro A hA
    rw [Finset.mem_filter] at hA
    exact lTensor_counit_admissibleForestStrictSummand_eq_zero _ _ A hA.1
  rw [add_zero]
  rw [genG_eq_X g _]

/-- **H5.7F AlgHom form** — Forest right counit axiom as an AlgHom equality. -/
theorem lTensor_counit_comp_coproduct_strict_forest_algHom :
    (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit).comp coproduct_strict_forest =
      Algebra.TensorProduct.includeLeft := by
  apply MvPolynomial.algHom_ext
  intro g
  rw [AlgHom.comp_apply, lTensor_counit_coproduct_strict_forest_X]
  rfl

/-! #### LinearMap form for forest counit axioms (Mathlib `Coalgebra` shape) -/

private theorem map_counit_id_toLinearMap_eq_rTensor_forest :
    (Algebra.TensorProduct.map counit (AlgHom.id ℚ HopfH)).toLinearMap =
      counit.toLinearMap.rTensor HopfH := by
  ext a b
  simp [LinearMap.rTensor_tmul]

private theorem map_id_counit_toLinearMap_eq_lTensor_forest :
    (Algebra.TensorProduct.map (AlgHom.id ℚ HopfH) counit).toLinearMap =
      counit.toLinearMap.lTensor HopfH := by
  ext a b
  simp [LinearMap.lTensor_tmul]

/-- **H5.6F** — Forest left counit axiom in Mathlib `Coalgebra` LinearMap form. -/
theorem rTensor_counit_comp_coproduct_strict_forest :
    counit.toLinearMap.rTensor HopfH ∘ₗ coproduct_strict_forest.toLinearMap =
      TensorProduct.mk ℚ ℚ HopfH 1 := by
  have h := congrArg AlgHom.toLinearMap rTensor_counit_comp_coproduct_strict_forest_algHom
  rw [AlgHom.comp_toLinearMap, map_counit_id_toLinearMap_eq_rTensor_forest,
      includeRight_toLinearMap_eq_mk] at h
  exact h

/-- **H5.7F** — Forest right counit axiom in Mathlib `Coalgebra` LinearMap form. -/
theorem lTensor_counit_comp_coproduct_strict_forest :
    counit.toLinearMap.lTensor HopfH ∘ₗ coproduct_strict_forest.toLinearMap =
      (TensorProduct.mk ℚ HopfH ℚ).flip 1 := by
  have h := congrArg AlgHom.toLinearMap lTensor_counit_comp_coproduct_strict_forest_algHom
  rw [AlgHom.comp_toLinearMap, map_id_counit_toLinearMap_eq_lTensor_forest,
      includeLeft_toLinearMap_eq_mk_flip] at h
  exact h

end ForestCounitAxioms

end PathW

end GaugeGeometry.QFT.Combinatorial
