import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftChoice

/-!
# R-6c-2d-4a — compatibility expansions by regrouping (`ofRegroup`)

The key planning insight of R-6c-2d-2b: the two expansion fields of
`ResolvedCoproductH58Compatibility` (`lhsExpansion`/`rhsExpansion`) are **pure bookkeeping** — they do
*not* need the product-of-sums (component-choice) expansion.  Only the third field, `reindex`, is the
genuine σ-cover geometry.  This file discharges the two expansions and packages everything into a
constructor `ofRegroup` that takes **only** `reindex`.

The grouping (computed by hand in R-6c-2d-3, formalised here):

  `coassocLeft  (X x) = P3 x + branchSum x`,   `branchSum x = leftLeak x  + coassocLeftTail  (forestSum x.1)`
  `coassocRight (X x) = P3 x + imageSum x`,    `imageSum  x = rightLeak x + coassocRightTail (forestSum x.1)`

with the **shared** fully-primitive part `P3 x = coassocPrimitivePart x` and the primitive *leaks*
`leftLeak x = assoc(forestSum x.1 ⊗ 1)`, `rightLeak x = 1 ⊗ forestSum x.1` (the forest part of
`Δᵣ(X x)` that leaks through the *primitive* tail of the iterated coproduct).  Everything is
representative-free (in terms of `forestSum x.1`).

Landed:

* `coassocPrimitivePart` — the shared `P3`;
* `coassocLeftTail_primitive` / `coassocRightTail_primitive` — the primitive tails split as `P3` plus
  their leak (the only genuine computation, by `map_*` + `assoc_tmul` + `abel`);
* `ResolvedCoproductProperForestData.regroupBranchSum` / `regroupImageSum` — the global branch/image
  sums (leak + the forest-sum tail);
* `ResolvedCoproductProperForestData.lhsExpansion` / `rhsExpansion` — the two expansions, by
  bookkeeping (`map_add` + the primitive lemma + `abel`);
* `ResolvedCoproductH58Compatibility.ofRegroup` — **the constructor: given only**
  `reindex : ∀ x, imageSum x = branchSum x`, returns the full compatibility (hence `coassoc_gen`).

So R-6c reduces to a single genuine theorem: the σ-cover reindex.  No facade, no flat term, no
`forgetHopf`, no product-of-sums (deferred to the reindex).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The genuinely-shared fully-primitive part `P3` of both iterated coproducts on `X x`. -/
noncomputable def coassocPrimitivePart (x : ResolvedHopfGen) : ResolvedHopfH3 :=
  MvPolynomial.X x ⊗ₜ[ℚ] ((1 : ResolvedHopfH) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
  + (1 : ResolvedHopfH) ⊗ₜ[ℚ] (MvPolynomial.X x ⊗ₜ[ℚ] (1 : ResolvedHopfH))
  + (1 : ResolvedHopfH) ⊗ₜ[ℚ] ((1 : ResolvedHopfH) ⊗ₜ[ℚ] MvPolynomial.X x)

/-- The left iterated coproduct on the primitive part: `P3` plus the left forest leak
`assoc(forestSum x.1 ⊗ 1)`. -/
theorem ResolvedCoproductProperForestData.coassocLeftTail_primitive (x : ResolvedHopfGen) :
    D.coassocLeftTail (resolvedCoproductGenPrimitive x)
      = coassocPrimitivePart x
        + (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.toGenSupply.forestSum x.1) ⊗ₜ[ℚ] (1 : ResolvedHopfH)) := by
  rw [resolvedCoproductGenPrimitive, ResolvedCoproductProperForestData.coassocLeftTail]
  simp only [AlgHom.comp_apply, map_add, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one,
    AlgEquiv.coe_algHom]
  simp only [ResolvedCoproductProperForestData.coproduct, ResolvedCoproductGenSupply.coproduct_X,
    ResolvedCoproductGenSupply.gen, resolvedCoproductGenPrimitive]
  simp only [TensorProduct.add_tmul, map_add, Algebra.TensorProduct.one_def,
    Algebra.TensorProduct.assoc_tmul, AlgEquiv.coe_algHom]
  unfold coassocPrimitivePart
  abel

/-- The right iterated coproduct on the primitive part: `P3` plus the right forest leak
`1 ⊗ forestSum x.1` (no associator on the right). -/
theorem ResolvedCoproductProperForestData.coassocRightTail_primitive (x : ResolvedHopfGen) :
    D.coassocRightTail (resolvedCoproductGenPrimitive x)
      = coassocPrimitivePart x
        + (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.toGenSupply.forestSum x.1) := by
  rw [resolvedCoproductGenPrimitive, ResolvedCoproductProperForestData.coassocRightTail]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_add, map_one]
  simp only [ResolvedCoproductProperForestData.coproduct, ResolvedCoproductGenSupply.coproduct_X,
    ResolvedCoproductGenSupply.gen, resolvedCoproductGenPrimitive]
  simp only [TensorProduct.tmul_add, Algebra.TensorProduct.one_def]
  unfold coassocPrimitivePart
  abel

/-- The global branch-side sum on `X x`: the left forest leak plus the left tail of the forest sum. -/
noncomputable def ResolvedCoproductProperForestData.regroupBranchSum (x : ResolvedHopfGen) :
    ResolvedHopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
      ((D.toGenSupply.forestSum x.1) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
  + D.coassocLeftTail (D.toGenSupply.forestSum x.1)

/-- The global image-side sum on `X x`: the right forest leak plus the right tail of the forest sum. -/
noncomputable def ResolvedCoproductProperForestData.regroupImageSum (x : ResolvedHopfGen) :
    ResolvedHopfH3 :=
  (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.toGenSupply.forestSum x.1)
  + D.coassocRightTail (D.toGenSupply.forestSum x.1)

/-- `D.coproduct (X x)` is the generator coproduct `primitive + forest sum`. -/
theorem ResolvedCoproductProperForestData.coproduct_X_eq (x : ResolvedHopfGen) :
    D.coproduct (MvPolynomial.X x)
      = resolvedCoproductGenPrimitive x + D.toGenSupply.forestSum x.1 := by
  rw [ResolvedCoproductProperForestData.coproduct, ResolvedCoproductGenSupply.coproduct_X]
  rfl

/-- **R-6c-2d-4a — the left expansion by regrouping** (bookkeeping: `coassocLeft = coassocLeftTail ∘
Δᵣ`, split the generator coproduct, apply the primitive-tail lemma, `abel`). -/
theorem ResolvedCoproductProperForestData.lhsExpansion (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = coassocPrimitivePart x + D.regroupBranchSum x := by
  rw [D.coassocLeft_apply, D.coproduct_X_eq, map_add, D.coassocLeftTail_primitive]
  unfold ResolvedCoproductProperForestData.regroupBranchSum
  abel

/-- **R-6c-2d-4a — the right expansion by regrouping** (mirror of `lhsExpansion`). -/
theorem ResolvedCoproductProperForestData.rhsExpansion (x : ResolvedHopfGen) :
    D.coassocRight (MvPolynomial.X x) = coassocPrimitivePart x + D.regroupImageSum x := by
  rw [D.coassocRight_apply, D.coproduct_X_eq, map_add, D.coassocRightTail_primitive]
  unfold ResolvedCoproductProperForestData.regroupImageSum
  abel

/-- **R-6c-2d-4a — the regroup constructor.**  Given only the global σ-cover reindex
`imageSum x = branchSum x`, assemble the full `ResolvedCoproductH58Compatibility` (with the two
expansions discharged by bookkeeping).  Then `coassoc_gen` fires.  This collapses all of R-6c to a
single genuine theorem: the resolved σ-cover reindex. -/
noncomputable def ResolvedCoproductH58Compatibility.ofRegroup
    (reindex : ∀ x : ResolvedHopfGen, D.regroupImageSum x = D.regroupBranchSum x) :
    ResolvedCoproductH58Compatibility D where
  primitivePart := coassocPrimitivePart
  branchSum := D.regroupBranchSum
  imageSum := D.regroupImageSum
  lhsExpansion := D.lhsExpansion
  rhsExpansion := D.rhsExpansion
  reindex := reindex

end GaugeGeometry.QFT.Combinatorial
