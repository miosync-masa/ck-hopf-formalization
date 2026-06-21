import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductSupply
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# R-6c-1 — the resolved-term H5.8 coassociativity frontier

This file **names the type of the H5.8 coassociativity cut** for `Δᵣ` on the resolved-generator
algebra `ResolvedHopfH`, *without* yet proving the geometry.  It is the resolved-term **native
replay** of the flat H5.8 reindex (`h58_resolved_carrier_double_sum_reindex` in
`ResolvedActualSigmaCover`), **not** a plug-in of it: that theorem lives in flat `HopfH ⊗ HopfH ⊗
HopfH` terms, whereas `Δᵣ`-coassociativity lives in `ResolvedHopfH ⊗ ResolvedHopfH ⊗ ResolvedHopfH`,
and `forgetHopf` is non-injective so a flat equality cannot be lifted.  Same mathematics, different
algebra carrier ⇒ genuine re-statement.  The payoff vs the flat wall (R-5): the carrier index is now
id-bearing, so the facade-true `hQuotBij` boundary dissolves — but that is re-proved here on the
resolved carrier, not borrowed.

Landed here (statement layer):

* `coassocLeft` / `coassocRight` — the two iterated coproducts
  `(Δᵣ ⊗ id) ∘ Δᵣ` (post-composed with the associator) and `(id ⊗ Δᵣ) ∘ Δᵣ`, both landing in the
  canonical `ResolvedHopfH ⊗ (ResolvedHopfH ⊗ ResolvedHopfH)` (the standard `Bialgebra.ofAlgHom`
  coassociativity shape, every factor a `ResolvedHopfGen`);
* `ResolvedCoproductH58Compatibility D` — the **frontier structure** fixing what the H5.8 cut *is*:
  a per-generator resolved outer carrier with image-side / branch-side inner sums in
  `ResolvedHopfH⊗³`, the two iterated-coproduct expansions (`lhsExpansion`, `rhsExpansion`), and the
  id-bearing per-outer agreement (`resolvedTermAgreement`);
* `ResolvedCoproductH58Compatibility.resolved_h58_reindex` — the **spine theorem**: the outer sum of
  image-side terms equals the outer sum of branch-side terms (the resolved analogue of the flat
  `outer_sum_reindex`, by `Finset.sum_congr`);
* `ResolvedCoproductH58Compatibility.coassoc_gen` — the **capstone reduction**: from the frontier
  fields, `Δᵣ`-coassociativity holds on every generator `X x` (chaining the two expansions through the
  reindex spine).  This shows the structure is *exactly* the right cut; the genuine geometry
  (discharging `lhsExpansion`/`rhsExpansion`/`resolvedTermAgreement` for a concrete instance) is
  R-6c-2.

No flat `HopfH` term theorem is invoked, no `forgetHopf` lift, no flat `splitPhiBranchReindexing`,
no facade/gated theorem.  Everything is parametric in the proper-forest data `D`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- The canonical triple-tensor target of the iterated coproduct (right-associated): every factor a
`ResolvedHopfGen`-algebra. -/
abbrev ResolvedHopfH3 : Type _ :=
  ResolvedHopfH ⊗[ℚ] (ResolvedHopfH ⊗[ℚ] ResolvedHopfH)

/-- `Δᵣ` as an algebra hom, from the proper-forest data. -/
noncomputable def ResolvedCoproductProperForestData.coproduct
    (D : ResolvedCoproductProperForestData) :
    ResolvedHopfH →ₐ[ℚ] ResolvedHopfH ⊗[ℚ] ResolvedHopfH :=
  D.toGenSupply.coproduct

/-- The **left** iterated coproduct `(Δᵣ ⊗ id) ∘ Δᵣ`, post-composed with the associator to land in
the canonical right-associated triple tensor (the standard coassociativity LHS shape). -/
noncomputable def ResolvedCoproductProperForestData.coassocLeft
    (D : ResolvedCoproductProperForestData) : ResolvedHopfH →ₐ[ℚ] ResolvedHopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom.comp
    ((Algebra.TensorProduct.map D.coproduct (AlgHom.id ℚ ResolvedHopfH)).comp D.coproduct)

/-- The **right** iterated coproduct `(id ⊗ Δᵣ) ∘ Δᵣ` (already right-associated). -/
noncomputable def ResolvedCoproductProperForestData.coassocRight
    (D : ResolvedCoproductProperForestData) : ResolvedHopfH →ₐ[ℚ] ResolvedHopfH3 :=
  (Algebra.TensorProduct.map (AlgHom.id ℚ ResolvedHopfH) D.coproduct).comp D.coproduct

/-- **R-6c-1 — the resolved-term H5.8 coassociativity frontier.**

This structure *names the cut* of `Δᵣ`-coassociativity into the H5.8 double sum, entirely in
resolved terms (`ResolvedHopfH⊗³`).  For each generator `x`:

* an outer (proper-forest) index `OuterIdx x` with a finite `outerCarrier x`;
* an **image-side** inner sum `innerImageSum x A` and a **branch-side** inner sum
  `innerBranchSum x A` per outer forest, both in `ResolvedHopfH⊗³` (the resolved analogues of the flat
  `innerImageSum`/`innerBranchSum`);
* a shared low-order `primitivePart x` (the once/twice-primitive terms common to both iterated
  coproducts);
* the two **expansions** identifying each iterated coproduct on `X x` with `primitivePart x` plus its
  outer sum (`lhsExpansion`: the left coproduct = primitive + branch sum; `rhsExpansion`: the right
  coproduct = primitive + image sum);
* `resolvedTermAgreement`: the **id-bearing, facade-free** per-outer reindex — image-side term =
  branch-side term for every outer forest (the resolved replay of the flat per-`A` `sum_reindex`,
  whose bijection is now a genuine bijection of id-bearing resolved forest classes).

The hard geometry is exactly the three fields `lhsExpansion`/`rhsExpansion`/`resolvedTermAgreement`;
R-6c-1 only fixes their *type*, R-6c-2 discharges them for a concrete instance. -/
structure ResolvedCoproductH58Compatibility (D : ResolvedCoproductProperForestData) where
  /-- The outer (proper-forest) H5.8 index, per generator. -/
  OuterIdx : ResolvedHopfGen → Type
  /-- The finite outer carrier, per generator. -/
  outerCarrier : (x : ResolvedHopfGen) → Finset (OuterIdx x)
  /-- The image-side (quotient) inner sum per outer forest, in resolved triple-tensor terms. -/
  innerImageSum : (x : ResolvedHopfGen) → OuterIdx x → ResolvedHopfH3
  /-- The branch-side (forest+mixed) inner sum per outer forest, in resolved triple-tensor terms. -/
  innerBranchSum : (x : ResolvedHopfGen) → OuterIdx x → ResolvedHopfH3
  /-- The shared low-order part of both iterated coproducts on `X x` (the primitive/once-primitive
  terms common to LHS and RHS). -/
  primitivePart : ResolvedHopfGen → ResolvedHopfH3
  /-- **The H5.8 cut, LHS**: the left iterated coproduct on a generator is its primitive part plus the
  branch-side outer sum. -/
  lhsExpansion : ∀ (x : ResolvedHopfGen),
    D.coassocLeft (MvPolynomial.X x)
      = primitivePart x + ∑ A ∈ outerCarrier x, innerBranchSum x A
  /-- **The H5.8 cut, RHS**: the right iterated coproduct on a generator is its primitive part plus
  the image-side outer sum. -/
  rhsExpansion : ∀ (x : ResolvedHopfGen),
    D.coassocRight (MvPolynomial.X x)
      = primitivePart x + ∑ A ∈ outerCarrier x, innerImageSum x A
  /-- **The id-bearing, facade-free reindex**: per outer forest, the image-side term equals the
  branch-side term.  This is the resolved replay of the flat per-`A` `sum_reindex` — its bijection is
  now a genuine bijection of id-bearing resolved forest classes, so the R-5 `hQuotBij` wall dissolves
  natively (re-proved here, not lifted from flat). -/
  resolvedTermAgreement : ∀ (x : ResolvedHopfGen) (A : OuterIdx x), A ∈ outerCarrier x →
    innerImageSum x A = innerBranchSum x A

namespace ResolvedCoproductH58Compatibility

variable {D : ResolvedCoproductProperForestData} (C : ResolvedCoproductH58Compatibility D)

/-- **R-6c-1 spine — the resolved H5.8 double-sum reindex.**  The outer sum of image-side terms
equals the outer sum of branch-side terms, assembled from the per-outer id-bearing agreement by
`Finset.sum_congr`.  The resolved-term analogue of the flat `outer_sum_reindex`; facade-free. -/
theorem resolved_h58_reindex (x : ResolvedHopfGen) :
    ∑ A ∈ C.outerCarrier x, C.innerImageSum x A
      = ∑ A ∈ C.outerCarrier x, C.innerBranchSum x A :=
  Finset.sum_congr rfl (fun A hA => C.resolvedTermAgreement x A hA)

include C in
/-- **R-6c-1 capstone — `Δᵣ`-coassociativity on a generator, from the frontier.**  Chaining the two
expansions through the reindex spine: the left and right iterated coproducts agree on every generator
`X x`.  This shows `ResolvedCoproductH58Compatibility` is *exactly* the H5.8 cut needed for
coassociativity; the genuine geometry (its three hard fields) is R-6c-2. -/
theorem coassoc_gen (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) := by
  rw [C.lhsExpansion x, C.rhsExpansion x, C.resolved_h58_reindex x]

end ResolvedCoproductH58Compatibility

end GaugeGeometry.QFT.Combinatorial
