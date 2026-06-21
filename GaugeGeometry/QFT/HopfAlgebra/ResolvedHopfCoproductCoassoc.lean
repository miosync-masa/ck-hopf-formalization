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
  per generator, a shared `primitivePart` and a `branchSum` / `imageSum` in `ResolvedHopfH⊗³`, the two
  iterated-coproduct expansions (`lhsExpansion`, `rhsExpansion`), and the **global** id-bearing
  reindex (`reindex : imageSum x = branchSum x`);
* `ResolvedCoproductH58Compatibility.coassoc_gen` — the **capstone reduction**: from the frontier
  fields, `Δᵣ`-coassociativity holds on every generator `X x` (chaining the two expansions through the
  global reindex).  This shows the structure is *exactly* the right cut; the genuine geometry
  (discharging `lhsExpansion`/`rhsExpansion`/`reindex` for a concrete instance) is R-6c-2.

  **R-6c-2d-fix:** the cut is *global*, not per-outer-forest.  R-6c-2d-3 showed the per-`A`
  image/branch terms differ (left inner sub-forests are component-subforests, right are
  quotient-subforests); they agree only after the σ-cover bijection.  So `branchSum`/`imageSum` are
  single totals and `reindex` is a global cover sum_bij (`ResolvedH58TermReindex.reindex`), not a
  per-`A` `Finset.sum_congr`.

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

/-- **R-6c-1/2d-fix — the resolved-term H5.8 coassociativity frontier (single-sum form).**

This structure *names the cut* of `Δᵣ`-coassociativity, entirely in resolved terms (`ResolvedHopfH⊗³`).
The cut is at the **global** level — the actual coassociativity grouping is

  `coassocLeft (X x)  = primitivePart x + branchSum x`
  `coassocRight (X x) = primitivePart x + imageSum x`

with the **shared** `primitivePart x` (the genuinely common low-order terms — the three
fully-primitive terms `X x ⊗ 1 ⊗ 1`, `1 ⊗ X x ⊗ 1`, `1 ⊗ 1 ⊗ X x`), and a single **global** reindex

  `imageSum x = branchSum x`.

The reindex is *not* a per-outer-forest equality (R-6c-2d-3 showed the per-`A` image/branch terms
differ — left inner sub-forests are component-subforests, right are quotient-subforests; they match
only after the σ-cover bijection).  It is a **global cover sum_bij**, exactly the shape of
`ResolvedH58TermReindex.reindex` (R-6c-2a): image carrier = forest ⊔ mixed.  So `branchSum`/`imageSum`
are single resolved-triple-tensor elements, and `reindex` is filled by the cover spine.

`coassoc_gen` then chains `lhsExpansion`, `reindex`, `rhsExpansion`.  The hard geometry is the three
fields (the two expansions + the reindex), discharged for a concrete instance in R-6c-2. -/
structure ResolvedCoproductH58Compatibility (D : ResolvedCoproductProperForestData) where
  /-- The shared low-order part of both iterated coproducts on `X x` (the fully-primitive terms common
  to LHS and RHS). -/
  primitivePart : ResolvedHopfGen → ResolvedHopfH3
  /-- The branch-side (forest+mixed) total sum on `X x`, in resolved triple-tensor terms. -/
  branchSum : ResolvedHopfGen → ResolvedHopfH3
  /-- The image-side (quotient) total sum on `X x`, in resolved triple-tensor terms. -/
  imageSum : ResolvedHopfGen → ResolvedHopfH3
  /-- **The H5.8 cut, LHS**: the left iterated coproduct on a generator is its primitive part plus the
  branch-side sum. -/
  lhsExpansion : ∀ (x : ResolvedHopfGen),
    D.coassocLeft (MvPolynomial.X x) = primitivePart x + branchSum x
  /-- **The H5.8 cut, RHS**: the right iterated coproduct on a generator is its primitive part plus
  the image-side sum. -/
  rhsExpansion : ∀ (x : ResolvedHopfGen),
    D.coassocRight (MvPolynomial.X x) = primitivePart x + imageSum x
  /-- **The id-bearing, facade-free global reindex**: the image-side sum equals the branch-side sum.
  This is the resolved replay of the flat `outer_sum_reindex`/`sum_reindex` — a global cover sum_bij
  (`ResolvedH58TermReindex.reindex`), whose bijection is now a genuine bijection of id-bearing
  resolved forest classes, so the R-5 `hQuotBij` wall dissolves natively (re-proved here, not lifted
  from flat). -/
  reindex : ∀ (x : ResolvedHopfGen), imageSum x = branchSum x

namespace ResolvedCoproductH58Compatibility

variable {D : ResolvedCoproductProperForestData} (C : ResolvedCoproductH58Compatibility D)

include C in
/-- **R-6c-1 capstone — `Δᵣ`-coassociativity on a generator, from the frontier.**  Chaining the two
expansions through the global reindex: the left and right iterated coproducts agree on every generator
`X x`.  This shows `ResolvedCoproductH58Compatibility` is *exactly* the H5.8 cut needed for
coassociativity; the genuine geometry (its three hard fields) is R-6c-2. -/
theorem coassoc_gen (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) := by
  rw [C.lhsExpansion x, C.rhsExpansion x, C.reindex x]

end ResolvedCoproductH58Compatibility

end GaugeGeometry.QFT.Combinatorial
