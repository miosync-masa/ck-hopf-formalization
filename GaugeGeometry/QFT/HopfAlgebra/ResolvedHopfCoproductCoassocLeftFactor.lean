import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductEq

/-!
# R-6c-heart-5c-1b — the left-factor equality (infrastructure: `resolvedForestLeftTerm_union`)

`product_eq` reduced (5c-1) to two factor equalities; the left one is

  `leftFactorProduct s = resolvedSelectedOuterTerm (imageOf s) = resolvedForestLeftTerm selectedOuter`,

where `selectedOuter = leftOf ∪ promotedOf`.  The structural engine for that is the fact that the
forest left term (a product of component generators) splits over a disjoint union of forests.

The obstacle is that `resolvedForestLeftTerm A = ∏ γ ∈ A.elements.attach, X (componentGen γ.1 (A.cd γ))`
carries the membership proof inside the generator's CD argument.  Since the generator is
**proof-irrelevant** in that argument, the term depends only on the bare component; this file factors
that out via a proof-free `resolvedComponentGenTerm`, rewrites `resolvedForestLeftTerm` as a plain
product over `A.elements` (`resolvedForestLeftTerm_eq_prod`), and then splits a disjoint union with
`Finset.prod_union`.

Landed:

* `resolvedComponentGenTerm` — the proof-free per-component generator term (`dite` on CD);
* `resolvedForestLeftTerm_eq_prod` — `resolvedForestLeftTerm A = ∏ δ ∈ A.elements, resolvedComponentGenTerm δ`;
* `resolvedForestLeftTerm_union` — the forest left term splits over a Finset-disjoint union.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The component-partition split of
`leftFactorProduct`, the promote-gen equality, and the right factor equality are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1b — the proof-free component-generator term.**  `X (componentGen δ)` when `δ` is
connected-divergent, `1` otherwise.  Proof-free in the CD witness (the generator is proof-irrelevant),
so it can be summed over a bare `Finset` of components. -/
noncomputable def resolvedComponentGenTerm (δ : ResolvedFeynmanSubgraph G) : ResolvedHopfH :=
  open Classical in
  if h : δ.forget.IsConnectedDivergent then MvPolynomial.X (resolvedComponentGen δ h) else 1

/-- **R-6c-heart-5c-1b — the forest left term as a plain product over components.**  Drops the
`attach` and the membership-derived CD proof (proof-irrelevant) in favour of `resolvedComponentGenTerm`
over `A.elements`. -/
theorem resolvedForestLeftTerm_eq_prod (A : ResolvedAdmissibleSubgraph G) :
    resolvedForestLeftTerm A = ∏ δ ∈ A.elements, resolvedComponentGenTerm δ := by
  unfold resolvedForestLeftTerm
  rw [← Finset.prod_attach A.elements resolvedComponentGenTerm]
  apply Finset.prod_congr rfl
  intro γ _
  simp only [resolvedComponentGenTerm]
  rw [dif_pos (A.isConnectedDivergent γ.1 γ.2)]

/-- **R-6c-heart-5c-1b — the forest left term splits over a disjoint union.**  When the two forests'
component sets are Finset-disjoint, the forest left term of their union is the product of the two — the
engine for `leftFactorProduct = leftTerm(leftOf) * leftTerm(promotedOf)`. -/
theorem resolvedForestLeftTerm_union (A B : ResolvedAdmissibleSubgraph G)
    (hCross : ∀ γ ∈ A.elements, ∀ δ ∈ B.elements, γ ≠ δ → γ.Disjoint δ)
    (hdisj : Disjoint A.elements B.elements) :
    resolvedForestLeftTerm (A.union B hCross)
      = resolvedForestLeftTerm A * resolvedForestLeftTerm B := by
  letI : DecidableEq (ResolvedFeynmanSubgraph G) := Classical.decEq _
  rw [resolvedForestLeftTerm_eq_prod (A.union B hCross), resolvedForestLeftTerm_eq_prod A,
    resolvedForestLeftTerm_eq_prod B, ResolvedAdmissibleSubgraph.union_elements]
  exact Finset.prod_union hdisj

end GaugeGeometry.QFT.Combinatorial
