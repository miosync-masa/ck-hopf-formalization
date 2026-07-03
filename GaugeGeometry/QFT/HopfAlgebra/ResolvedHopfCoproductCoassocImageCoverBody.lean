import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberAgreementBody

/-!
# R-6c-body-65 — image_cover scout: the boundary IS a split term (RIGHT closes per-`A`)

Sixty-fifth genuine-body step, the RIGHT-side counterpart to body-64's LEFT decision.  Body-64 found the LEFT
(branch) boundary `leftTerm A ⊗ (rightTerm A ⊗ 1)` is NOT any split-choice term, breaking the per-`A` cover.
Here the RIGHT (image) boundary is shown to BE a split-choice term — so the image per-`A` cover closes, and
`image_cover` reduces to the pure quotient de-contraction.

## The boundary lemma (PROVED)

```text
resolvedSplitChoiceTerm ⟨A, fun _ _ => Sum.inl false⟩ = 1 ⊗ (leftTerm A ⊗ rightTerm A)
```

The all-right-primitive split choice `p₀ = (fun _ _ => Sum.inl false)` sends every component to its right
primitive `1 ⊗ X gen γ`; the product is `∏ (1 ⊗ X gen γ) = 1 ⊗ ∏ X gen γ = 1 ⊗ leftTerm A` (via
`Algebra.TensorProduct.includeRight`'s `map_prod`, then `Finset.prod_attach` reconciling the double attach),
and `assoc((1 ⊗ leftTerm A) ⊗ rightTerm A) = 1 ⊗ (leftTerm A ⊗ rightTerm A)` (`assoc_tmul`).  So the image
boundary lives INSIDE the split-choice sum — exactly the asymmetry body-64 predicted (`1` in the LEFT slot is a
right-primitive choice; the branch's `1` sits in the RIGHT slot, which no choice produces).

## The reduction

Body-62's `image_cover` LHS is `1 ⊗ (leftTerm A ⊗ rightTerm A) + leftTerm A ⊗ (primitive (quot gen) + (quot
graph).sum)`.  Rewriting the boundary by the lemma turns it into

```text
resolvedSplitChoiceTerm ⟨A, p₀⟩ + leftTerm A ⊗ (primitive (quot gen A) + (quot graph A).sum)
  = (∑ forest fiber splitTerm) + (∑ mixed fiber splitTerm),
```

where now BOTH the boundary and the fiber sums are in split-choice vocabulary; the only non-split-choice piece
left is `leftTerm A ⊗ (primitive (quot gen A) + (quot graph A).sum)` — the genuine quotient de-contraction (the
image quotient's own forest sum reassembling into the `selectedOuter = A` fibers).  This is `image_cover`'s
irreducible content, fielded as `ResolvedImageQuotientCoverSupply.image_cover_quotient`.

## Result — the RIGHT/LEFT asymmetry, formalized

* LEFT (`branch_cover`, body-64): boundary is NOT a split term → per-`A` cover carries an irreducible boundary;
* RIGHT (`image_cover`, here): boundary IS the all-right-primitive split term → per-`A` cover closes, leaving
  only the quotient de-contraction.

So the image OUTPUT leaf is now the single quotient de-contraction field `image_cover_quotient`, with the
boundary discharged by the proved lemma.  The asymmetry is worth keeping in the final proof shape.

Per the HALT, the quotient de-contraction cover is NOT proved (it is `image_cover_quotient`); the branch side is
untouched; no return to retarget / `right_eq`.

Landed:

* `resolved_allRightPrimitive_splitTerm` — the image boundary as the all-right-primitive split term (PROVED);
* `ResolvedImageQuotientCoverSupply F` — `image_cover` with the boundary absorbed (only the quotient sum left);
* `ResolvedImageQuotientCoverSupply.toImageFiberCoverSupply` — recovers body-62's `image_cover`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-65 — the image boundary is the all-right-primitive split term.**  The split choice sending every
component to its right primitive (`Sum.inl false`) has split-choice term `1 ⊗ (leftTerm A ⊗ rightTerm A)` — the
image side's boundary.  (The branch boundary `(leftTerm A ⊗ rightTerm A) ⊗ 1` has no such representation; body-64.) -/
theorem resolved_allRightPrimitive_splitTerm
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  unfold ResolvedCoproductProperForestData.resolvedSplitChoiceTerm
  simp only [ResolvedCoproductProperForestData.localChoiceTerm, Sum.elim_inl, cond_false]
  have hprod : (∏ γ ∈ (A.1.elements.attach).attach,
      (1 : ResolvedHopfH) ⊗ₜ[ℚ] MvPolynomial.X
        ((γ.1.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD A.1 γ.1)))
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).leftTerm A := by
    simp only [← Algebra.TensorProduct.includeRight_apply]
    rw [← map_prod]
    congr 1
    rw [Finset.prod_attach (A.1.elements.attach)
      (fun γ' => MvPolynomial.X ((γ'.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD A.1 γ')))]
    rfl
  rw [hprod, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]

/-- **R-6c-body-65 — the image quotient de-contraction cover.**  `image_cover` with its boundary absorbed into
the split-choice vocabulary (via the lemma): the all-right-primitive split term plus the quotient de-contraction
equals the `selectedOuter = A` fiber sum.  The genuine RIGHT inner content — the quotient graph's own forest sum
reassembling into the image fibers. -/
structure ResolvedImageQuotientCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The all-right-primitive term + the quotient de-contraction = the `selectedOuter = A` fiber sum. -/
  image_cover_quotient : ∀ A ∈ (D.supply G).forestCarrier,
    (D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
        + (D.supply G).leftTerm A ⊗ₜ[ℚ]
            (resolvedCoproductGenPrimitive
                ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
              + (D.supply (A.1.contractWithStars (D.starOf G A.1))).sum))
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-65 — body-62's image cover from the quotient cover.**  Rewrite the boundary back to
`1 ⊗ (leftTerm A ⊗ rightTerm A)` via the proved lemma. -/
def ResolvedImageQuotientCoverSupply.toImageFiberCoverSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageQuotientCoverSupply F) :
    ResolvedImageFiberCoverSupply F where
  image_cover := fun A hA => by
    rw [← resolved_allRightPrimitive_splitTerm A]
    exact S.image_cover_quotient A hA

end GaugeGeometry.QFT.Combinatorial
