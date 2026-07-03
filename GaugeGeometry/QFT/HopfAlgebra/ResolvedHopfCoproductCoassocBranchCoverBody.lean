import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchFiberAgreementBody

/-!
# R-6c-body-64 — branch_cover scout: the boundary obstruction and the base/image discriminator mismatch

Sixty-fourth genuine-body step, a DECISION scout of `branch_cover` (body-61) — expected to be "the easy pure
sum-vs-sum cover".  It is NOT: the LEFT reindex carries a boundary term that base-outer fibering cannot produce,
and F's carriers are discriminated by a *different* index than the branch fiber.  Recorded here with the one
clean provable refinement (a direct-form entry point).

## What `branch_cover` actually asks

Body-61's `branch_cover` (with the LEFT tail already expanded to the pi-choice sum by
`coassocLeftTail_eq_splitChoiceTermSum`) is, per outer forest `A`:

```text
assoc((leftTerm A ⊗ rightTerm A) ⊗ 1)  +  ∑ p ∈ piCarrier A, splitTerm ⟨A, p⟩
  = (∑ q ∈ F.forestCarrier with q.1.1 = A, splitTerm q.1)
      + (∑ q ∈ F.mixedCarrier with q.1.1 = A, splitTerm q.1).
```

## The boundary obstruction (the decisive finding)

`∑ p ∈ piCarrier A, splitTerm ⟨A, p⟩` is exactly `coassocLeftTail (leftTerm A ⊗ rightTerm A)` — the FULL
base-`A` split-choice sum.  The extra summand `assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) = leftTerm A ⊗
(rightTerm A ⊗ 1)` is a genuine boundary — and it is **not** any `splitTerm ⟨A, p⟩`: every split-choice term
has `rightTerm A` in its RIGHTMOST tensor slot (`splitTerm = assoc((∏ localChoiceTerm) ⊗ rightTerm A)`), whereas
the boundary has `1` there and `rightTerm A` in the MIDDLE.  So no base-`A` split choice — and no sum of them —
can produce the branch boundary.

## The satisfiability ASYMMETRY with the image side

The image boundary is different: `1 ⊗ (leftTerm A ⊗ rightTerm A)` IS the all-right-primitive split term — the
choice `p₀ = (fun _ => Sum.inl false)` gives `∏ localChoiceTerm = ∏ (1 ⊗ X gen γ) = 1 ⊗ leftTerm A`, hence
`splitTerm ⟨A, p₀⟩ = assoc((1 ⊗ leftTerm A) ⊗ rightTerm A) = 1 ⊗ (leftTerm A ⊗ rightTerm A)`.  So the RIGHT
(image) per-`A` fibration's boundary lives inside the split-choice sum and is satisfiable; the LEFT (branch)
per-`A` fibration's boundary does not.

Compounding this, F's `forestCarrier` / `mixedCarrier` are discriminated by the IMAGE (`imageOf s` touching the
outer stars — `resolvedIsForestByStar`), and `cover_on` connects them only to `imageCarrier` via `imageOf` —
NOT to the base-outer index `s.1` the branch fiber (body-59) groups by.  So the branch per-`A` sum reindexes an
IMAGE-indexed cover along a BASE-index fiber.

## DECISION

`branch_cover` is a genuine fielded identity, NOT a pure combinatorial partition: its boundary term cannot be a
base-outer split-choice sum, and it relindexes an image-discriminated cover by a base-outer fiber.  It does not
reduce to a `piCarrier ≃ base-fiber` bijection (that bijection would give `∑ base-A fibers = coassocLeftTail A`,
forcing the boundary to vanish, which it does not).  The honest content is: **the branch reindex is genuinely
per-`A` only if the boundary contribution is carried by the fiber** — i.e. `branch_cover` stays a fielded
supply, exactly as the image `image_cover` (body-62) does.  This corrects the earlier expectation that LEFT
would be strictly easier than RIGHT; the boundary makes them siblings.  (The satisfiable full-sum form remains
body-54's `outer_branch_cover`; the per-`A` split is what carries the boundary.)

## The one clean refinement

`branch_cover` is stated more naturally WITHOUT the pi-choice expansion — directly as "branch outer summand `A`
= its base-`A` fiber sum".  `ResolvedBranchCoverDirectSupply` fields that direct form; `toBranchFiberCoverSupply`
recovers body-61's pi-choice form by re-folding the tail (`coassocLeftTail_eq_splitChoiceTermSum`).  So the
fielded LEFT leaf can be the readable direct branch-summand identity rather than the pi-carrier one.

Per the HALT, the branch bijection is NOT proved (it remains `branch_cover`); the boundary is identified, not
discharged; the image side is only referenced for the asymmetry.

Landed:

* `ResolvedBranchCoverDirectSupply F` — the direct branch-summand form of the LEFT cover;
* `ResolvedBranchCoverDirectSupply.toBranchFiberCoverSupply` — recovers body-61's pi-choice `branch_cover`.

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

/-- **R-6c-body-64 — the direct-form LEFT cover.**  The branch outer summand `A` (`assoc(⊗1)` boundary +
`coassocLeftTail`) equals its base-`A` fiber sum — the natural statement of `branch_cover`, without the
pi-choice expansion.  Still a fielded identity (the boundary is not a base-`A` split-choice term). -/
structure ResolvedBranchCoverDirectSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The branch outer summand for `A` equals its base-outer-`A` fiber sum (forest ⊕ mixed). -/
  branch_cover_direct : ∀ A ∈ (D.supply G).forestCarrier,
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
          (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with resolvedBranchForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedBranchMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-64 — body-61's pi-choice cover from the direct form.**  Re-fold the LEFT tail to the pi-choice
sum via `coassocLeftTail_eq_splitChoiceTermSum`. -/
def ResolvedBranchCoverDirectSupply.toBranchFiberCoverSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedBranchCoverDirectSupply F) :
    ResolvedBranchFiberCoverSupply F where
  branch_cover := fun A hA => by
    rw [← D.coassocLeftTail_eq_splitChoiceTermSum A]
    exact S.branch_cover_direct A hA

end GaugeGeometry.QFT.Combinatorial
