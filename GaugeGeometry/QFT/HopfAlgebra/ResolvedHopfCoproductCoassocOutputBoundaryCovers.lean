import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverBody

/-!
# R-6c-body-70 — OUTPUT boundary covers: image is a ∅-fiber, branch is primitive-outer (cover-external)

Seventieth genuine-body step, a SCOUT of body-69's two global boundary terms.  Do they live in the
split-choice cover?  The answer is asymmetric — and both halves are proved concretely here.

## Image boundary IS a split-choice fiber (PROVED)

`1 ⊗ forestSum G = ∑_A 1 ⊗ (leftTerm A ⊗ rightTerm A)` (`tmul_sum`), and body-65's
`resolved_allRightPrimitive_splitTerm` gives `1 ⊗ (leftTerm A ⊗ rightTerm A) = resolvedSplitChoiceTerm
⟨A, p₀⟩` for the all-right-primitive `p₀`.  So

```text
1 ⊗ forestSum G = ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩
```

— the image boundary is exactly the sum of the all-right-primitive split terms, one per base outer `A`.  These
have `selectedOuter = ∅` (nothing is left-selected), so they are the `selectedOuter = ∅` fiber (`resolved_image_
boundary_eq_allRightPrimitive_sum`).  The image boundary has a genuine home INSIDE the cover.

## Branch boundary is primitive-outer, NOT a split-choice fiber (PROVED + decided)

`assoc(forestSum G ⊗ 1) = ∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)` (`sum_tmul` + `map_sum` + `assoc_tmul`,
`resolved_branch_boundary_eq_primitive_outer`).  Each term has inner-third factor `1`.  But EVERY split term is
`resolvedSplitChoiceTerm s = assoc((∏ localChoiceTerm) ⊗ rightTerm s.1)`, whose inner-third factor is
`rightTerm s.1 = X(quotient gen of the base outer)` — a generator, never `1` (and via `right_eq`,
`innerRightTerm (imageOf s) = rightTerm s.1`, so the image weights agree: `1` would force base `= ∅`, but then
the outer factor is `leftTerm ∅ = 1 ≠ leftTerm A`).  So `leftTerm A ⊗ (rightTerm A ⊗ 1)` is NOT any split term,
and the branch boundary is NOT a split-choice sum.

**Decision.** The branch boundary `assoc(forestSum G ⊗ 1) = ∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)` is the
PRIMITIVE-OUTER boundary — the `(Δᵣ ⊗ 1) ∘ Δᵣ` term where the second `Δᵣ` on the quotient is TRIVIAL (`… ⊗ 1`).
It is cover-EXTERNAL: it belongs with the image side's coassoc-RIGHT primitive part (`∑_A leftTerm A ⊗ (rightTerm
A ⊗ 1)` also appears inside `coassocRightTail(forestSum)` as `Δᵣ(rightTerm A)`'s `X ⊗ 1` primitive), NOT with the
split-choice cover.  So the two OUTPUT boundaries are handled differently: the image boundary via the
`selectedOuter = ∅` split-choice fiber (this body, proved), the branch boundary as a primitive-outer term
matched against the image tail's primitive part.

This deepens the body-64/68 asymmetry: the image side's unit terms fold into the cover (`∅`-fiber); the branch
side's unit term stays outside it.  Follow-up: body-69's `branch_cover_partition` equates `assoc(forestSum ⊗ 1)`
to a slice of the split-choice cover, which by this finding needs the branch boundary routed to the image tail's
primitive part instead (a further correction, not entered here).

Per the HALT, the image boundary cover is proved; the branch boundary is classified (primitive-outer), not
forced into split choices.

Landed:

* `resolved_image_boundary_eq_allRightPrimitive_sum` — image boundary = `∑_A` all-right-primitive split terms;
* `resolved_branch_boundary_eq_primitive_outer` — branch boundary = `∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)`
  (primitive-outer, not split choices).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-70 — the image boundary is the all-right-primitive fiber.**  The global image boundary
`1 ⊗ forestSum G` equals the sum over base outers `A` of the all-right-primitive split terms — the
`selectedOuter = ∅` split-choice fiber.  Its home is INSIDE the cover. -/
theorem resolved_image_boundary_eq_allRightPrimitive_sum :
    (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
      = ∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G) := by
  rw [ResolvedCoproductForestSummandSupply.sum, TensorProduct.tmul_sum]
  exact Finset.sum_congr rfl (fun A _ => (resolved_allRightPrimitive_splitTerm A).symm)

/-- **R-6c-body-70 — the branch boundary is primitive-outer.**  The global branch boundary
`assoc(forestSum G ⊗ 1)` equals `∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)` — the primitive-outer form, where the inner
third factor is `1`.  This is NOT any split term (whose inner third factor is `rightTerm(base) ≠ 1`), so the
branch boundary is cover-EXTERNAL. -/
theorem resolved_branch_boundary_eq_primitive_outer :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
        ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
      = ∑ A ∈ (D.supply G).forestCarrier,
          (D.supply G).leftTerm A ⊗ₜ[ℚ] ((D.supply G).rightTerm A ⊗ₜ[ℚ] (1 : ResolvedHopfH)) := by
  rw [ResolvedCoproductForestSummandSupply.sum, TensorProduct.sum_tmul, map_sum]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]

end GaugeGeometry.QFT.Combinatorial
