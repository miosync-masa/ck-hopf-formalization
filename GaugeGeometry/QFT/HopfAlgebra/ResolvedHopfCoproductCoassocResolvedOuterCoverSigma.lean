import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedPartitionLayer

/-!
# R-6c-body-54 — the resolved outer↔cover σ-cover skeleton

Fifty-fourth genuine-body step, isolating the LAST reindex obstruction: the outer-forest ↔ splitPhi-cover
connection, as a resolved-native σ-cover skeleton (the `ResolvedHopfH3` analogue of R-4-full's
`ResolvedActualSigmaCover`).

## The partition bridge (from body-53 + `term_eq`)

`grandFull_partition_reindex` (body-53) at `w = imageWeight`, with `term_eq : resolvedSplitChoiceTerm s =
imageWeight (imageOf s)`, gives

```text
∑ z ∈ imageCarrier, imageWeight z = ∑ q ∈ forestCarrier, splitTerm q.1 + ∑ q ∈ mixedCarrier, splitTerm q.1
```

(`grandFull_imageWeight_eq_splitTerm_sum`).  So the splitPhi cover's IMAGE sum and its (FOREST ⊕ MIXED) TERM
sum are THE SAME — body-38's image side (`∑ imageCarrier imageWeight`) and branch side (`∑ forest+mixed
splitTerm`) meet at the cover.

## The remaining obstruction, in split-term coordinates

Both of body-38's reindexes then reduce to connecting the OUTER-forest sum to this single split-term cover sum:

* `outer_image_cover` — the outer image summand sum = the split-term cover sum;
* `outer_branch_cover` — the split-term cover sum = the outer branch summand sum.

These two are the resolved σ-cover data (`ResolvedOuterCoverSigmaSupply`) — the genuine outer × inner H5.8
double sum, resolved-natively over `ResolvedHopfH3`.  Given them, body-38's `image_cover_reindex` /
`branch_cover_reindex` follow (image via the partition bridge, branch directly).

Per the HALT, the outer × inner double-sum bijection is NOT proved; the two σ-cover reindexes are the named
fields; no flat `HopfH`.

Landed:

* `grandFull_imageWeight_eq_splitTerm_sum` — the partition bridge (image cover sum = forest+mixed term sum);
* `ResolvedOuterCoverSigmaSupply F` — the resolved σ-cover skeleton (`outer_image_cover` + `outer_branch_cover`);
* `.image_cover_reindex` / `.branch_cover_reindex` — body-38's reindexes, from the skeleton + the bridge.

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

set_option linter.unusedSectionVars false in
/-- **R-6c-body-54 — the partition bridge.**  The splitPhi cover's image-weight sum equals its (forest ⊕
mixed) split-term sum (body-53's partition + `term_eq`). -/
theorem grandFull_imageWeight_eq_splitTerm_sum (F : ResolvedCoassocGrandFullSupply D G) :
    ∑ z ∈ F.imageCarrier, F.toFiniteData.imageWeight z =
      (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1) := by
  rw [grandFull_partition_reindex F F.toFiniteData.imageWeight]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl (fun q _ => ?_))
    (Finset.sum_congr rfl (fun q _ => ?_))
  · exact (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.term_eq q.1).symm
  · exact (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.term_eq q.1).symm

/-- **R-6c-body-54 — the resolved outer↔cover σ-cover skeleton.**  The outer-forest image / branch summand sums
each connected to the split-term cover sum — the resolved-native H5.8 outer × inner double sum. -/
structure ResolvedOuterCoverSigmaSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The outer image summand sum equals the split-term cover sum. -/
  outer_image_cover :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
  /-- The split-term cover sum equals the outer branch summand sum. -/
  outer_branch_cover :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))

/-- **R-6c-body-54 — body-38's image reindex from the skeleton** (via the partition bridge). -/
theorem ResolvedOuterCoverSigmaSupply.image_cover_reindex {F : ResolvedCoassocGrandFullSupply D G}
    (S : ResolvedOuterCoverSigmaSupply F) :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = ∑ z ∈ F.toFiniteData.imageCarrier, F.toFiniteData.imageWeight z :=
  S.outer_image_cover.trans (grandFull_imageWeight_eq_splitTerm_sum F).symm

/-- **R-6c-body-54 — body-38's branch reindex from the skeleton** (directly). -/
theorem ResolvedOuterCoverSigmaSupply.branch_cover_reindex {F : ResolvedCoassocGrandFullSupply D G}
    (S : ResolvedOuterCoverSigmaSupply F) :
    (∑ q ∈ F.toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ F.toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply G).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)) :=
  S.outer_branch_cover

end GaugeGeometry.QFT.Combinatorial
