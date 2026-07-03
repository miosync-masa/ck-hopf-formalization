import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocResolvedOuterCoverSigma

/-!
# R-6c-body-69 — OUTPUT full-sum boundary split: boundary global + tail fibration (corrected path)

Sixty-ninth genuine-body step, the CORRECTION mandated by body-68's boundary-slot finding.  The per-`A` OUTPUT
covers (bodies 56–67) misattribute the outer boundary (`1 ⊗ forestSum` / `forestSum ⊗ 1`), which under `term_eq`
belongs to the `selectedOuter = ∅` contributions, not the nonempty `A` fibers.  Here the satisfiable full-sum
form (body-54) is re-derived as `boundary global term + tail outer sum`, giving each unit term its own home.

## The boundary/tail algebraic split (PROVED)

Both outer full sums split cleanly — the boundary factors out of the per-`A` sum:

* IMAGE: `∑_A (1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail A) = 1 ⊗ forestSum G + ∑_A coassocRightTail A`
  (`Finset.sum_add_distrib` + `TensorProduct.tmul_sum`);
* BRANCH: `∑_A (assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail A) = assoc(forestSum G ⊗ 1) + ∑_A
  coassocLeftTail A` (`Finset.sum_add_distrib` + `TensorProduct.sum_tmul` + `map_sum`).

Here `forestSum G = (D.supply G).sum = ∑_A leftTerm A ⊗ rightTerm A`, and the boundary `1 ⊗ forestSum G` /
`assoc(forestSum G ⊗ 1)` is ONE global term — the `∅`-fiber home the per-`A` covers lacked.

## The corrected cover primitive

`ResolvedOutputFullSumCoverSupply` fields the cover at full-sum level as `boundary + tail`:

```text
∑ forest splitTerm + ∑ mixed splitTerm
  = 1 ⊗ forestSum G          (image boundary, ∅-fiber)  + ∑_A coassocRightTail A     (image tail)
∑ forest splitTerm + ∑ mixed splitTerm
  = assoc(forestSum G ⊗ 1)   (branch boundary, ∅-fiber) + ∑_A coassocLeftTail A       (branch tail)
```

Both are SATISFIABLE (the true coassoc content at full-sum level): the boundary sits in its own `∅`-fiber term,
the tails `∑_A coassocRightTail A` / `∑_A coassocLeftTail A` carry the per-`A` de-contraction WITHOUT the unit
terms — exactly what body-68's `term_eq`/`right_eq` tunnel handles.  Via the proved boundary/tail splits,
`toOuterCoverSigmaSupply` recovers body-54's `ResolvedOuterCoverSigmaSupply` (whence `image_cover_reindex` /
`branch_cover_reindex` → body-38 → `coassoc_gen`) — bypassing the per-`A` fibration engine (body-55) for the
boundary.

## Status of the old per-`A` covers

Bodies 56–67 (`image_fiber_agree` / `branch_cover` / `image_quotient_fiber` / `branch_cover_direct`) remain
typed and axiom-clean but are SEMANTICALLY TOO STRONG (per body-68: unsatisfiable for nonempty `A` due to
boundary mislocation).  This body supersedes them with the satisfiable full-sum decomposition; the tail covers
are the correct place to resume the per-`A` `term_eq`/`right_eq` de-contraction (now boundary-free).

Per the HALT, the boundary/tail SPLIT is proved (it is `rfl`-adjacent algebra); the cover partition itself is
fielded (the genuine cover, satisfiable); no per-`A` cover is repaired in place.

Landed:

* `outer_image_boundary_tail_split` / `outer_branch_boundary_tail_split` — the boundary/tail algebra (PROVED);
* `ResolvedOutputFullSumCoverSupply F` — the corrected full-sum cover (`boundary + tail`, both sides);
* `ResolvedOutputFullSumCoverSupply.toOuterCoverSigmaSupply` — to body-54's σ-cover skeleton.

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

/-- **R-6c-body-69 — the IMAGE boundary/tail split.**  The image outer full sum factors as the global boundary
`1 ⊗ forestSum G` plus the tail `∑_A coassocRightTail A`. -/
theorem outer_image_boundary_tail_split :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
          + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [Finset.sum_add_distrib]
  congr 1
  rw [ResolvedCoproductForestSummandSupply.sum, TensorProduct.tmul_sum]

/-- **R-6c-body-69 — the BRANCH boundary/tail split.**  The branch outer full sum factors as the global
boundary `assoc(forestSum G ⊗ 1)` plus the tail `∑_A coassocLeftTail A`. -/
theorem outer_branch_boundary_tail_split :
    (∑ A ∈ (D.supply G).forestCarrier,
        ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
          + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)))
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [Finset.sum_add_distrib]
  congr 1
  rw [ResolvedCoproductForestSummandSupply.sum, TensorProduct.sum_tmul, map_sum]

/-- **R-6c-body-69 — the corrected full-sum cover** (`boundary + tail`, both sides).  The satisfiable OUTPUT
cover: the splitPhi cover sum equals the global boundary term plus the per-`A` tail — the boundary given its own
`∅`-fiber home, the tails carrying the boundary-free per-`A` de-contraction. -/
structure ResolvedOutputFullSumCoverSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- Image cover = boundary `1 ⊗ forestSum G` + tail `∑_A coassocRightTail A`. -/
  image_cover_partition :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
  /-- Branch cover = boundary `assoc(forestSum G ⊗ 1)` + tail `∑_A coassocLeftTail A`. -/
  branch_cover_partition :
    (∑ q ∈ F.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-69 — body-54's σ-cover skeleton from the corrected full-sum cover.**  Re-fold the boundary/tail
split into the per-`A` outer summand form, bypassing the per-`A` fibration for the boundary. -/
def ResolvedOutputFullSumCoverSupply.toOuterCoverSigmaSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedOutputFullSumCoverSupply F) :
    ResolvedOuterCoverSigmaSupply F where
  outer_image_cover := by
    rw [outer_image_boundary_tail_split]; exact S.image_cover_partition.symm
  outer_branch_cover := by
    rw [outer_branch_boundary_tail_split]; exact S.branch_cover_partition

end GaugeGeometry.QFT.Combinatorial
