import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductSupply

/-!
# R-6c-body-404 — strict-star usage audit + the right-term alpha interface (PROVED feasibility)

Four-hundred-and-fourth genuine-body step — the minimal repair prototype after body-403's no-go.  Instead of changing
`D` wholesale, the replacement LAW is prototyped and its `sum`-proof feasibility is discharged, strict `star_mapPerm`
unused.

## Strict-`star_mapPerm` usage audit (source-confirmed)

`D.star_mapPerm` is CONSUMED in exactly ONE place in the live proof code: `ResolvedCoproductProperForestData.sum_mapPerm`
(`ResolvedHopfCoproductSupply.lean:173`), via `resolvedForestRightTerm_mapPerm`'s per-component star-equality hypothesis
`starOf' (γ.mapPerm σ) = σ (starOf γ)` — which is exactly the strict equivariance body-403 proved inconsistent with
freshness.  Every other occurrence is a docstring / audit anchor or body-403's own no-go.  So the algebra needs only the
`mapPerm`-invariance of the RIGHT TERM, not the strict star equality.

## The minimal alpha law + its `sum`-proof feasibility

* `ResolvedRightTermAlphaSupply D` — the single law `rightTerm_mapPerm`: the forest right term is `mapPerm`-invariant
  (the resolved CLASS of the contraction is relabel-invariant), stated with `D`'s own `starOf` on BOTH sides, so a
  correcting-permutation / alpha-equivalence provider can discharge it WITHOUT a strict fresh-name equivariance.
* `sum_mapPerm_of_rightTermAlpha` — body's `sum_mapPerm`, with its ONLY `star_mapPerm` use replaced by
  `Alpha.rightTerm_mapPerm`; strict `star_mapPerm` NEVER touched.

Per the HALT: the old `ResolvedCoproductProperForestData` is NOT changed; only the strict-`star_mapPerm`-free `sum`-proof
feasibility is proved; the correcting permutation itself is NOT built; the term-level law is NOT read as "the star
equality was proved".  The atomic migration (retire `star_mapPerm` → introduce `rightTerm_mapPerm` → swap `sum_mapPerm`
→ migrate `W` / supported-carrier / body-400 chain) is body-405.  No facade, no flat term, no `forgetHopf`, no rep/perm,
and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-404 — the right-term alpha law.**  The forest right term is `mapPerm`-invariant — the ONLY property the
`sum`-proof needs from the star assignment (weaker than the strict, inconsistent `star_mapPerm`). -/
structure ResolvedRightTermAlphaSupply (D : ResolvedCoproductProperForestData) where
  /-- The forest right term is `mapPerm`-invariant (`D`'s own `starOf` on both sides). -/
  rightTerm_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) (hA : A ∈ D.carrier G)
    (hAσ : A.mapPerm σ ∈ D.carrier (G.mapPerm σ)),
    resolvedForestRightTerm A (D.starOf G A) (D.hCD G A hA)
      = resolvedForestRightTerm (A.mapPerm σ) (D.starOf (G.mapPerm σ) (A.mapPerm σ))
          (D.hCD (G.mapPerm σ) (A.mapPerm σ) hAσ)

/-- **R-6c-body-405 — the alpha law is now a projection of the migrated core** (`D.rightTerm_mapPerm` is a field). -/
def ResolvedCoproductProperForestData.toRightTermAlphaSupply (D : ResolvedCoproductProperForestData) :
    ResolvedRightTermAlphaSupply D where
  rightTerm_mapPerm := D.rightTerm_mapPerm

/-- **R-6c-body-404 — `sum` is `mapPerm`-invariant from the alpha law ALONE** (strict `star_mapPerm` unused). -/
theorem sum_mapPerm_of_rightTermAlpha (Alpha : ResolvedRightTermAlphaSupply D)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (D.supply (G.mapPerm σ)).sum = (D.supply G).sum := by
  symm
  refine ResolvedCoproductForestSummandSupply.sum_eq_of_bij (D.supply G) (D.supply (G.mapPerm σ))
    (fun A _ => ⟨A.1.mapPerm σ, by rw [D.carrier_mapPerm]; exact Finset.mem_image_of_mem _ A.2⟩)
    (fun _ _ => Finset.mem_attach _ _) (fun A₁ _ A₂ _ h => ?_) (fun B _ => ?_)
    (fun A _ => ?_) (fun A _ => ?_)
  · exact Subtype.ext (ResolvedAdmissibleSubgraph.mapPerm_injective σ (Subtype.ext_iff.mp h))
  · obtain ⟨A, hA, hAeq⟩ := Finset.mem_image.mp
      (by simpa only [D.carrier_mapPerm] using B.2)
    exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, Subtype.ext hAeq⟩
  · exact resolvedForestLeftTerm_mapPerm A.1 σ
  · exact Alpha.rightTerm_mapPerm G σ A.1 A.2
      (by rw [D.carrier_mapPerm]; exact Finset.mem_image_of_mem _ A.2)

end GaugeGeometry.QFT.Combinatorial
