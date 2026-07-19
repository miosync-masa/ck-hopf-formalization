import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPerm

/-!
# R-6c-body-409 — the correcting permutation's on-stars law (PROVED)

Four-hundred-and-ninth genuine-body step — the second `correctingPerm` action law, completing body-408: `τ` sends each
old star `R.starOf G A γ` to the corresponding new star `R.starOf (G.mapPerm σ) (A.mapPerm σ) (γ.mapPerm σ)`.

The key, per the safe split, is to use ONLY the subtype witnesses that the equivalences themselves issue — never a hand-built
`⟨σ oldStar, _⟩` witness that would carry its membership on a different `DecidableEq` instance.  The chain law
`starRelabelEquiv_symm_canonical` is proved by `Equiv.injective` + `apply_symm_apply`: the forward image of the relabeled
star index collapses the two round-trips (`apply_symm_apply` on the relabeled-star index, `symm_apply_apply` on the
component relabel), leaving both sides definitionally the `σ`-image projection — no `Classical.choose` interior is ever
inspected.  `correctingPerm_on_stars` then reads off `τ (oldStar) = (starRelabelEquiv.symm mappedOldV).1 = newStarV.1`
from `finsetSubtypeExtensionPerm_on_t` applied to the equiv-issued `mappedOldV.2`.

* `starRelabelEquiv_symm_canonical` — the canonical inverse image `mappedOldStar ↦ newStar` (equiv-issued witnesses only);
* `correctingPerm_on_stars` — `τ (oldStar) = newStar (γ.mapPerm σ)`.

Per the HALT: the `symm`-chain is NOT unfolded value-first; no hand-built subtype witness flows through the equivalences;
the `Finset.mem_image.mp` choose is NOT computed; graph transport / `classData` are the next front; no new datum.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {R : ResolvedCoproductProperForestRawData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-409 — the canonical inverse star-relabel image.**  `starRelabelEquiv.symm` sends the `σ`-image of the old
star of `γ` (as issued by `finsetImageSubtypeEquiv ∘ (starVertexEquivIndex …).symm`) to the new star of `γ.mapPerm σ`
(as issued by `(starVertexEquivIndex …).symm ∘ componentMapPermEquiv`).  Proved by injectivity — the forward chain
collapses both round-trips without inspecting the `Classical.choose` interior. -/
theorem starRelabelEquiv_symm_canonical (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ A.elements) :
    (starRelabelEquiv Fstar σ A).symm
        (finsetImageSubtypeEquiv σ σ.injective (A.starVertices (R.starOf G A))
          ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar A)).symm ⟨γ, hγ⟩))
      = (starVertexEquivIndex (starIndexRecoverOfFacts Fstar (A.mapPerm σ))).symm
          (componentMapPermEquiv σ A ⟨γ, hγ⟩) := by
  apply (starRelabelEquiv Fstar σ A).injective
  rw [Equiv.apply_symm_apply]
  -- reshape the RHS to `starRelabelEquiv`'s unfolded body, then collapse the two round-trips
  show _ = ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar (A.mapPerm σ))).trans
      ((componentMapPermEquiv σ A).symm.trans
        ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar A)).symm.trans
          (finsetImageSubtypeEquiv σ σ.injective (A.starVertices (R.starOf G A))))))
      ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar (A.mapPerm σ))).symm
          (componentMapPermEquiv σ A ⟨γ, hγ⟩))
  rw [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.trans_apply]
  rfl

/-- **R-6c-body-409 — `τ` sends each old star to the corresponding new star.**  Read off from the canonical inverse image
via `finsetSubtypeExtensionPerm_on_t` applied to the equiv-issued membership witness `mappedOldV.2`. -/
theorem correctingPerm_on_stars (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ A.elements) :
    correctingPerm Fstar σ A (R.starOf G A γ)
      = R.starOf (G.mapPerm σ) (A.mapPerm σ) (γ.mapPerm σ) := by
  calc correctingPerm Fstar σ A (R.starOf G A γ)
      = ((starRelabelEquiv Fstar σ A).symm
          (finsetImageSubtypeEquiv σ σ.injective (A.starVertices (R.starOf G A))
            ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar A)).symm ⟨γ, hγ⟩))).1 := by
        rw [correctingPerm, Equiv.Perm.mul_apply]
        exact finsetSubtypeExtensionPerm_on_t _ _ _
          (finsetImageSubtypeEquiv σ σ.injective (A.starVertices (R.starOf G A))
            ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar A)).symm ⟨γ, hγ⟩)).2
    _ = R.starOf (G.mapPerm σ) (A.mapPerm σ) (γ.mapPerm σ) :=
        congrArg Subtype.val (starRelabelEquiv_symm_canonical Fstar σ A hγ)

end GaugeGeometry.QFT.Combinatorial
