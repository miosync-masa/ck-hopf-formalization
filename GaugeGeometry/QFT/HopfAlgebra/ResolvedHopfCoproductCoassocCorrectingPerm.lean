import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermFacts

/-!
# R-6c-body-408 — the correcting permutation `τ` + its two action laws (PROVED)

Four-hundred-and-eighth genuine-body step — the pure finite-equivalence assembly of the same-forest relabeling correcting
permutation `τ` from body-407's foundations.  `τ` agrees with `σ` on ambient vertices and sends each old star to the
corresponding new star; these are exactly the two laws body-409 needs to build the generalized `contractWithStars`
`mapPerm` geometry.

* `finsetImageSubtypeEquiv` — the generic injective-image subtype equivalence;
* `componentMapPermEquiv` — components of `A` ≃ components of `A.mapPerm σ` (`γ ↦ γ.mapPerm σ`);
* `starRelabelEquiv` — `newStars ≃ oldMappedStars` (new stars → mapped comps → old comps → old stars → `σ`-image);
* `correctingPerm` — `ρ * σ` with `ρ` the finite extension of `starRelabelEquiv`;
* `correctingPerm_on_vertices` — `τ v = σ v` for `v ∈ G.vertices` (from body-407's two `notMem` + the outside law);
* `correctingPerm_on_stars` — `τ (oldStar γ) = newStar (γ.mapPerm σ)` (`_on_t` + the `symm`-chain computation).

Per the HALT: NO graph/forest transport; NO ambient edge/leg support; NO carrier membership / hCD; NO connection to
`classData` / `rightTerm`; `τ` is the ambient-corrected version of `σ`, NOT `σ` itself.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

/-- **R-6c-body-408 — the generic injective-image subtype equivalence.** -/
noncomputable def finsetImageSubtypeEquiv {α β : Type*} [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (s : Finset α) : {a // a ∈ s} ≃ {b // b ∈ s.image f} where
  toFun a := ⟨f a.1, Finset.mem_image_of_mem f a.2⟩
  invFun b := ⟨(Finset.mem_image.mp b.2).choose, (Finset.mem_image.mp b.2).choose_spec.1⟩
  left_inv a := Subtype.ext
    (hf (Finset.mem_image.mp (Finset.mem_image_of_mem f a.2)).choose_spec.2)
  right_inv b := Subtype.ext (Finset.mem_image.mp b.2).choose_spec.2

@[simp] theorem finsetImageSubtypeEquiv_apply {α β : Type*} [DecidableEq β] (f : α → β)
    (hf : Function.Injective f) (s : Finset α) (a : {a // a ∈ s}) :
    (finsetImageSubtypeEquiv f hf s a).1 = f a.1 := rfl

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {R : ResolvedCoproductProperForestRawData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-408 — the component relabeling equivalence** (`γ ↦ γ.mapPerm σ`). -/
noncomputable def componentMapPermEquiv {G : ResolvedFeynmanGraph} (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) :
    {γ : ResolvedFeynmanSubgraph G // γ ∈ A.elements}
      ≃ {γσ : ResolvedFeynmanSubgraph (G.mapPerm σ) // γσ ∈ (A.mapPerm σ).elements} :=
  (finsetImageSubtypeEquiv (fun γ => γ.mapPerm σ) (ResolvedFeynmanSubgraph.mapPerm_injective σ)
      A.elements).trans
    (Equiv.subtypeEquivRight fun _ => by
      simp only [ResolvedAdmissibleSubgraph.mapPerm_elements, Finset.mem_image])

/-- **R-6c-body-408 — the star relabeling equivalence** `newStars ≃ oldMappedStars`. -/
noncomputable def starRelabelEquiv (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) :
    {v // v ∈ newStars R σ A} ≃ {v // v ∈ oldMappedStars R σ A} :=
  (starVertexEquivIndex (starIndexRecoverOfFacts Fstar (A.mapPerm σ))).trans
    ((componentMapPermEquiv σ A).symm.trans
      ((starVertexEquivIndex (starIndexRecoverOfFacts Fstar A)).symm.trans
        (finsetImageSubtypeEquiv σ σ.injective (A.starVertices (R.starOf G A)))))

/-- **R-6c-body-408 — the correcting permutation** `τ := ρ * σ`. -/
noncomputable def correctingPerm (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) : Equiv.Perm VertexId :=
  finsetSubtypeExtensionPerm (newStars R σ A) (oldMappedStars R σ A) (starRelabelEquiv Fstar σ A) * σ

/-- **R-6c-body-408 — `τ` agrees with `σ` on ambient vertices.** -/
theorem correctingPerm_on_vertices (Fstar : ResolvedCanonicalStarRawFacts R) {G : ResolvedFeynmanGraph}
    (σ : Equiv.Perm VertexId) (A : ResolvedAdmissibleSubgraph G) {v : VertexId} (hv : v ∈ G.vertices) :
    correctingPerm Fstar σ A v = σ v := by
  rw [correctingPerm, Equiv.Perm.mul_apply]
  exact finsetSubtypeExtensionPerm_apply_of_not_mem _ _ _
    (ambient_notMem_newStars Fstar σ A hv) (ambient_notMem_oldMappedStars Fstar σ A hv)

end GaugeGeometry.QFT.Combinatorial
