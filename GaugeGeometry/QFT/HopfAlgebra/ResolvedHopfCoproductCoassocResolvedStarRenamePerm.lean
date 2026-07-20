import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCrossAmbientCorrectingPerm
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFinsetPermBody

/-!
# R-6c-body-449 — the generic resolved star-renaming permutation (ambient-local fixing) (PROVED)

Four-hundred-and-forty-ninth genuine-body step — the resolved analogue of body-423's flat `flatStarRenamePerm`, built as
the reusable engine for the cross-ambient correcting permutations (inner side next, promoted side after).  Given a
resolved admissible forest `A` in an ambient `H` and TWO star assignments `s₁`, `s₂` that are each fresh (outside
`H.vertices`) and injective on `A.elements`, the permutation `ρ` relabels the `s₁`-stars to the `s₂`-stars and fixes ALL
of `H.vertices` — the LOCAL ambient, exactly the body-447 fixing domain.

* `resolvedStarVertexEquivIndex` — the star-vertex ↔ component equiv (resolved mirror of body-423);
* `resolvedStarRenamePerm` — `ρ` via `finsetSubtypeExtensionPerm`;
* `resolvedStarRenamePerm_on_ambient` — `ρ` fixes `H.vertices` (both star sets avoid it by freshness);
* `resolvedStarRenamePerm_on_stars` — `ρ (s₁ γ) = s₂ γ`.

For the inner cross-ambient socket the instantiation is `H := (Core.parent z δ).tRFG`, `A := Core.innerRaw z δ`,
`s₁ := hardcodedStar` (fresh w.r.t. the parent by `starOf_fresh`), `s₂ := touchedInnerStar` (fresh w.r.t. `G ⊇ parent`,
injective by `starOf_injective` + `innerSource_spec`).  That instantiation (and the promoted one) reuse THIS engine — its
fixing domain is exactly `H.vertices = (Core.parent z δ).vertices`, a strict subset of `G.vertices`, never all of `G`.

Per the HALT/guards: `ρ` fixes only the ambient `H`'s vertices, never a global `G` survivor; `innerStar_agrees_raw` /
strict `StarProm` are not used; no graph equality is proved here (that is the next body); no `Concrete` wiring; body-445
stays a valid conditional.  NOT the unconditional theorem.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false

variable {H : ResolvedFeynmanGraph}

/-- **R-6c-body-449 — the star-vertex ↔ component equiv** (resolved mirror of body-423's `flatStarVertexEquivIndex`). -/
noncomputable def resolvedStarVertexEquivIndex (A : ResolvedAdmissibleSubgraph H)
    (s : ResolvedFeynmanSubgraph H → VertexId)
    (hinj : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s γ₁ = s γ₂ → γ₁ = γ₂) :
    {v : VertexId // v ∈ A.starVertices s} ≃ {γ : ResolvedFeynmanSubgraph H // γ ∈ A.elements} := by
  refine ⟨fun v => ⟨Classical.choose (A.mem_starVertices.mp v.2),
      (Classical.choose_spec (A.mem_starVertices.mp v.2)).1⟩,
    fun γ => ⟨s γ.1, A.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩⟩, ?_, ?_⟩
  · intro v
    exact Subtype.ext (Classical.choose_spec (A.mem_starVertices.mp v.2)).2
  · intro γ
    refine Subtype.ext ?_
    exact hinj _ (Classical.choose_spec (A.mem_starVertices.mp
        (A.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩))).1 γ.1 γ.2
      (Classical.choose_spec (A.mem_starVertices.mp
        (A.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩))).2

/-- **R-6c-body-449 — the resolved star-renaming permutation** `ρ` relating two fresh/injective star assignments. -/
noncomputable def resolvedStarRenamePerm (A : ResolvedAdmissibleSubgraph H)
    (s₁ s₂ : ResolvedFeynmanSubgraph H → VertexId)
    (hinj₁ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₁ γ₁ = s₁ γ₂ → γ₁ = γ₂)
    (hinj₂ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₂ γ₁ = s₂ γ₂ → γ₁ = γ₂) : Equiv.Perm VertexId :=
  finsetSubtypeExtensionPerm (A.starVertices s₂) (A.starVertices s₁)
    ((resolvedStarVertexEquivIndex A s₂ hinj₂).trans (resolvedStarVertexEquivIndex A s₁ hinj₁).symm)

/-- **R-6c-body-449 — `ρ` fixes the AMBIENT vertices** — the local fixing domain, both star sets avoid `H.vertices`. -/
theorem resolvedStarRenamePerm_on_ambient (A : ResolvedAdmissibleSubgraph H)
    (s₁ s₂ : ResolvedFeynmanSubgraph H → VertexId)
    (hinj₁ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₁ γ₁ = s₁ γ₂ → γ₁ = γ₂)
    (hinj₂ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₂ γ₁ = s₂ γ₂ → γ₁ = γ₂)
    (hfresh₁ : ∀ γ ∈ A.elements, s₁ γ ∉ H.vertices)
    (hfresh₂ : ∀ γ ∈ A.elements, s₂ γ ∉ H.vertices)
    {v : VertexId} (hvH : v ∈ H.vertices) :
    resolvedStarRenamePerm A s₁ s₂ hinj₁ hinj₂ v = v :=
  finsetSubtypeExtensionPerm_apply_of_not_mem _ _ _
    (fun hs => by obtain ⟨γ, hγ, heq⟩ := A.mem_starVertices.mp hs; exact (heq ▸ hfresh₂ γ hγ) hvH)
    (fun hs => by obtain ⟨γ, hγ, heq⟩ := A.mem_starVertices.mp hs; exact (heq ▸ hfresh₁ γ hγ) hvH)

/-- **R-6c-body-449 — `ρ` sends each `s₁`-star to the corresponding `s₂`-star.** -/
theorem resolvedStarRenamePerm_on_stars (A : ResolvedAdmissibleSubgraph H)
    (s₁ s₂ : ResolvedFeynmanSubgraph H → VertexId)
    (hinj₁ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₁ γ₁ = s₁ γ₂ → γ₁ = γ₂)
    (hinj₂ : ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements, s₂ γ₁ = s₂ γ₂ → γ₁ = γ₂)
    {γ : ResolvedFeynmanSubgraph H} (hγ : γ ∈ A.elements) :
    resolvedStarRenamePerm A s₁ s₂ hinj₁ hinj₂ (s₁ γ) = s₂ γ := by
  have hmem : s₁ γ ∈ A.starVertices s₁ := A.mem_starVertices.mpr ⟨γ, hγ, rfl⟩
  have hcanon : (⟨s₁ γ, hmem⟩ : {v // v ∈ A.starVertices s₁})
      = (resolvedStarVertexEquivIndex A s₁ hinj₁).symm ⟨γ, hγ⟩ := Subtype.ext rfl
  rw [resolvedStarRenamePerm, finsetSubtypeExtensionPerm_on_t _ _ _ hmem, hcanon]
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end GaugeGeometry.QFT.Combinatorial
