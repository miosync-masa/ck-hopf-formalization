import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractForget
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermFacts

/-!
# R-6c-body-423 — generic same-forest fresh star-renaming permutation (PROVED)

Four-hundred-and-twenty-third genuine-body step — the `σ = id` specialisation of the bodies 407–410 correcting
permutation, now on the FLAT side.  Body-422 collapsed the resolved↔flat boundary, so the `hCD` obstacle is purely:
two fresh/injective star assignments `s₁ s₂` on the SAME flat forest `B` give contractions of the same class.  This
body builds the correcting permutation `ρ` relating them and its two action laws — a standalone generic lemma, so the
`hCD` proof (body-424) is thin.

* `flatStarVertexEquivIndex` — the flat star-index recovery `{v // v ∈ B.starVertices s} ≃ {γ // γ ∈ B.elements}` for a
  fresh/injective `s` (the flat analog of the resolved `starVertexEquivIndex`; `finsetImageSubtypeEquiv` cannot be used —
  fresh stars are only `InjOn B.elements`, not globally injective);
* `flatStarRenamePerm` — `ρ := finsetSubtypeExtensionPerm (starVertices s₂) (starVertices s₁) e`, `e` the star bijection
  `s₂ γ ↦ s₁ γ` (both indices via `flatStarVertexEquivIndex`);
* `flatStarRenamePerm_on_ambient` — `ρ v = v` for `v ∈ G.vertices` (freshness: ambient vertices are outside both star
  sets, `finsetSubtypeExtensionPerm_apply_of_not_mem`);
* `flatStarRenamePerm_on_stars` — `ρ (s₁ γ) = s₂ γ` (`finsetSubtypeExtensionPerm_on_t` + the canonical-witness
  round-trip collapse, no `Classical.choose` interior inspected).

Per the HALT: NO graph/class equality, NO CD, NO `hCD` here — this is the permutation + its two point laws only.  Body-424
consumes them to get `B.contractWithStars s₂ = (B.contractWithStars s₁).mapPerm ρ` (via the FLAT `mapPerm_contractWithStars`
with the two laws as `hstar`), the class equality, the flat canonical CD + iso-invariance, `hCD`, and the RawW assembly.
No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-423 — the flat star-index recovery.**  `star vertices ≃ components`, from injectivity of a fresh star
assignment on the forest's elements (the flat analog of `starVertexEquivIndex`). -/
noncomputable def flatStarVertexEquivIndex {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s : FeynmanSubgraph G → VertexId)
    (hinj : ∀ γ₁ ∈ B.elements, ∀ γ₂ ∈ B.elements, s γ₁ = s γ₂ → γ₁ = γ₂) :
    {v : VertexId // v ∈ B.starVertices s} ≃ {γ : FeynmanSubgraph G // γ ∈ B.elements} := by
  refine ⟨fun v => ⟨Classical.choose (B.mem_starVertices.mp v.2),
      (Classical.choose_spec (B.mem_starVertices.mp v.2)).1⟩,
    fun γ => ⟨s γ.1, B.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩⟩, ?_, ?_⟩
  · intro v
    exact Subtype.ext (Classical.choose_spec (B.mem_starVertices.mp v.2)).2
  · intro γ
    refine Subtype.ext ?_
    exact hinj _ (Classical.choose_spec (B.mem_starVertices.mp
        (B.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩))).1 γ.1 γ.2
      (Classical.choose_spec (B.mem_starVertices.mp
        (B.mem_starVertices.mpr ⟨γ.1, γ.2, rfl⟩))).2

/-- **R-6c-body-423 — the same-forest star-renaming permutation** `ρ` relating two fresh/injective star assignments. -/
noncomputable def flatStarRenamePerm {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s₁ s₂ : FeynmanSubgraph G → VertexId)
    (h₁ : B.IsFreshStarAssignment s₁) (h₂ : B.IsFreshStarAssignment s₂) : Equiv.Perm VertexId :=
  finsetSubtypeExtensionPerm (B.starVertices s₂) (B.starVertices s₁)
    ((flatStarVertexEquivIndex B s₂ h₂.2).trans (flatStarVertexEquivIndex B s₁ h₁.2).symm)

/-- **R-6c-body-423 — `ρ` fixes ambient vertices** (both star sets avoid `G.vertices` by freshness). -/
theorem flatStarRenamePerm_on_ambient {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s₁ s₂ : FeynmanSubgraph G → VertexId)
    (h₁ : B.IsFreshStarAssignment s₁) (h₂ : B.IsFreshStarAssignment s₂)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    flatStarRenamePerm B s₁ s₂ h₁ h₂ v = v :=
  finsetSubtypeExtensionPerm_apply_of_not_mem _ _ _
    (fun hs => (h₂.star_not_mem_vertices hs) hvG)
    (fun hs => (h₁.star_not_mem_vertices hs) hvG)

/-- **R-6c-body-423 — `ρ` sends each `s₁`-star to the corresponding `s₂`-star.** -/
theorem flatStarRenamePerm_on_stars {G : FeynmanGraph} (B : AdmissibleSubgraph G)
    (s₁ s₂ : FeynmanSubgraph G → VertexId)
    (h₁ : B.IsFreshStarAssignment s₁) (h₂ : B.IsFreshStarAssignment s₂)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ B.elements) :
    flatStarRenamePerm B s₁ s₂ h₁ h₂ (s₁ γ) = s₂ γ := by
  have hmem : s₁ γ ∈ B.starVertices s₁ := B.mem_starVertices.mpr ⟨γ, hγ, rfl⟩
  have hcanon : (⟨s₁ γ, hmem⟩ : {v // v ∈ B.starVertices s₁})
      = (flatStarVertexEquivIndex B s₁ h₁.2).symm ⟨γ, hγ⟩ := Subtype.ext rfl
  rw [flatStarRenamePerm, finsetSubtypeExtensionPerm_on_t _ _ _ hmem, hcanon]
  simp only [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  rfl

end GaugeGeometry.QFT.Combinatorial
