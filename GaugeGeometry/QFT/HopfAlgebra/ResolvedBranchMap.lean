import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58BranchSeparation

/-!
# Resolved σ-index branch-map interface (Track R-4-superfull, Step 7C)

Step 7B showed the remaining H5.8 obligations (`cross`, `mixed_inj`, `cover`) all sit
on **one** layer: the resolved σ-index branch maps.  Here we fix that layer's
*interface* (`ResolvedBranchMapLayer`) and prove its generic consequences, **without**
porting the flat `forestComponentForestChoiceToQuotientForestSigma` machinery.

Once an actual layer is instantiated (Step 7D), all three obligations are immediate:
* `cross`     — `forest_sat` + `mixed_unsat` (discriminator, Step 7B);
* `forest_inj`/`mixed_inj` — branch-map injectivity (forest side ← `parentRemnant_injOn`);
* `cover`     — branch-map surjectivity onto the image index.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **Resolved σ-index branch-map layer.**  The abstract interface H5.8 needs: two
branch index families into a common image type, a discriminator separating them, branch
injectivity, and a cover (surjectivity) of the image. -/
structure ResolvedBranchMapLayer where
  /-- Forest-branch index. -/
  ForestIdx : Type*
  /-- Mixed-branch index. -/
  MixedIdx : Type*
  /-- RHS image index (resolved `forestQuotientForestSigma`-analogue). -/
  Image : Type*
  /-- Forest-branch image map. -/
  forestImage : ForestIdx → Image
  /-- Mixed-branch image map. -/
  mixedImage : MixedIdx → Image
  /-- The discriminator (resolved `isForestByStar`-analogue). -/
  isForestByStar : Image → Prop
  /-- Forest images satisfy the discriminator. -/
  forest_sat : ∀ q, isForestByStar (forestImage q)
  /-- Mixed images violate the discriminator. -/
  mixed_unsat : ∀ q, ¬ isForestByStar (mixedImage q)
  /-- Forest-branch injectivity (← `parentRemnant_injOn` at instantiation). -/
  forest_inj : Function.Injective forestImage
  /-- Mixed-branch injectivity. -/
  mixed_inj : Function.Injective mixedImage
  /-- Cover: every image is hit by some branch. -/
  cover : ∀ z : Image, (∃ q, forestImage q = z) ∨ (∃ q, mixedImage q = z)

namespace ResolvedBranchMapLayer

variable (L : ResolvedBranchMapLayer)

/-- **Cross-branch separation** — forest and mixed images never coincide (the `cross`
field of the flat injectivity/separation package). -/
theorem cross (qF : L.ForestIdx) (qM : L.MixedIdx) :
    L.forestImage qF ≠ L.mixedImage qM :=
  cross_of_discriminator (L.forest_sat qF) (L.mixed_unsat qM)

/-- No image is hit by both branches (the discriminator is exclusive). -/
theorem not_both (z : L.Image) :
    ¬ ((∃ q, L.forestImage q = z) ∧ (∃ q, L.mixedImage q = z)) := by
  rintro ⟨⟨qF, hF⟩, qM, hM⟩
  exact L.cross qF qM (hF.trans hM.symm)

/-- **Separated cover:** every image lies in exactly one branch (cover + exclusivity).
This is the classifier content `…IndexedBranchClassifierOfSeparatedCover` consumes. -/
theorem exactly_one_branch (z : L.Image) :
    ((∃ q, L.forestImage q = z) ∧ ¬ (∃ q, L.mixedImage q = z)) ∨
      ((∃ q, L.mixedImage q = z) ∧ ¬ (∃ q, L.forestImage q = z)) := by
  rcases L.cover z with hF | hM
  · exact Or.inl ⟨hF, fun hM => L.not_both z ⟨hF, hM⟩⟩
  · exact Or.inr ⟨hM, fun hF => L.not_both z ⟨hF, hM⟩⟩

/-- Bridge to the Step 7B separation interface. -/
def toSeparationData : ResolvedBranchSeparationData where
  ForestIdx := L.ForestIdx
  MixedIdx := L.MixedIdx
  Image := L.Image
  discriminator := L.isForestByStar
  forestImage := L.forestImage
  mixedImage := L.mixedImage
  forest_sat := L.forest_sat
  mixed_unsat := L.mixed_unsat

end ResolvedBranchMapLayer

/-! **Report (7C-3) — field correspondence to flat H5.8.**  Matching the flat
`forestComponentSplitPhiBranchInjectivitySeparation` (`forest_inj`, `mixed_inj`, `cross`)
+ `…BranchCoverCertificate` (`cover`) → `…BranchInverseCover` → classifier:

| flat | `ResolvedBranchMapLayer` |
|------|--------------------------|
| `forestComponentForestChoiceSigmaIndex` | `ForestIdx` |
| `forestComponentMixedBoundaryChoiceSigmaIndex` | `MixedIdx` |
| `forestQuotientForestSigma` | `Image` |
| `…ForestChoiceToQuotientForestSigma` | `forestImage` |
| `…MixedBoundaryToQuotientForestSigma` | `mixedImage` |
| `forestQuotientForestSigma_isForestByStar` | `isForestByStar` |
| `…isForestByStar_of_forest` / `…not_…_of_mixed` | `forest_sat` / `mixed_unsat` |
| `forest_inj` / `mixed_inj` fields | `forest_inj` / `mixed_inj` |
| `…BranchCoverCertificate.cover` | `cover` |

`cross`, `not_both`, `exactly_one_branch` are derived here.  The flat
`…InverseCover` bundles exactly `{forest_inj, mixed_inj, cross, cover}` — all present
or derivable.  **Instantiation (Step 7D)** must supply the four constructive fields
(`forestImage`, `mixedImage`, `isForestByStar`, `cover`) from the resolved σ-index;
`forest_inj` comes from `ResolvedSigmaCoverData.parentRemnant_injOn`, `forest_sat`/
`mixed_unsat` from the resolved actual-quotient discriminator. -/

end GaugeGeometry.QFT.Combinatorial
