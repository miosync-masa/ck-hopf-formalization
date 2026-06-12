import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Classifier

/-!
# Abstract H5.8 sum-reindex (Track R-4-superfull, Step 7G)

The algebraic heart of `coassoc_strict_forest_linear_h58`, abstracted to a pure
`Finset` statement over a `ResolvedBranchMapLayer` with finite carriers:

  ∑ over Image  =  ∑ over forest branch  +  ∑ over mixed branch

for any additive-commutative-monoid weight `w`.  The forest/mixed branch images
partition the image carrier (cover + cross), and each branch map is injective, so the
sum splits and reindexes.  Plugging the concrete `HopfH`-tensor weight later turns this
into the H5.8 reindexing identity.
-/

set_option linter.unusedSectionVars false

open scoped Classical

namespace GaugeGeometry.QFT.Combinatorial

/-- A branch-map layer with finite, complete carriers for forest/mixed/image. -/
structure ResolvedFiniteBranchMapLayer where
  /-- The underlying branch-map layer. -/
  layer : ResolvedBranchMapLayer
  /-- Finite carrier of forest indices. -/
  forestCarrier : Finset layer.ForestIdx
  /-- Finite carrier of mixed indices. -/
  mixedCarrier : Finset layer.MixedIdx
  /-- Finite carrier of images. -/
  imageCarrier : Finset layer.Image
  /-- The forest carrier is complete. -/
  forest_mem : ∀ q, q ∈ forestCarrier
  /-- The mixed carrier is complete. -/
  mixed_mem : ∀ q, q ∈ mixedCarrier
  /-- The image carrier is complete. -/
  image_mem : ∀ z, z ∈ imageCarrier

namespace ResolvedFiniteBranchMapLayer

variable (FL : ResolvedFiniteBranchMapLayer)

/-- The forest-branch images. -/
noncomputable def forestImages : Finset FL.layer.Image := FL.forestCarrier.image FL.layer.forestImage

/-- The mixed-branch images. -/
noncomputable def mixedImages : Finset FL.layer.Image := FL.mixedCarrier.image FL.layer.mixedImage

/-- **Branch images are disjoint** (from cross-branch separation). -/
theorem disjoint_images : Disjoint FL.forestImages FL.mixedImages := by
  rw [Finset.disjoint_left]
  intro z hzF hzM
  obtain ⟨qF, _, hqF⟩ := Finset.mem_image.mp hzF
  obtain ⟨qM, _, hqM⟩ := Finset.mem_image.mp hzM
  exact FL.layer.cross qF qM (hqF.trans hqM.symm)

/-- **The image carrier is partitioned** into forest and mixed images (cover). -/
theorem imageCarrier_eq : FL.imageCarrier = FL.forestImages ∪ FL.mixedImages := by
  apply Finset.ext
  intro z
  refine ⟨fun _ => ?_, fun _ => FL.image_mem z⟩
  rcases FL.layer.cover z with ⟨qF, hqF⟩ | ⟨qM, hqM⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨qF, FL.forest_mem qF, hqF⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨qM, FL.mixed_mem qM, hqM⟩)

/-- **H5.8 abstract sum-reindex.**  A sum over the image carrier splits as a sum over
the forest branch plus a sum over the mixed branch — the algebraic heart of
`coassoc_strict_forest_linear_h58`, here pure `Finset`. -/
theorem sum_reindex {M : Type*} [AddCommMonoid M] (w : FL.layer.Image → M) :
    ∑ z ∈ FL.imageCarrier, w z =
      (∑ q ∈ FL.forestCarrier, w (FL.layer.forestImage q)) +
      (∑ q ∈ FL.mixedCarrier, w (FL.layer.mixedImage q)) := by
  rw [FL.imageCarrier_eq, forestImages, mixedImages,
    Finset.sum_union (by
      rw [← forestImages, ← mixedImages]; exact FL.disjoint_images),
    Finset.sum_image (fun x _ y _ h => FL.layer.forest_inj h),
    Finset.sum_image (fun x _ y _ h => FL.layer.mixed_inj h)]

end ResolvedFiniteBranchMapLayer

/-! **Report (7G).**
* `ResolvedFiniteBranchMapLayer` (layer + complete `Finset` carriers — no global
  `Fintype` needed) + `disjoint_images` + `imageCarrier_eq` (partition) + `sum_reindex`
  — landed, axiom-light.
* `sum_reindex` is the abstract H5.8 reindexing identity: `∑ image = ∑ forest + ∑ mixed`
  for any `AddCommMonoid` weight.  The concrete `coassoc_strict_forest_linear_h58` is now
  this identity with the `HopfH ⊗ (HopfH ⊗ HopfH)` tensor-term weight `w` — the final
  step is to supply that weight and match it to the flat double-sum. -/

/-! ## Carrier-based finite layer (案A — infinite `Image`, finite quotient carrier)

`ResolvedFiniteBranchMapLayer` above states completeness/cover over the **whole** `Image`
type, which forces `Image` finite.  For the actual construction `Image =
ResolvedAdmissibleSubgraph (contracted)` is *infinite*, and H5.8 sums only over the finite
RHS quotient carrier.  This carrier-based variant fixes that: `Image` may be any type;
everything is stated over `imageCarrier` (the finite quotient index).  `cover_on` is the
genuine σ-cover surjectivity over that carrier. -/

/-- A branch-map layer with a **finite quotient carrier** — completeness/cover stated over
`imageCarrier` only, so `Image` may be an infinite type. -/
structure ResolvedCarrierFiniteBranchMapLayer where
  /-- The underlying branch-map layer (`Image` may be infinite). -/
  layer : ResolvedBranchMapLayer
  /-- Finite forest-index carrier. -/
  forestCarrier : Finset layer.ForestIdx
  /-- Finite mixed-index carrier. -/
  mixedCarrier : Finset layer.MixedIdx
  /-- Finite image (quotient) carrier — the set actually summed over. -/
  imageCarrier : Finset layer.Image
  /-- Forest images land in the image carrier. -/
  forestImage_mem : ∀ q ∈ forestCarrier, layer.forestImage q ∈ imageCarrier
  /-- Mixed images land in the image carrier. -/
  mixedImage_mem : ∀ q ∈ mixedCarrier, layer.mixedImage q ∈ imageCarrier
  /-- Cover over the carrier: every carrier image is a forest or mixed branch image. -/
  cover_on : ∀ z ∈ imageCarrier,
    (∃ q ∈ forestCarrier, layer.forestImage q = z) ∨
      (∃ q ∈ mixedCarrier, layer.mixedImage q = z)
  /-- Forest injectivity on the carrier. -/
  forest_inj_on : ∀ q₁ ∈ forestCarrier, ∀ q₂ ∈ forestCarrier,
    layer.forestImage q₁ = layer.forestImage q₂ → q₁ = q₂
  /-- Mixed injectivity on the carrier. -/
  mixed_inj_on : ∀ q₁ ∈ mixedCarrier, ∀ q₂ ∈ mixedCarrier,
    layer.mixedImage q₁ = layer.mixedImage q₂ → q₁ = q₂

namespace ResolvedCarrierFiniteBranchMapLayer

variable (FL : ResolvedCarrierFiniteBranchMapLayer)

/-- **Carrier-based H5.8 sum-reindex.**  The sum over the finite quotient carrier splits
into the forest and mixed branch sums — `Image` may be infinite; only the carrier is
summed.  This is the correct finite-reindex formulation. -/
theorem sum_reindex {M : Type*} [AddCommMonoid M] (w : FL.layer.Image → M) :
    ∑ z ∈ FL.imageCarrier, w z =
      (∑ q ∈ FL.forestCarrier, w (FL.layer.forestImage q)) +
      (∑ q ∈ FL.mixedCarrier, w (FL.layer.mixedImage q)) := by
  have hpart : FL.imageCarrier =
      FL.forestCarrier.image FL.layer.forestImage ∪
        FL.mixedCarrier.image FL.layer.mixedImage := by
    apply Finset.Subset.antisymm
    · intro z hz
      rcases FL.cover_on z hz with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hq)
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hq)
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz; exact FL.forestImage_mem q hq
      · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz; exact FL.mixedImage_mem q hq
  have hdisj : Disjoint (FL.forestCarrier.image FL.layer.forestImage)
      (FL.mixedCarrier.image FL.layer.mixedImage) := by
    rw [Finset.disjoint_left]
    intro z hzF hzM
    obtain ⟨qF, _, hqF⟩ := Finset.mem_image.mp hzF
    obtain ⟨qM, _, hqM⟩ := Finset.mem_image.mp hzM
    exact FL.layer.cross qF qM (hqF.trans hqM.symm)
  rw [hpart, Finset.sum_union hdisj,
    Finset.sum_image (fun x hx y hy h => FL.forest_inj_on x hx y hy h),
    Finset.sum_image (fun x hx y hy h => FL.mixed_inj_on x hx y hy h)]

end ResolvedCarrierFiniteBranchMapLayer

end GaugeGeometry.QFT.Combinatorial
