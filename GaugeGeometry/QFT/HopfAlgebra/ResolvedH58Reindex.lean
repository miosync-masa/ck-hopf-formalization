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

end GaugeGeometry.QFT.Combinatorial
