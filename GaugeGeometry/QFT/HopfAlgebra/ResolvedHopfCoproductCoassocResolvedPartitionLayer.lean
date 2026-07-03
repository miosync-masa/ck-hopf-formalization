import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFiniteCoverCarriersBody

/-!
# R-6c-body-53 — the resolved partition reindex from the GrandFull cover

Fifty-third genuine-body step, recovering body-52's REUSABLE partition half: the splitPhi finite cover's image
sum equals its forest ⊕ mixed sum, resolved-natively over `ResolvedHopfH3` (indeed any `AddCommMonoid`).

Rather than instantiate `ResolvedFiniteBranchMapLayer` (whose `forest_mem : ∀ q, q ∈ forestCarrier` forces the
whole index type into the carrier — the GrandFull cover is carrier-based, a specific `Finset` of a subtype), we
replay the H5.8 partition proof directly on the GrandFull cover fields:

* `imageCarrier = forestImages ∪ mixedImages` — from `cover_on` (⊆) and `forest/mixedImage_mem` (⊇);
* `Disjoint forestImages mixedImages` — from body-39's `grandFull_forest_image_ne_mixed_image` (the `cross`);
* `Finset.sum_union` + `Finset.sum_image` (with `forest/mixed_inj_on`).

So the partition is FULLY resolved-native and reusable — no flat `HopfH`, no `ResolvedFiniteBranchMapLayer`
total-membership mismatch.  The remaining reindex obstruction is now exactly the outer-forest ↔ cover
connection (body-52 adapter (4)), a resolved σ-cover construction.

Per the HALT, the outer-forest carrier is not touched; only the splitPhi-cover-internal partition is proved; no
flat `HopfH`.

Landed:

* `grandFull_partition_reindex` — `∑ imageCarrier w = ∑ forestCarrier w∘imageOf + ∑ mixedCarrier w∘imageOf`,
  for any `w : ResolvedCoassocQuotientImage → M` (`M` an `AddCommMonoid`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false in
/-- **R-6c-body-53 — the resolved splitPhi-cover partition reindex.**  The finite image cover sum equals the
forest ⊕ mixed cover sum, for any `AddCommMonoid`-valued weight — the carrier-agnostic partition, proved
directly from the GrandFull cover (`cover_on` + `inj_on` + body-39 `cross`). -/
theorem grandFull_partition_reindex {M : Type*} [AddCommMonoid M]
    (F : ResolvedCoassocGrandFullSupply D G)
    (w : ResolvedCoassocQuotientImage D G → M) :
    ∑ z ∈ F.imageCarrier, w z =
      (∑ q ∈ F.forestCarrier,
          w (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1)) +
        (∑ q ∈ F.mixedCarrier,
          w (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1)) := by
  classical
  have hcov : F.imageCarrier =
      F.forestCarrier.image
          (fun q => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1) ∪
        F.mixedCarrier.image
          (fun q => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hz
      rcases F.cover_on z hz with ⟨q, hq, hqz⟩ | ⟨q, hq, hqz⟩
      · exact Or.inl ⟨q, hq, hqz⟩
      · exact Or.inr ⟨q, hq, hqz⟩
    · rintro (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact F.forestImage_mem q hq
      · exact F.mixedImage_mem q hq
  have hdisj : Disjoint
      (F.forestCarrier.image
        (fun q => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1))
      (F.mixedCarrier.image
        (fun q => F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1)) := by
    rw [Finset.disjoint_left]
    intro z hzF hzM
    obtain ⟨qF, _, hqFz⟩ := Finset.mem_image.mp hzF
    obtain ⟨qM, _, hqMz⟩ := Finset.mem_image.mp hzM
    exact grandFull_forest_image_ne_mixed_image F qF qM (hqFz.trans hqMz.symm)
  rw [hcov, Finset.sum_union hdisj,
    Finset.sum_image (fun q₁ hq₁ q₂ hq₂ h => F.forest_inj_on q₁ hq₁ q₂ hq₂ h),
    Finset.sum_image (fun q₁ hq₁ q₂ hq₂ h => F.mixed_inj_on q₁ hq₁ q₂ hq₂ h)]

end GaugeGeometry.QFT.Combinatorial
