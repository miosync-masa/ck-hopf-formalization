import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Payload

/-!
# Resolved branch separation — `cross` (Track R-4-superfull, Step 7B)

The `cross` field of the flat `forestComponentSplitPhiBranchInjectivitySeparation` is
facade-free: it is a **discriminator separation**.  The flat proof
(`forestComponentSplitPhi_cross_separation`) is
`fun hEq => (not_isForestByStar_of_mixed) (hEq ▸ isForestByStar_of_forest)`: the
forest-branch image satisfies the `isForestByStar` discriminator, the mixed-branch
image violates it, hence they differ.

We capture that **mechanism** here abstractly (`cross_of_discriminator` +
`ResolvedBranchSeparationData`), so the resolved `cross` is a one-liner once the
resolved branch images and discriminator exist.  Those σ-index objects are **not yet
defined** (see the report note); this phase delivers the separation interface and the
precise list of objects an instance requires.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **Discriminator separation (the `cross` mechanism).**  If a property holds of `f`
but not of `m`, then `f ≠ m`.  This is the entire mathematical content of the flat
`cross` field. -/
theorem cross_of_discriminator {Image : Type*} {p : Image → Prop}
    {f m : Image} (hf : p f) (hm : ¬ p m) : f ≠ m :=
  fun h => hm (h ▸ hf)

/-- **Abstract resolved branch-separation data.**  Two index families mapping into a
common image type, with a discriminator the forest images satisfy and the mixed
images violate — the resolved-side shape of `isForestByStar` + its two branch lemmas. -/
structure ResolvedBranchSeparationData where
  /-- The forest-branch index. -/
  ForestIdx : Type*
  /-- The mixed-branch index. -/
  MixedIdx : Type*
  /-- The common RHS image type (resolved `forestQuotientForestSigma`-analogue). -/
  Image : Type*
  /-- The discriminator (resolved `isForestByStar`-analogue). -/
  discriminator : Image → Prop
  /-- The forest-branch image map. -/
  forestImage : ForestIdx → Image
  /-- The mixed-branch image map. -/
  mixedImage : MixedIdx → Image
  /-- Forest images satisfy the discriminator (`…isForestByStar_of_forest`). -/
  forest_sat : ∀ q, discriminator (forestImage q)
  /-- Mixed images violate the discriminator (`…not_isForestByStar_of_mixed`). -/
  mixed_unsat : ∀ q, ¬ discriminator (mixedImage q)

/-- **Resolved cross-branch separation.**  Forest and mixed images never coincide —
the resolved analogue of `forestComponentSplitPhi_cross_separation`, reduced to the
discriminator mechanism. -/
theorem ResolvedBranchSeparationData.cross (S : ResolvedBranchSeparationData)
    (qF : S.ForestIdx) (qM : S.MixedIdx) :
    S.forestImage qF ≠ S.mixedImage qM :=
  cross_of_discriminator (S.forest_sat qF) (S.mixed_unsat qM)

/-! **Report (HALT — branch images not yet defined).**  To *instantiate*
`ResolvedBranchSeparationData` for H5.8 one needs resolved analogues of the flat
σ-index objects (none currently exist):

* `Image`  ← resolved `forestQuotientForestSigma g` (the RHS branch index);
* `forestImage` / `mixedImage` ← resolved `forestComponentForestChoiceToQuotientForestSigma`
  / `…MixedBoundaryToQuotientForestSigma` (the branch maps);
* `discriminator` ← resolved `forestQuotientForestSigma_isForestByStar` (a component of
  the resolved actual-quotient subgraph meeting the star vertices);
* `forest_sat` / `mixed_unsat` ← resolved `…isForestByStar_of_forest` /
  `…not_isForestByStar_of_mixed`.

These are exactly the resolved σ-index branch-map layer (the same layer `mixed_inj` and
`cover` will also need).  The `cross` *mechanism* is now facade-free and trivial; the
remaining work is the σ-index branch-map construction, shared across `cross`/`mixed_inj`/
`cover`. -/

end GaugeGeometry.QFT.Combinatorial
