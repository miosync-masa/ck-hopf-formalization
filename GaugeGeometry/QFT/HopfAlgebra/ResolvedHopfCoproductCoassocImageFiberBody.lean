import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterCoverFiberMaps

/-!
# R-6c-body-58 — ImageFiber construction scout: the canonical `selectedOuter ∘ imageOf` fiber

Fifty-eighth genuine-body step, a SCOUT of `ResolvedOuterImageFiberSupply` (body-56) — the IMAGE side of the
OUTPUT σ-cover double sum — locating where its fiber data comes from.

## The decisive coincidence: `selectedOuter` IS an outer-forest index

`(D.supply G).ForestIdx = {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}` and
`(D.supply G).forestCarrier = (D.carrier G).attach` (`ResolvedCoproductProperForestData.supply`).  A quotient
image `ResolvedCoassocQuotientImage D G` carries `selectedOuter : {A : ResolvedAdmissibleSubgraph G //
A ∈ D.carrier G}` — the SAME type.  So each split choice already names its parent outer forest: the fiber map
is just `s ↦ (imageOf s).selectedOuter`, and landing in the outer carrier is FREE (`Finset.mem_attach`, since
`forestCarrier` is the full `attach`).

## What this collapses

Four of `ResolvedOuterImageFiberSupply`'s five fields are therefore CONSTRUCTED, not fielded:

* `forestFiber` / `mixedFiber` := `fun q => (imageOf q.1).selectedOuter` (both sides, same canonical map);
* `forestFiber_maps_to` / `mixedFiber_maps_to` := `fun q _ => Finset.mem_attach _ _`.

The ONLY genuine remaining obligation is the per-`A` agreement.  With the canonical fiber substituted, it reads:

```text
image summand A  (= 1 ⊗ (leftTerm A ⊗ rightTerm A) + coassocRightTail (leftTerm A ⊗ rightTerm A))
  = (∑ q ∈ F.forestCarrier with (imageOf q.1).selectedOuter = A, resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ F.mixedCarrier with (imageOf q.1).selectedOuter = A, resolvedSplitChoiceTerm q.1)
```

i.e. **the coassoc-RIGHT expansion of the outer forest `A` equals the split-term sum over exactly the split
choices whose quotient image selects `A`** — the genuine resolved-native H5.8 image-side coverage.  Via
`term_eq` its RHS is `∑ imageWeight (imageOf q.1)` over that fiber; the identity is that reassembling the image
weights fibered by `selectedOuter` rebuilds `A`'s right expansion.  This is the true coverage geometry and is
fielded here (its proof — the quotient / right-factor de-contraction — is not entered, per the HALT).

## Result

`ResolvedOuterImageFiberSupply` reduces to the single-field `ResolvedImageFiberAgreementSupply` (just the per-`A`
RIGHT-expansion agreement over the canonical `selectedOuter` fiber), via `toImageFiberSupply`.  So the IMAGE side
of the OUTPUT double sum is now `{canonical fiber construction (proved)} + {per-A RIGHT-expansion agreement
(fielded)}` — exactly the split the task asked for.

Per the HALT, the RIGHT-expansion agreement proof (quotient forest / right factor depth) is NOT entered; the
branch side is untouched; no flat `HopfH` transport.

Landed:

* `ResolvedImageFiberAgreementSupply F` — the single per-`A` RIGHT-expansion agreement over the canonical fiber;
* `ResolvedImageFiberAgreementSupply.toImageFiberSupply` — builds the full body-56 image fiber supply (four
  fields constructed, agreement passed through).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-58 — the canonical image forest-fiber map** `selectedOuter ∘ imageOf` (forest side). -/
noncomputable def resolvedImageForestFiber (F : ResolvedCoassocGrandFullSupply D G) :
    {s : ResolvedCoassocSplitChoice D G //
        F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx :=
  fun q => (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1).selectedOuter

/-- **R-6c-body-58 — the canonical image mixed-fiber map** `selectedOuter ∘ imageOf` (mixed side). -/
noncomputable def resolvedImageMixedFiber (F : ResolvedCoassocGrandFullSupply D G) :
    {s : ResolvedCoassocSplitChoice D G //
        ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx :=
  fun q => (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf q.1).selectedOuter

/-- **R-6c-body-58 — the image-side per-`A` RIGHT-expansion agreement over the canonical `selectedOuter`
fiber.**  The single genuine obligation left in `ResolvedOuterImageFiberSupply` once the fiber map is fixed to
`selectedOuter ∘ imageOf`: the coassoc-RIGHT expansion of the outer forest `A` equals the split-term sum over
the split choices whose quotient image selects `A` (forest ⊕ mixed). -/
structure ResolvedImageFiberAgreementSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The RIGHT-expansion of `A` = the split-term sum fibered over `selectedOuter = A`. -/
  image_fiber_agree : ∀ A ∈ (D.supply G).forestCarrier,
    ((1 : ResolvedHopfH) ⊗ₜ[ℚ] ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
        + D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-58 — the canonical image fiber supply.**  Four of body-56's `ResolvedOuterImageFiberSupply`
fields are constructed (fiber = `selectedOuter ∘ imageOf`; `maps_to` = `Finset.mem_attach`); only the per-`A`
RIGHT-expansion agreement is carried. -/
noncomputable def ResolvedImageFiberAgreementSupply.toImageFiberSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedImageFiberAgreementSupply F) :
    ResolvedOuterImageFiberSupply F where
  forestFiber := resolvedImageForestFiber F
  mixedFiber := resolvedImageMixedFiber F
  forestFiber_maps_to := fun _ _ => Finset.mem_attach _ _
  mixedFiber_maps_to := fun _ _ => Finset.mem_attach _ _
  image_fiber_agree := S.image_fiber_agree

end GaugeGeometry.QFT.Combinatorial
