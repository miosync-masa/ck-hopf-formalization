import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageFiberBody

/-!
# R-6c-body-59 — BranchFiber construction scout: the canonical base-outer `s.1` fiber

Fifty-ninth genuine-body step, the LEFT-side mirror of body-58.  Scouts `ResolvedOuterBranchFiberSupply`
(body-56) — the BRANCH side of the OUTPUT σ-cover double sum — and confirms it too collapses to
`{canonical fiber construction} + {one per-A agreement}`.

## The branch fiber is the split choice's BASE outer `s.1`

Body-58 fibered the IMAGE side by `(imageOf s).selectedOuter` (the image-SELECTED / promoted outer), because
the image carrier groups by the quotient image's outer.  The BRANCH side is different: the LEFT expansion
`(Δᵣ ⊗ 1) ∘ Δᵣ` first splits `G` into `(outer forest, quotient)` and re-splits the OUTER forest — the outer
here is the ORIGINAL selected forest, and `D.resolvedSplitChoiceTerm s = assoc(∏ localChoiceTerm ⊗ rightTerm
s.1)` is already keyed to `s.1`.  So the branch fiber is the split choice's BASE outer:

`ResolvedCoassocSplitChoice D G = Σ A : {A // A ∈ D.carrier G}, ∀ γ ∈ A.1.elements.attach, …`, hence
`s.1 : {A // A ∈ D.carrier G} = (D.supply G).ForestIdx` — the SAME outer-index type again.  The branch fiber
map is just `s ↦ s.1` (`fun q => q.1.1`), and landing in the outer carrier is again FREE (`Finset.mem_attach`,
`forestCarrier = (D.carrier G).attach`).

## What this collapses (mirroring body-58)

Four of `ResolvedOuterBranchFiberSupply`'s five fields are constructed:

* `forestFiber` / `mixedFiber` := `fun q => q.1.1` (both sides, the base outer);
* `forestFiber_maps_to` / `mixedFiber_maps_to` := `fun _ _ => Finset.mem_attach _ _`.

The ONLY genuine remaining obligation is the per-`A` LEFT-expansion agreement:

```text
branch summand A  (= assoc((leftTerm A ⊗ rightTerm A) ⊗ 1) + coassocLeftTail (leftTerm A ⊗ rightTerm A))
  = (∑ q ∈ F.forestCarrier with q.1.1 = A, resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ F.mixedCarrier with q.1.1 = A, resolvedSplitChoiceTerm q.1)
```

i.e. **the coassoc-LEFT expansion of the outer forest `A` equals the split-term sum over exactly the split
choices whose base outer is `A`** — the genuine resolved-native H5.8 branch-side coverage, fielded here (its
proof — the outer re-split — is not entered, per the HALT).

## Result — the OUTPUT fiber layer is now left-right symmetric

`ResolvedOuterBranchFiberSupply` reduces to the single-field `ResolvedBranchFiberAgreementSupply` via
`toBranchFiberSupply`.  Together with body-58, the ENTIRE OUTPUT fiber layer is now:

* IMAGE side = canonical `selectedOuter ∘ imageOf` fiber (proved) + `image_fiber_agree` (RIGHT-expansion);
* BRANCH side = canonical base-outer `s.1` fiber (proved) + `branch_fiber_agree` (LEFT-expansion).

The fiber CONSTRUCTIONS have vanished into `mem_attach` on both sides; the OUTPUT σ-cover double sum is down to
**two per-`A` expansion agreements** (one RIGHT, one LEFT).

Per the HALT, the LEFT-expansion agreement proof is NOT entered; the image side is not re-touched (only imported
for its symmetric shape); the two sides are kept as separate supplies (`s.1` vs `selectedOuter` — not unified);
no flat `HopfH` transport.

Landed:

* `resolvedBranchForestFiber` / `resolvedBranchMixedFiber` — the canonical base-outer `s.1` fiber maps;
* `ResolvedBranchFiberAgreementSupply F` — the single per-`A` LEFT-expansion agreement;
* `ResolvedBranchFiberAgreementSupply.toBranchFiberSupply` — the full body-56 branch fiber supply.

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

/-- **R-6c-body-59 — the canonical branch forest-fiber map** `s ↦ s.1` (the split choice's base outer, forest
side). -/
noncomputable def resolvedBranchForestFiber (F : ResolvedCoassocGrandFullSupply D G) :
    {s : ResolvedCoassocSplitChoice D G //
        F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx :=
  fun q => q.1.1

/-- **R-6c-body-59 — the canonical branch mixed-fiber map** `s ↦ s.1` (the split choice's base outer, mixed
side). -/
noncomputable def resolvedBranchMixedFiber (F : ResolvedCoassocGrandFullSupply D G) :
    {s : ResolvedCoassocSplitChoice D G //
        ¬ F.ImageTerm.toImageSideTermSupply.toSplitPhiData.discriminator
          (F.ImageTerm.toImageSideTermSupply.toSplitPhiData.imageOf s)} → (D.supply G).ForestIdx :=
  fun q => q.1.1

/-- **R-6c-body-59 — the branch-side per-`A` LEFT-expansion agreement over the canonical base-outer fiber.**
The single genuine obligation left in `ResolvedOuterBranchFiberSupply` once the fiber map is fixed to `s ↦ s.1`:
the coassoc-LEFT expansion of the outer forest `A` equals the split-term sum over the split choices whose base
outer is `A` (forest ⊕ mixed). -/
structure ResolvedBranchFiberAgreementSupply (F : ResolvedCoassocGrandFullSupply D G) where
  /-- The LEFT-expansion of `A` = the split-term sum fibered over the base outer `s.1 = A`. -/
  branch_fiber_agree : ∀ A ∈ (D.supply G).forestCarrier,
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
          (((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A))
      = (∑ q ∈ F.forestCarrier with resolvedBranchForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ F.mixedCarrier with resolvedBranchMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)

/-- **R-6c-body-59 — the canonical branch fiber supply.**  Four of body-56's `ResolvedOuterBranchFiberSupply`
fields are constructed (fiber = base outer `s.1`; `maps_to` = `Finset.mem_attach`); only the per-`A`
LEFT-expansion agreement is carried. -/
noncomputable def ResolvedBranchFiberAgreementSupply.toBranchFiberSupply
    {F : ResolvedCoassocGrandFullSupply D G} (S : ResolvedBranchFiberAgreementSupply F) :
    ResolvedOuterBranchFiberSupply F where
  forestFiber := resolvedBranchForestFiber F
  mixedFiber := resolvedBranchMixedFiber F
  forestFiber_maps_to := fun _ _ => Finset.mem_attach _ _
  mixedFiber_maps_to := fun _ _ => Finset.mem_attach _ _
  branch_fiber_agree := S.branch_fiber_agree

end GaugeGeometry.QFT.Combinatorial
