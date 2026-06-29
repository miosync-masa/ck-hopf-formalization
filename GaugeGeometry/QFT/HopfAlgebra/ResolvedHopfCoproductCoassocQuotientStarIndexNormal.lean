import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndexScout

/-!
# R-6c-heart-6a-10a — quotient-star index normal forms (BIGGEST entrance)

Before constructing the BIGGEST `quotientStarEquiv : {i // i.hasQuotientStar} ≃ TwoStageStarIndex`, this
normalises its domain and codomain into matching sums:

* **domain** `{i : OneStageStarIndex // i.hasQuotientStar}` ≃ `RightPrimitiveIndex ⊕ ForestPrimitiveIndex`
  — CONSTRUCTED here, since `hasQuotientStar = isRight ∨ isForest` and the two are disjoint (5b-1);
* **codomain** `TwoStageStarIndex` ≃ `RightSurvivorIndex ⊕ RemnantIndex` — the genuine `Right ⊔ Remnant`
  split (5b-4), kept as a supply field (`ResolvedQuotientStarCodomainSplitSupply`).

Then `quotientStarEquiv` is `quotientDomainEquiv.trans ((rightEquiv.sumCongr forestEquiv).trans
codomainEquiv.symm)` — reducing the BIGGEST to the two per-sector correspondences
`RightPrimitiveIndex ≃ RightSurvivorIndex` and `ForestPrimitiveIndex ≃ RemnantIndex`.

Per the HALT, the codomain split and the two sector correspondences are NOT constructed; no term / edge /
retarget.

Landed:

* `RightPrimitiveIndex` / `ForestPrimitiveIndex` — the domain sectors;
* `quotientDomainEquiv` — the CONSTRUCTED domain normal form;
* `ResolvedQuotientStarCodomainSplitSupply` — the codomain `Right ⊔ Remnant` split (fielded);
* `quotientStarEquivOf` — the `sumCongr` assembly from the two sector correspondences.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-10a — a right-primitive domain index.**  A one-stage star whose component is
right-primitive. -/
structure RightPrimitiveIndex (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- The one-stage star. -/
  i : OneStageStarIndex D G s
  /-- Its component is right-primitive. -/
  hR : i.isRight

/-- **R-6c-heart-6a-10a — a forest-choice domain index.**  A one-stage star whose component is a forest
choice. -/
structure ForestPrimitiveIndex (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- The one-stage star. -/
  i : OneStageStarIndex D G s
  /-- Its component is a forest choice. -/
  hF : i.isForest

open Classical in
/-- **R-6c-heart-6a-10a — the domain normal form (CONSTRUCTED).**  The quotient-star domain splits into the
right-primitive and forest-choice sectors (`hasQuotientStar = isRight ∨ isForest`, disjoint by 5b-1). -/
noncomputable def quotientDomainEquiv (s : ResolvedCoassocSplitChoice D G) :
    {i : OneStageStarIndex D G s // i.hasQuotientStar} ≃
      (RightPrimitiveIndex D G s ⊕ ForestPrimitiveIndex D G s) where
  toFun := fun v => if hR : v.1.isRight then Sum.inl ⟨v.1, hR⟩ else Sum.inr ⟨v.1, v.2.resolve_left hR⟩
  invFun := fun x => Sum.elim (fun r => ⟨r.i, Or.inl r.hR⟩) (fun f => ⟨f.i, Or.inr f.hF⟩) x
  left_inv := fun v => by
    rcases v with ⟨i, h⟩
    by_cases hR : i.isRight
    · simp only [dif_pos hR, Sum.elim_inl]
    · simp only [dif_neg hR, Sum.elim_inr]
  right_inv := fun x => by
    cases x with
    | inl r => simp only [Sum.elim_inl, dif_pos r.hR]
    | inr f =>
        have hnr : ¬ f.i.isRight := fun hR => s.not_isForestChoice_of_isRightPrimitive hR f.hF
        simp only [Sum.elim_inr, dif_neg hnr]

variable {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10a — the codomain normal form (fielded).**  The genuine `Right ⊔ Remnant` split of the
quotient-forest stars into right-survivor and remnant sectors. -/
structure ResolvedQuotientStarCodomainSplitSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right-survivor sector of the quotient-forest stars. -/
  RightSurvivorIndex : ResolvedCoassocSplitChoice D G → Type
  /-- The remnant sector of the quotient-forest stars. -/
  RemnantIndex : ResolvedCoassocSplitChoice D G → Type
  /-- The two-stage stars split as right-survivor ⊕ remnant (the `Right ⊔ Remnant` decomposition). -/
  codomainEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
    TwoStageStarIndex D G imageOf s ≃ (RightSurvivorIndex s ⊕ RemnantIndex s)

/-- **R-6c-heart-6a-10a — the BIGGEST assembly from the two sector correspondences.**  Given the
domain/codomain normal forms, `quotientStarEquiv` is the `sumCongr` of the right ↔ right-survivor and
forest ↔ remnant correspondences. -/
noncomputable def quotientStarEquivOf (C : ResolvedQuotientStarCodomainSplitSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G)
    (rightEquiv : RightPrimitiveIndex D G s ≃ C.RightSurvivorIndex s)
    (forestEquiv : ForestPrimitiveIndex D G s ≃ C.RemnantIndex s) :
    {i : OneStageStarIndex D G s // i.hasQuotientStar} ≃ TwoStageStarIndex D G imageOf s :=
  (quotientDomainEquiv s).trans ((rightEquiv.sumCongr forestEquiv).trans (C.codomainEquiv s).symm)

end GaugeGeometry.QFT.Combinatorial
