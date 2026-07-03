import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageStrictSummandReconstruction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputBoundaryCovers

/-!
# R-6c-body-82 — image boundary cover body: `1 ⊗ forestSum` discharged, only the ∅-fiber structure remains

Eighty-second genuine-body step, reducing body-81's `boundary_cover` using body-70's PROVED all-right-primitive
lemma.  The shallow `1 ⊗ forestSum` bookkeeping falls; what remains is the genuine `∅`-fiber structure.

## The reduction

Body-81's `boundary_cover` is `∑_{boundary A} fiber A = 1 ⊗ forestSum + ∑_{boundary A} coassocRightTail A`.
Body-70 PROVED `1 ⊗ forestSum G = ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩` (the image boundary is the
all-right-primitive term sum).  Substituting, `boundary_cover` reduces to the pure `∅`-fiber identity

```text
boundary_fiber_ident :  ∑_{boundary A} fiber A  =  ∑_A splitTerm ⟨A, allRightPrimitive⟩  +  ∑_{boundary A} coassocRightTail A
```

— the boundary (`leftTerm A = 1`, empty-`selectedOuter`) fibers collect exactly the all-right-primitive split
terms (over ALL base outers `A`, body-70) plus their own right tails.  `ResolvedImageBoundaryFiberSupply.
boundary_cover` recovers body-81's field by `rw [resolved_image_boundary_eq_allRightPrimitive_sum]`.

## What remains

`boundary_fiber_ident` is the genuine `∅`-fiber content: which split choices land in the empty-`selectedOuter`
fiber (the all-right-primitives, plus whatever else the `∅` outer's own tail covers).  The `1 ⊗ forestSum`
tensor bookkeeping is now DISCHARGED by the proved body-70 lemma; only this combinatorial `∅`-fiber
identification is fielded.  `toStrictToOuterCoverSupply` bundles it with body-80's `Strict` to produce body-81's
`ResolvedImageStrictToOuterCoverSupply` (whence `outer_image_cover` → body-54 → `coassoc_gen`).

So the IMAGE OUTPUT obligations are now: `strict_summand_cover` (body-80, non-boundary tails, the deep
`right_eq` quotient de-contraction) + `boundary_fiber_ident` (body-82, the shallow `∅`-fiber identification).
The shallow boundary stone is off the pile.

Per the HALT, `isBoundaryOuter` stays the abstract guard (from body-80's `Strict`); `boundary_fiber_ident` is
fielded (the `∅`-fiber structure); `strict_summand_cover` is not entered; the `1 ⊗ forestSum` bookkeeping is
proved-away via body-70.

Landed:

* `ResolvedImageBoundaryFiberSupply F Strict` — the `∅`-fiber identity (`boundary_fiber_ident`);
* `.boundary_cover` — body-81's `boundary_cover`, via body-70;
* `.toStrictToOuterCoverSupply` — bundles to body-81's reconstruction supply.

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

/-- **R-6c-body-82 — the `∅`-fiber identity** (the boundary content after `1 ⊗ forestSum` is discharged).  The
boundary (`isBoundaryOuter`) fibers equal the all-right-primitive split terms (over all base outers, body-70)
plus their own right tails. -/
structure ResolvedImageBoundaryFiberSupply (F : ResolvedCoassocGrandFullSupply D G)
    (Strict : ResolvedImageStrictSummandCoverSupply F) where
  /-- The boundary fibers = the all-right-primitive terms + the boundary right tails. -/
  boundary_fiber_ident :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
        + ∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)

/-- **R-6c-body-82 — body-81's `boundary_cover` from the `∅`-fiber identity.**  Discharge `1 ⊗ forestSum` via
body-70's proved all-right-primitive lemma. -/
theorem ResolvedImageBoundaryFiberSupply.boundary_cover
    {F : ResolvedCoassocGrandFullSupply D G} {Strict : ResolvedImageStrictSummandCoverSupply F}
    (B : ResolvedImageBoundaryFiberSupply F Strict) :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [resolved_image_boundary_eq_allRightPrimitive_sum]
  exact B.boundary_fiber_ident

/-- **R-6c-body-82 — bundle to body-81's reconstruction supply.**  Body-80's `Strict` + the `∅`-fiber identity
give body-81's `ResolvedImageStrictToOuterCoverSupply` (whence `outer_image_cover`). -/
def ResolvedImageBoundaryFiberSupply.toStrictToOuterCoverSupply
    {F : ResolvedCoassocGrandFullSupply D G} {Strict : ResolvedImageStrictSummandCoverSupply F}
    (B : ResolvedImageBoundaryFiberSupply F Strict) : ResolvedImageStrictToOuterCoverSupply F where
  Strict := Strict
  boundary_cover := B.boundary_cover

end GaugeGeometry.QFT.Combinatorial
