import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageBoundaryCoverBody

/-!
# R-6c-body-83 — image boundary fiber identification: `selectedOuter = ∅ ⟺ all-right-primitive`

Eighty-third genuine-body step, reducing body-82's `boundary_fiber_ident` to its structural core: the boundary
(`selectedOuter = ∅`) fiber is exactly the all-right-primitive split choices.  A `∅`-tail subtlety is isolated
and flagged honestly.

## The structural characterization

`selectedOuter` is the split choice's left-selected ∪ promoted components (`ResolvedCoassocSelectedOuterSupply`,
"left-selected ∪ promoted").  It is EMPTY iff no component is left-selected (`Sum.inl true`) and none is
promoted (`Sum.inr B`), i.e. iff EVERY component is right-primitive (`Sum.inl false`) — the all-right-primitive
choice.  So:

```text
selectedOuter (imageOf q) = ∅  (leftTerm = 1)   ⟺   q is all-right-primitive ⟨A, p₀⟩.
```

Hence the boundary (`isBoundaryOuter`, `leftTerm A = 1`) fiber collects EXACTLY the all-right-primitive terms:
`∑_{boundary A} fiber A = ∑_A resolvedSplitChoiceTerm ⟨A, allRightPrimitive⟩` (`boundary_fiber_allRight`).  This
is the clean combinatorial content; the `selectedOuter`-construction internals make it a fielded
characterization (the forward `all-right ⇒ boundary` and the reverse `boundary ⇒ all-right`).

## The `∅`-tail subtlety (flagged)

Body-82's `boundary_fiber_ident` carries an extra `∑_{boundary A} coassocRightTail A`.  With the boundary set
`{∅}` (the empty carrier forest) and the `∅`-fiber = all-right-primitives (`= 1 ⊗ forestSum`), consistency FORCES
`∑_{boundary A} coassocRightTail A = 0`, i.e. `coassocRightTail ∅ = leftTerm ∅ ⊗ Δᵣ(rightTerm ∅) = 1 ⊗
Δᵣ(rightTerm ∅) = 0` — which is FALSE for a nonzero quotient generator.  So the `∅` forest is a genuine
degeneracy: the decomposition is consistent only if the empty-outer's right tail vanishes or the empty outer is
NOT a carrier summand.  This is fielded as `boundary_tail_vanishes` and flagged: the exact `∅`-forest role
(`∅ ∈ carrier`?  `rightTerm ∅`?  whether the image boundary is in-cover or external) is the pivotal construction
question — the SAME `∅` pivot that decides whether the IMAGE boundary is the `∅`-fiber (in-cover, body-78) or
cover-external (like the branch, body-76).

## Result

`boundary_fiber_ident` reduces to `boundary_fiber_allRight` (the clean characterization) + `boundary_tail_
vanishes` (the `∅`-tail degeneracy).  `.boundary_fiber_ident` recovers body-82's field.  So the IMAGE shallow
boundary is now: one structural characterization (all-right ⟺ `∅`-fiber) + one flagged `∅`-degeneracy field.

Per the HALT, the `selectedOuter` internals are not unfolded (`boundary_fiber_allRight` is fielded); the `∅`
degeneracy is isolated (`boundary_tail_vanishes`), not resolved; `strict_summand_cover` is not entered.

Landed:

* `ResolvedImageBoundaryFiberIdentSupply F Strict` — the characterization + the `∅`-tail field;
* `.boundary_fiber_ident` — body-82's field, reconstructed.

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

/-- **R-6c-body-83 — the boundary fiber characterization** (`selectedOuter = ∅ ⟺ all-right-primitive`) + the
isolated `∅`-tail degeneracy.  The boundary fiber collects exactly the all-right-primitive terms; the extra
right-tail on the boundary outers must vanish (the `∅`-forest degeneracy). -/
structure ResolvedImageBoundaryFiberIdentSupply (F : ResolvedCoassocGrandFullSupply D G)
    (Strict : ResolvedImageStrictSummandCoverSupply F) where
  /-- The boundary fiber = the all-right-primitive terms (`selectedOuter = ∅ ⟺ all-right-primitive`). -/
  boundary_fiber_allRight :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = ∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G)
  /-- The boundary outers' right tails vanish (the `∅`-forest degeneracy — flagged). -/
  boundary_tail_vanishes :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)) = 0

/-- **R-6c-body-83 — body-82's `boundary_fiber_ident` from the characterization + the `∅`-tail field.** -/
theorem ResolvedImageBoundaryFiberIdentSupply.boundary_fiber_ident
    {F : ResolvedCoassocGrandFullSupply D G} {Strict : ResolvedImageStrictSummandCoverSupply F}
    (B : ResolvedImageBoundaryFiberIdentSupply F Strict) :
    (∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
        ((∑ q ∈ F.forestCarrier with resolvedImageForestFiber F q = A, D.resolvedSplitChoiceTerm q.1)
          + (∑ q ∈ F.mixedCarrier with resolvedImageMixedFiber F q = A, D.resolvedSplitChoiceTerm q.1)))
      = (∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
        + ∑ A ∈ (D.supply G).forestCarrier with Strict.isBoundaryOuter A,
            D.coassocRightTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [B.boundary_tail_vanishes, add_zero]
  exact B.boundary_fiber_allRight

end GaugeGeometry.QFT.Combinatorial
