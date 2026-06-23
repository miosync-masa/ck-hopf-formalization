import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromote

/-!
# R-6c-support-3 (continued) — concrete `leftOf` via `filterElements`

The cheap half of the selected-outer forest.  The flat template
(`forestComponentForestChoiceOuterSubgraph A p`, `Coassoc.lean`) is
`(left-selected ∪ promoted)`, where the left-selected forest is
`admissibleSubgraphOfSubelements A (A.elements.filter (isLeft A p))` — a *sub-forest of the input outer
`A`* cut out by the per-component left-selection predicate.  With the support-3 `filterElements`
constructor in hand, the resolved left-selected forest is now **concrete**: a `filter` of the input
outer forest's components.

The exact left-selection classification (which component choice `Bool ⊕ ForestIdx` lands a component in
the left factor) carries the membership subtlety that the predicate is on a bare
`γ : ResolvedFeynmanSubgraph G` while the choice `s.2` needs `γ ∈ s.1.1.elements.attach`.  Per the HALT,
that classification is **isolated as a supply field** (`ResolvedSplitChoiceLeftSelectionSupply`),
exactly mirroring how `promotedOf` is a supply field in R-6c-support-2 — the *constructor* `leftOf`
(a `filterElements` of the input outer) is concrete; only the predicate is supplied.

Landed:

* `ResolvedCoassocSplitChoice.inputOuter` — the input outer forest `A` of a split choice `(A, p)`;
* `ResolvedSplitChoiceLeftSelectionSupply D G` — the left-selection predicate as a supply field;
* `ResolvedSplitChoiceLeftSelectionSupply.leftOf` (+ `leftOf_elements` simp) — the concrete left-selected
  sub-forest `inputOuter.filterElements leftSelected`;
* `ResolvedSplitChoiceLeftSelectionSupply.toPromoteSupply` — builds a `ResolvedForestPromoteSupply` from
  the concrete `leftOf` plus a supplied `promotedOf` and the cross-disjointness.

No facade, no flat term, no `forgetHopf`; `promotedOf` (the genuine rep/perm promote) stays the single
deferred de-contraction piece.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-3 — the input outer forest of a split choice.**  A split choice is a pair `(A, p)`
with `A` a carrier outer forest; `inputOuter` is that `A` (the first projection). -/
def ResolvedCoassocSplitChoice.inputOuter (s : ResolvedCoassocSplitChoice D G) :
    ResolvedAdmissibleSubgraph G := s.1.1

/-- **R-6c-support-3 — the left-selection supply.**  The per-split-choice predicate picking out the
components of the input outer forest that land in the left factor (the resolved analogue of the flat
`forestComponentChoiceIsLeft`).  Isolated as a supply field because the classification needs the
component's membership in `s.1.1.elements.attach` to evaluate the choice `s.2`, while the predicate is
stated on a bare component — mirroring the deferred `promotedOf`. -/
structure ResolvedSplitChoiceLeftSelectionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The components of the input outer forest selected into the left factor by a split choice. -/
  leftSelected : ResolvedCoassocSplitChoice D G → ResolvedFeynmanSubgraph G → Prop

/-- **R-6c-support-3 — the concrete left-selected sub-forest.**  The components of the input outer
forest satisfying the left-selection predicate, cut out by the support-3 `filterElements`.  This is the
resolved `forestComponentChoiceLeftSubgraph` — concrete, no supply for the *forest* itself (only the
predicate is supplied). -/
noncomputable def ResolvedSplitChoiceLeftSelectionSupply.leftOf
    (L : ResolvedSplitChoiceLeftSelectionSupply D G)
    (s : ResolvedCoassocSplitChoice D G) : ResolvedAdmissibleSubgraph G :=
  s.inputOuter.filterElements (L.leftSelected s)

@[simp] theorem ResolvedSplitChoiceLeftSelectionSupply.leftOf_elements
    (L : ResolvedSplitChoiceLeftSelectionSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (L.leftOf s).elements = s.inputOuter.elements.filter (L.leftSelected s) := rfl

/-- **R-6c-support-3 — assemble the promote supply from the concrete `leftOf`.**  Given the
left-selection supply (which makes `leftOf` concrete) together with a promoted-forest family
`promotedOf` and their cross-disjointness, build the `ResolvedForestPromoteSupply` whose
`selectedOuterRawOf` is `leftOf.union promotedOf`. -/
noncomputable def ResolvedSplitChoiceLeftSelectionSupply.toPromoteSupply
    (L : ResolvedSplitChoiceLeftSelectionSupply D G)
    (promotedOf : ResolvedCoassocSplitChoice D G → ResolvedAdmissibleSubgraph G)
    (cross : ∀ s, ∀ γ ∈ (L.leftOf s).elements, ∀ δ ∈ (promotedOf s).elements,
        γ ≠ δ → γ.Disjoint δ) :
    ResolvedForestPromoteSupply D G where
  leftOf := L.leftOf
  promotedOf := promotedOf
  cross := cross

end GaugeGeometry.QFT.Combinatorial
