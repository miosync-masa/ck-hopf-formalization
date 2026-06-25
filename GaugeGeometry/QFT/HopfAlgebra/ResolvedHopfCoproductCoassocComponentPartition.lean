import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelectConcrete

/-!
# R-6c-heart-5b-1 — the local-choice component partition

`product_eq` (heart-5) cannot be proved while `fullQuotientOf` is an arbitrary supply: the quotient
forest must be built from the **same** split-choice data that builds the selected-outer forest.  The
quotient = `Right ⊔ Remnant`, where the pieces come from the per-component local choices:

* `Sum.inl true`  — left primitive (`X γ ⊗ 1`): selected-outer side, **not** quotient;
* `Sum.inl false` — right primitive (`1 ⊗ X γ`): quotient **right-survivor**;
* `Sum.inr B`     — forest choice: selected-outer **promoted** piece *and* quotient **remnant** piece.

This file lays the foundation: it classifies each input outer component (`s.1.1.elements`, accessed via
`attach` so the choice `s.2` is evaluable) by its local choice, and partitions the components into the
three Finsets `leftComponents`/`rightComponents`/`forestComponents`.

Landed:

* `ResolvedCoassocSplitChoice.isLeftPrimitive` / `isRightPrimitive` / `isForestChoice` — the three
  local-choice predicates on an attached component;
* `ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice` — exhaustiveness;
* `ResolvedCoassocSplitChoice.leftComponents` / `rightComponents` / `forestComponents` — the three
  component Finsets (a `filter` of `s.1.1.elements.attach`);
* `ResolvedCoassocSplitChoice.components_union` — `left ∪ right ∪ forest = attach` (the partition covers);
* the three pairwise `Disjoint` lemmas (the partition is disjoint).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The right-survivor / remnant forests and the
concrete `fullQuotientOf` (5b-2…5b-4) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5b-1 — the left-primitive predicate.**  A component's local choice is `Sum.inl true`
(the `X γ ⊗ 1` term): it lands on the selected-outer side, not the quotient. -/
def ResolvedCoassocSplitChoice.isLeftPrimitive (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) : Prop :=
  s.choiceAt γ = Sum.inl true

/-- **R-6c-heart-5b-1 — the right-primitive predicate.**  A component's local choice is `Sum.inl false`
(the `1 ⊗ X γ` term): it is a quotient right-survivor. -/
def ResolvedCoassocSplitChoice.isRightPrimitive (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) : Prop :=
  s.choiceAt γ = Sum.inl false

/-- **R-6c-heart-5b-1 — the forest-choice predicate.**  A component's local choice is `Sum.inr B`
(a sub-forest of the component graph): it contributes a promoted piece (selected-outer) and a remnant
piece (quotient). -/
def ResolvedCoassocSplitChoice.isForestChoice (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) : Prop :=
  ∃ B, s.choiceAt γ = Sum.inr B

/-- **R-6c-heart-5b-1 — exhaustiveness.**  Every component is left-primitive, right-primitive, or a
forest choice (the local choice is `Sum.inl true`, `Sum.inl false`, or `Sum.inr B`). -/
theorem ResolvedCoassocSplitChoice.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) :
    s.isLeftPrimitive γ ∨ s.isRightPrimitive γ ∨ s.isForestChoice γ := by
  rcases hc : s.choiceAt γ with b | B
  · cases b
    · exact Or.inr (Or.inl hc)
    · exact Or.inl hc
  · exact Or.inr (Or.inr ⟨B, hc⟩)

/-- A left-primitive component is not right-primitive. -/
theorem ResolvedCoassocSplitChoice.not_isRightPrimitive_of_isLeftPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (h : s.isLeftPrimitive γ) : ¬ s.isRightPrimitive γ := by
  intro h'
  have := h.symm.trans h'
  simp at this

/-- A left-primitive component is not a forest choice. -/
theorem ResolvedCoassocSplitChoice.not_isForestChoice_of_isLeftPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (h : s.isLeftPrimitive γ) : ¬ s.isForestChoice γ := by
  rintro ⟨B, hB⟩
  have := h.symm.trans hB
  simp at this

/-- A right-primitive component is not a forest choice. -/
theorem ResolvedCoassocSplitChoice.not_isForestChoice_of_isRightPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (h : s.isRightPrimitive γ) : ¬ s.isForestChoice γ := by
  rintro ⟨B, hB⟩
  have := h.symm.trans hB
  simp at this

/-- **R-6c-heart-5b-1 — the left-primitive component Finset.**  The input outer components whose local
choice is `Sum.inl true` (the selected-outer left primitives). -/
noncomputable def ResolvedCoassocSplitChoice.leftComponents (s : ResolvedCoassocSplitChoice D G) :
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} :=
  s.1.1.elements.attach.filter s.isLeftPrimitive

/-- **R-6c-heart-5b-1 — the right-primitive component Finset.**  The input outer components whose local
choice is `Sum.inl false` (the quotient right-survivors). -/
noncomputable def ResolvedCoassocSplitChoice.rightComponents (s : ResolvedCoassocSplitChoice D G) :
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} :=
  s.1.1.elements.attach.filter s.isRightPrimitive

/-- **R-6c-heart-5b-1 — the forest-choice component Finset.**  The input outer components whose local
choice is `Sum.inr B` (the promoted/remnant contributors). -/
noncomputable def ResolvedCoassocSplitChoice.forestComponents (s : ResolvedCoassocSplitChoice D G) :
    Finset {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} :=
  s.1.1.elements.attach.filter s.isForestChoice

/-- **R-6c-heart-5b-1 — the partition covers.**  Every input outer component lands in exactly one of the
three Finsets: `left ∪ right ∪ forest = attach`. -/
theorem ResolvedCoassocSplitChoice.components_union (s : ResolvedCoassocSplitChoice D G) :
    s.leftComponents ∪ s.rightComponents ∪ s.forestComponents = s.1.1.elements.attach := by
  ext γ
  simp only [ResolvedCoassocSplitChoice.leftComponents, ResolvedCoassocSplitChoice.rightComponents,
    ResolvedCoassocSplitChoice.forestComponents, Finset.mem_union, Finset.mem_filter,
    Finset.mem_attach, true_and, iff_true]
  rcases s.isLeftPrimitive_or_isRightPrimitive_or_isForestChoice γ with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **R-6c-heart-5b-1 — left/right disjointness.** -/
theorem ResolvedCoassocSplitChoice.leftComponents_disjoint_rightComponents
    (s : ResolvedCoassocSplitChoice D G) : Disjoint s.leftComponents s.rightComponents := by
  rw [Finset.disjoint_left]
  intro γ hL hR
  simp only [ResolvedCoassocSplitChoice.leftComponents, ResolvedCoassocSplitChoice.rightComponents,
    Finset.mem_filter] at hL hR
  exact s.not_isRightPrimitive_of_isLeftPrimitive hL.2 hR.2

/-- **R-6c-heart-5b-1 — left/forest disjointness.** -/
theorem ResolvedCoassocSplitChoice.leftComponents_disjoint_forestComponents
    (s : ResolvedCoassocSplitChoice D G) : Disjoint s.leftComponents s.forestComponents := by
  rw [Finset.disjoint_left]
  intro γ hL hF
  simp only [ResolvedCoassocSplitChoice.leftComponents, ResolvedCoassocSplitChoice.forestComponents,
    Finset.mem_filter] at hL hF
  exact s.not_isForestChoice_of_isLeftPrimitive hL.2 hF.2

/-- **R-6c-heart-5b-1 — right/forest disjointness.** -/
theorem ResolvedCoassocSplitChoice.rightComponents_disjoint_forestComponents
    (s : ResolvedCoassocSplitChoice D G) : Disjoint s.rightComponents s.forestComponents := by
  rw [Finset.disjoint_left]
  intro γ hR hF
  simp only [ResolvedCoassocSplitChoice.rightComponents, ResolvedCoassocSplitChoice.forestComponents,
    Finset.mem_filter] at hR hF
  exact s.not_isForestChoice_of_isRightPrimitive hR.2 hF.2

end GaugeGeometry.QFT.Combinatorial
