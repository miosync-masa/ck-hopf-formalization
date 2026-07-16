import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRepresentedInQuotientConcrete

/-!
# R-6c-body-304 — left-residual sound/complete: directional audit + the `promoted_represented_value` residual (PROVED)

Three-hundred-and-fourth genuine-body step — a directional audit of the left-residual bridge (body-279/280
`left_sound_value` / `left_complete_value`) at the forward image, with the definitional `leftOf` case banked.  The two
directions are NOT a generic `¬forest-image ⇔ inl true` (false — `inl false` is also not a forest image); they need the
selected-outer membership context.  Splitting them:

## The two directions (code labels)

```text
left_sound_value    : leftSelectedConcrete q.1 γ → γ ∈ leftResidual (fwdMapFilteredValue F V q)
left_complete_value : γ ∈ leftResidual (fwdMapFilteredValue F V q) → leftSelectedConcrete q.1 γ
```
`leftResidual (fwd q) = (selectedOuterRawOf q.1).filterElements (¬ ∃δ, componentToForest (fwd q) δ = γ)`
(body-252 outer = `selectedOuterRawOf q.1`; body-303 predicate); and `selectedOuterRawOf q.1 = leftOf q.1 ∪ promotedOf q.1`
(body-289).

## `left_sound_value` — PROVABLE (leftOf + tag exclusivity + forest bridge)

`leftSelectedConcrete q.1 γ` (`choiceAt = inl true`) puts `γ ∈ leftOf q.1 ⊆ selectedOuterRawOf q.1`; and a forest image
`γ = componentToForest (fwd q) δ` would give `γ ∈ forestRecovered (fwd q)`, which the FOREST bridge (body-278) equates to
`forestChoiceSelected q.1 γ` (`choiceAt = inr B`) — contradicting `inl true ≠ inr B` (`not_leftSelectedConcrete_of_inr`).
Legitimate at `z = fwd q` (the actual domain, NOT the self-circular `recPre z`).

## `left_complete_value` — leftOf case DEFINITIONAL; promotedOf case → ONE leaf

`γ ∈ leftResidual (fwd q)` ⟹ `γ ∈ leftOf q.1 ∨ γ ∈ promotedOf q.1`:
* **`leftOf` case — DEFINITIONAL** (banked here: `leftSelectedConcrete_of_mem_leftOf`, the filter predicate IS
  `leftSelectedConcrete`).
* **`promotedOf` case** — `γ ∈ promotedOf q.1 ∧ ¬forest-image` must be impossible, i.e. the residual leaf:
  ```text
  promoted_represented_value : γ ∈ (promotedOf q.1).elements → ∃ δ, componentToForest (fwd q) δ = γ
  ```
  This is **NOT** dischargeable by `promote_collapse` alone: at the DOMAIN `q.1` the forest tag `B` is a genuine
  sub-forest (`(promote γ B).elements ≠ {γ}` in general), and tying the promoted / de-contracted components to the
  `componentToForest` parents needs the forest occurrence / component-map compatibility (body-176/188:
  "`promotedOf_recovered_eq` does NOT follow from tags — fielded"), i.e. the SAME geometry behind the forest bridge's
  `forest_sound_value` / `forest_complete_value`.

## Dependency judgment — REVERSE the order

Both left directions depend on the FOREST bridge (body-278): `left_sound_value` uses `forestRecovered_forward_value_
membership` to exclude the `inl true` component; `left_complete_value`'s `promoted_represented_value` IS the forest-image
side.  Neither touches the LEFT bridge (body-280) — no circularity.  Therefore the concrete FOREST (and right/survivor/
remnant) sound/complete directions must be discharged FIRST; `left_sound` / `left_complete` come after (consuming the
forest bridge + `promoted_represented_value`).

Per the HALT: only the definitional `leftOf` case is proved; `left_sound` / `left_complete` are reduced to (forest bridge
+ `promoted_represented_value`), not proved here; no generic `¬forest-image ⇔ inl true`; no `forward_outer_value` / whole
round-trip; the LEFT bridge is not used.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-304 — the `leftOf` case is definitional.**  A component of the concrete `leftOf` is left-selected — the
`leftOf` filter predicate IS `leftSelectedConcrete`. -/
theorem leftSelectedConcrete_of_mem_leftOf (q : ResolvedCoassocSplitChoice D G)
    (γ : ResolvedFeynmanSubgraph G)
    (h : γ ∈ ((resolvedConcreteForestPromoteSupply D G).leftOf q).elements) :
    ResolvedCoassocSplitChoice.leftSelectedConcrete q γ := by
  have hLe : ((resolvedConcreteForestPromoteSupply D G).leftOf q).elements
      = q.1.1.elements.filter (ResolvedCoassocSplitChoice.leftSelectedConcrete q) := rfl
  rw [hLe] at h
  exact (Finset.mem_filter.mp h).2

end GaugeGeometry.QFT.Combinatorial
