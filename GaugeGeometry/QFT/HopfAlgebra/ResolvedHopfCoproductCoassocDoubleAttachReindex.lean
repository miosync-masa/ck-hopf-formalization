import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactor

/-!
# R-6c-body-118 — double-attach product reindex: the shared reindex machinery for all four factor products

Hundred-and-eighteenth genuine-body step, landing the generic `Finset`-product reindex common to all four
remaining factor products (body-117): a product over the FILTERED double-`attach`
`(s.attach).attach.filter (P ∘ ·)` reindexes to a product over the single `attach` of the FILTERED set
`(s.filter P).attach`.  This is the map's per-component correspondence stripped of all geometry — pure `Finset`
combinatorics, proved once and reusable four times.

## The generic reindex (PROVED)

`prod_double_attach_filter_reindex`: for a `CommMonoid M`, a `Finset s`, a decidable predicate `P`, and a
membership-dependent `f`,

```text
∏ γ ∈ (s.attach).attach.filter (fun γ => P γ.1.1), f γ.1
  = ∏ β ∈ (s.filter P).attach, f ⟨β.1, mem_of_mem_filter …⟩
```

by `Finset.prod_bij'` with the bijection `γ ↦ ⟨γ.1.1, …⟩` / `β ↦ ⟨⟨β.1, …⟩, mem_attach⟩` (both directions are
`rfl` on the value; the membership facts are `mem_filter` / `mem_attach`).  The dependent `f : {x // x ∈ s} → M`
lets the summand carry the component's connected-divergence witness — the two witnesses (from the double-`attach`
side and the `filter`-attach side) are proof-irrelevant, so `f` agrees.

## How it discharges the factor-product reindex

For `left_primitive_factor` (body-117), after the right-primitive drop-out (`resolved_prod_bif_eq_filter`,
body-103) the LHS is `∏` over `(A'.elements.attach).attach.filter (choice · = inl true)` of `X(component gen)`,
and `resolved_leftOf_elements_eq` gives `(leftOf).elements = A'.elements.filter (leftSelectedConcrete)`; so with
`s = A'.elements`, `P = leftSelectedConcrete`, `f β = X(component gen of β)`, this lemma reindexes the LHS to `∏`
over `(leftOf).elements.attach` of `X(component gen)` `= leftTerm(leftOf)` (`resolved_leftTerm_eq_prod`,
body-103).  The SAME lemma serves `promoted_factor` / `right_primitive_factor` / `remnant_factor` — only the
predicate `P` and the summand `f` change.

Per the HALT: the generic reindex lemma is landed; the four factor products are NOT proved in full (they still
need their component-set correspondence + the summand identification); no sector forward map is constructed.

Landed:

* `prod_double_attach_filter_reindex` — the shared double-`attach` filtered-product reindex (PROVED, generic).

Toolkit body (like body-103/108/117), no new supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-- **R-6c-body-118 — the double-`attach` filtered-product reindex.**  A product over the `P`-filtered double
`attach` of `s` equals the product over the single `attach` of the `P`-filtered `s`.  The shared reindex behind
all four factor products (`left_primitive` / `promoted` / `right_primitive` / `remnant`). -/
theorem prod_double_attach_filter_reindex {α M : Type*} [CommMonoid M] (s : Finset α)
    (P : α → Prop) [DecidablePred P] (f : {x // x ∈ s} → M) :
    (∏ γ ∈ (s.attach).attach.filter (fun γ => P γ.1.1), f γ.1)
      = ∏ β ∈ (s.filter P).attach, f ⟨β.1, Finset.mem_of_mem_filter β.1 β.2⟩ := by
  apply Finset.prod_bij'
    (i := fun γ hγ => (⟨γ.1.1, Finset.mem_filter.mpr ⟨γ.1.2, (Finset.mem_filter.mp hγ).2⟩⟩ :
        {x // x ∈ s.filter P}))
    (j := fun β hβ => (⟨⟨β.1, Finset.mem_of_mem_filter β.1 β.2⟩, Finset.mem_attach _ _⟩ :
        {y // y ∈ s.attach}))
    (hi := fun γ hγ => Finset.mem_attach _ _)
    (hj := fun β hβ => Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, (Finset.mem_filter.mp β.2).2⟩)
    (left_inv := fun γ hγ => Subtype.ext (Subtype.ext rfl))
    (right_inv := fun β hβ => Subtype.ext rfl)
    (h := fun γ hγ => rfl)

end GaugeGeometry.QFT.Combinatorial
