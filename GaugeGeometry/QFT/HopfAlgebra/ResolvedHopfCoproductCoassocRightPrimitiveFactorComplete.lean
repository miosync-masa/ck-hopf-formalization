import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocDoubleAttachReindex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedOf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-body-120 — right-primitive factor: the SOURCE side proved (mirror), the quotient transport isolated

Hundred-and-twentieth genuine-body step, the second factor product `right_primitive_factor`.  The mirror of
body-119 goes through cleanly on the SOURCE side: `∏_{¬isRight} localRightFactor = leftTerm(source
right-primitive forest)` is PROVED by the same five-move template.  But the assembly's `right_primitive_factor`
wants `leftTerm(rightSurvivor)` with `rightSurvivor` a forest of the QUOTIENT graph — so the remaining content is
exactly the source↔quotient SURVIVOR TRANSPORT (`leftTerm(sourceRightPrim) = leftTerm(rightSurvivor)`), the leaf
the mismatch predicts.

## The source-side result (PROVED, mirror of body-119)

`right_primitive_factor_source`: with `rightPrimSelected q γ := ∃ hγ, choiceAt q ⟨γ, hγ⟩ = Sum.inl false` (the
right-primitive components) and `sourceRightPrim q := q.1.1.filterElements (rightPrimSelected q)`,

```text
∏_{γ : ¬(p γ).isRight} localRightFactor(p γ) = leftTerm(sourceRightPrim q)
```

by the SAME five moves as `left_primitive_factor` — only mirrored: the drop-out keeps the `inl false` (right
primitives, `localRightFactor(inl false) = X`) and drops the `inl true` (`localRightFactor(inl true) = 1`), then
the double-`attach` reindex (body-118) gives the product over `sourceRightPrim`'s components.

## The isolated transport (the mismatch leaf)

`localRightFactor(inl false) = X(source component gen)` lives in `G`; `leftTerm(rightSurvivor)` lives in the
QUOTIENT graph `A_target.contractWithStars`.  A right-survivor component is a source right-primitive component
that survives the contraction UNCHANGED (it is disjoint from the contracted left/promoted forests), so its class
— and hence its generator — is preserved.  The remaining obligation is therefore

```text
leftTerm(sourceRightPrim q) = leftTerm(rightSurvivor q)
```

— the survival transport (source right-primitive forest ≅ its image in the quotient, with generators preserved).
This is genuinely NOT a same-graph mirror; it is the first place the source/quotient distinction bites, and it is
isolated as the leaf `right_survivor_transport`.  (The assembly's `right_primitive_factor` = the source result
above, composed with this transport.)

Per the HALT: the source-side right-primitive factor is PROVED (mirror); the quotient survival transport is
isolated as the exact remaining leaf; the remnant / promoted products are not entered.

Landed:

* `rightPrimSelected` / `rightPrimSelected_iff_choice` — the right-primitive selection predicate + its
  choice equivalence (PROVED);
* `right_primitive_factor_source` — `∏_{¬isRight} localRightFactor = leftTerm(sourceRightPrim)` (PROVED, mirror
  of body-119); the assembly's `right_primitive_factor` reduces to this + the survival transport.

Toolkit body (like body-119), no new supply.  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-120 — the right-primitive selection predicate.**  A component is right-primitive when its choice
is `Sum.inl false`. -/
def rightPrimSelected (q : ResolvedCoassocSplitChoice D G) (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ hγ : γ ∈ q.1.1.elements, ResolvedCoassocSplitChoice.choiceAt q ⟨γ, hγ⟩ = Sum.inl false

/-- **R-6c-body-120 — the right-primitive selection↔choice equivalence.** -/
theorem rightPrimSelected_iff_choice (q : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ q.1.1.elements} // x ∈ q.1.1.elements.attach}) :
    rightPrimSelected q γ.1.1 ↔ q.2 γ.1 γ.2 = Sum.inl false := by
  simp only [rightPrimSelected, ResolvedCoassocSplitChoice.choiceAt]
  exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨γ.1.2, he⟩⟩

/-- **R-6c-body-120 — the SOURCE-side right-primitive factor** (PROVED, mirror of body-119).  `∏_{¬isRight}
localRightFactor = leftTerm(source right-primitive forest)`.  The assembly's `right_primitive_factor` is this
composed with the source↔quotient survival transport. -/
theorem right_primitive_factor_source (q : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (q.1.1.filterElements (fun γ => rightPrimSelected q γ)) := by
  have hsub : (q.1.1.elements.attach).attach.filter (fun γ => rightPrimSelected q γ.1.1)
      ⊆ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight) := by
    intro γ hγ
    rw [Finset.mem_filter] at hγ ⊢
    refine ⟨hγ.1, ?_⟩
    rw [(rightPrimSelected_iff_choice q γ).mp hγ.2]; simp [Sum.isRight]
  rw [← Finset.prod_subset hsub (fun γ hγ hγ' => by
    rw [Finset.mem_filter] at hγ hγ'
    have hnr : ¬ (q.2 γ.1 γ.2).isRight := hγ.2
    have hnf : q.2 γ.1 γ.2 ≠ Sum.inl false := fun he =>
      hγ' ⟨Finset.mem_attach _ _, (rightPrimSelected_iff_choice q γ).mpr he⟩
    obtain ⟨b, hb⟩ : ∃ b, q.2 γ.1 γ.2 = Sum.inl b := by
      cases hc : q.2 γ.1 γ.2 with
      | inl b => exact ⟨b, rfl⟩
      | inr B => simp [hc, Sum.isRight] at hnr
    rw [hb] at hnf ⊢; cases b with
    | false => exact absurd rfl hnf
    | true => rfl)]
  rw [Finset.prod_congr rfl (fun γ hγ =>
    show localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2)
        = MvPolynomial.X ((γ.1.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD q.1.1 γ.1))
      from by rw [(rightPrimSelected_iff_choice q γ).mp (Finset.mem_filter.mp hγ).2]; rfl)]
  exact prod_double_attach_filter_reindex q.1.1.elements
    (fun γ => rightPrimSelected q γ)
    (fun β => MvPolynomial.X ((β.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD q.1.1 β)))

end GaugeGeometry.QFT.Combinatorial
