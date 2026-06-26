import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPartition

/-!
# R-6c-heart-5c-1f — `rightFactorProduct` partition split

The right-factor analogue of 5c-1c.  `rightFactorProduct s = ∏ γ, localChoiceRightFactor γ (choiceAt γ)`
splits over the component partition (`leftComponents ∪ rightComponents ∪ forestComponents`):

* `Sum.inl true`  → right factor `1`     (left primitive — drops out);
* `Sum.inl false` → right factor `X γ`   (right primitive — a quotient right-survivor);
* `Sum.inr B`     → right factor `rightTerm B` (forest choice — a quotient remnant).

This file delivers the split and the easy left region (`= 1`), so

  `rightFactorProduct s = (∏ rightComponents) * (∏ forestComponents)`,

mirroring `leftFactorProduct_eq_leftOf_mul_forestPart`.  The two remaining regions identify with the
quotient forest `RightSurvivors ⊔ Remnants` — but those forests live over the *contract* graph via the
**supply** survivor/remnant embeddings, so connecting them needs the embedding generator equalities
(`rightSurvivorGen_eq` / `remnantGen_eq`), deferred to the next step.

Landed:

* `rightFactorOf` — the per-component right factor (single `attach`, via `choiceAt`);
* `rightFactorProduct_eq` — `rightFactorProduct s = ∏ γ ∈ attach, rightFactorOf s γ`;
* `rightFactorProduct_split` — splits over the three partition regions;
* `rightFactorProduct_left_eq_one` — the left-primitive region contributes `1`;
* `rightFactorProduct_eq_rightPart_mul_forestPart` —
  `rightFactorProduct s = (∏ rightComponents, rightFactorOf) * (∏ forestComponents, rightFactorOf)`.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The survivor/remnant generator equalities and the
quotient-forest assembly are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1f — the per-component right factor.**  The local-choice right factor at a component
`γ`, indexed over the single `attach` via `choiceAt`. -/
noncomputable def ResolvedCoproductProperForestData.rightFactorOf
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}) : ResolvedHopfH :=
  D.localChoiceRightFactor (γ.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ) (s.choiceAt γ)

/-- **R-6c-heart-5c-1f — `rightFactorProduct` over the single `attach`.** -/
theorem ResolvedCoproductProperForestData.rightFactorProduct_eq
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.rightFactorProduct s = ∏ γ ∈ s.1.1.elements.attach, D.rightFactorOf s γ := by
  unfold ResolvedCoproductProperForestData.rightFactorProduct
  rw [← Finset.prod_attach (s.1.1.elements.attach) (D.rightFactorOf s)]
  rfl

/-- **R-6c-heart-5c-1f — the partition split of `rightFactorProduct`.** -/
theorem ResolvedCoproductProperForestData.rightFactorProduct_split
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.rightFactorProduct s
      = (∏ γ ∈ s.leftComponents, D.rightFactorOf s γ)
        * (∏ γ ∈ s.rightComponents, D.rightFactorOf s γ)
        * (∏ γ ∈ s.forestComponents, D.rightFactorOf s γ) := by
  rw [D.rightFactorProduct_eq, ← s.components_union,
    Finset.prod_union (Finset.disjoint_union_left.mpr
      ⟨s.leftComponents_disjoint_forestComponents, s.rightComponents_disjoint_forestComponents⟩),
    Finset.prod_union s.leftComponents_disjoint_rightComponents]

/-- **R-6c-heart-5c-1f — the left-primitive region contributes `1`.**  A left-primitive component has
`choiceAt = Sum.inl true`, whose right factor is `1`. -/
theorem ResolvedCoproductProperForestData.rightFactorProduct_left_eq_one
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ s.leftComponents, D.rightFactorOf s γ) = 1 := by
  classical
  apply Finset.prod_eq_one
  intro γ hγ
  have hl : s.choiceAt γ = Sum.inl true := (Finset.mem_filter.mp hγ).2
  unfold ResolvedCoproductProperForestData.rightFactorOf
  rw [hl]
  rfl

/-- **R-6c-heart-5c-1f — `rightFactorProduct` is the right-survivor ⊗ remnant region product.**
`rightFactorProduct s = (∏ rightComponents, rightFactorOf) * (∏ forestComponents, rightFactorOf)` — the
left region drops out (`= 1`). -/
theorem ResolvedCoproductProperForestData.rightFactorProduct_eq_rightPart_mul_forestPart
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) :
    D.rightFactorProduct s
      = (∏ γ ∈ s.rightComponents, D.rightFactorOf s γ)
        * (∏ γ ∈ s.forestComponents, D.rightFactorOf s γ) := by
  rw [D.rightFactorProduct_split, D.rightFactorProduct_left_eq_one, one_mul]

end GaugeGeometry.QFT.Combinatorial
