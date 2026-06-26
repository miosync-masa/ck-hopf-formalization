import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFactorAssembly

/-!
# R-6c-heart-5c-1h — survivor / remnant generator equalities (hRight / hForest)

The right factor assembly (5c-1g) left two region equalities as hypotheses:

* `hRight`  : `∏ γ ∈ rightComponents, rightFactorOf s γ = resolvedForestLeftTerm (rightSurvivorForest s)`;
* `hForest` : `∏ γ ∈ forestComponents, rightFactorOf s γ = resolvedForestLeftTerm (remnantForest s)`.

This file reduces each to the **pointwise generator equality** of the corresponding supply embedding,
via a `prod_image` bijection over the survivor / remnant forest elements:

* `rightSurvivor_region_eq` — from `survivorGen` (`componentGenTerm (survivorComponent γ) =
  componentGenTerm γ.1.1`: the survivor is the same component living in the quotient graph) plus the
  embedding's injectivity;
* `remnant_region_eq` — from `remnantGen` (`componentGenTerm (remnantComponent (occ γ)) = rightFactorOf
  s γ.1`, i.e. `= rightTerm Bγ`: the de-contraction remnant) plus injectivity.

Both pointwise facts are properties of the **abstract supply** embeddings (the genuine de-contraction
geometry), so — per the HALT — they are taken as hypotheses; the bijection algebra is proved.  Feeding
the results into `rightFactorProduct_eq_quotientForestTerm` (5c-1g) then needs only those gen equalities.

Landed:

* `rightFactorOf_eq_genTerm_of_isRightPrimitive` — a right-primitive component's right factor is its
  generator term;
* `rightSurvivor_region_eq` / `remnant_region_eq` — the two region equalities from the pointwise gen
  equalities + injectivity.

No facade, no flat term, no `forgetHopf`, no rep/perm.  The pointwise gen equalities (survivor/remnant
embeddings) and `right_eq` remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1h — a right-primitive component's right factor is its generator term.**  Its choice
is `Sum.inl false`, whose right factor is `X (componentGen γ)`. -/
theorem rightFactorOf_eq_genTerm_of_isRightPrimitive
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    (h : s.isRightPrimitive γ) : D.rightFactorOf s γ = resolvedComponentGenTerm γ.1 := by
  have hc : s.choiceAt γ = Sum.inl false := h
  have hcd : γ.1.forget.IsConnectedDivergent := s.1.1.isConnectedDivergent γ.1 γ.2
  unfold ResolvedCoproductProperForestData.rightFactorOf
    ResolvedCoproductProperForestData.localChoiceRightFactor resolvedComponentGenTerm
  rw [hc, dif_pos hcd]
  rfl

/-- **R-6c-heart-5c-1h — the right-survivor region equality from the survivor gen equality.**  Given the
survivor embedding's generator equality (`survivorGen`) and injectivity (`hInj`), the right-primitive
region is the right-survivor forest term. -/
theorem rightSurvivor_region_eq (R : ResolvedRightSurvivorSupply D G)
    (s : ResolvedCoassocSplitChoice D G)
    (hInj : ∀ γ₁ ∈ s.rightComponents.attach, ∀ γ₂ ∈ s.rightComponents.attach,
        R.survivorComponent s γ₁ = R.survivorComponent s γ₂ → γ₁ = γ₂)
    (survivorGen : ∀ γ : {x : _ // x ∈ s.rightComponents},
        resolvedComponentGenTerm (R.survivorComponent s γ) = resolvedComponentGenTerm γ.1.1) :
    (∏ γ ∈ s.rightComponents, D.rightFactorOf s γ)
      = resolvedForestLeftTerm (R.rightSurvivorForest s) := by
  classical
  symm
  rw [resolvedForestLeftTerm_eq_prod, ResolvedRightSurvivorSupply.rightSurvivorForest_elements,
    Finset.prod_image hInj, Finset.prod_congr rfl (fun γ _ => survivorGen γ),
    Finset.prod_attach s.rightComponents (fun δ => resolvedComponentGenTerm δ.1)]
  apply Finset.prod_congr rfl
  intro γ hγ
  exact (rightFactorOf_eq_genTerm_of_isRightPrimitive (Finset.mem_filter.mp hγ).2).symm

/-- **R-6c-heart-5c-1h — the remnant region equality from the remnant gen equality.**  Given the remnant
embedding's generator equality (`remnantGen`: the de-contraction remnant's term is the forest choice's
`rightTerm`) and injectivity (`hInj`), the forest region is the remnant forest term. -/
theorem remnant_region_eq (M : ResolvedRemnantComponentSupply D G)
    (s : ResolvedCoassocSplitChoice D G)
    (hInj : ∀ γ₁ ∈ s.forestComponents.attach, ∀ γ₂ ∈ s.forestComponents.attach,
        M.remnantComponent s (s.forestComponentOccurrence γ₁)
          = M.remnantComponent s (s.forestComponentOccurrence γ₂) → γ₁ = γ₂)
    (remnantGen : ∀ γ : {x : _ // x ∈ s.forestComponents},
        resolvedComponentGenTerm (M.remnantComponent s (s.forestComponentOccurrence γ))
          = D.rightFactorOf s γ.1) :
    (∏ γ ∈ s.forestComponents, D.rightFactorOf s γ)
      = resolvedForestLeftTerm (M.remnantForest s) := by
  classical
  symm
  rw [resolvedForestLeftTerm_eq_prod, ResolvedRemnantComponentSupply.remnantForest_elements,
    Finset.prod_image hInj, Finset.prod_congr rfl (fun γ _ => remnantGen γ),
    Finset.prod_attach s.forestComponents (fun δ => D.rightFactorOf s δ)]

end GaugeGeometry.QFT.Combinatorial
