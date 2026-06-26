import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFactorGen
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestRegion

/-!
# R-6c-heart-5c-1i — assemble `product_eq` from the factor pieces

`product_eq = leftFactor ⊗ rightFactor` (5c-1), with both factors now structurally complete:

* left factor `leftFactorProduct s = resolvedForestLeftTerm (selectedOuterRaw s)` (5c-1e, given
  `hPD`/`hLP`);
* right factor `rightFactorProduct s = resolvedForestLeftTerm (remnantForest ⊔ rightSurvivorForest)`
  (5c-1g/1h, given the survivor/remnant generator equalities + injectivities + disjointness).

This file feeds both into `product_eq_of_factors`, closing `product_eq` **conditionally** on the
remaining parametric supply hypotheses (the de-contraction geometry that the parametric carrier and the
abstract survivor/remnant embeddings do not pin down).  The two connector hypotheses `hSel`/`hQuot`
identify the abstract image's `selectedOuter`/`quotientForest` projections with the concrete forests.

Landed:

* `product_eq_of_region_data` — `product_eq` from all the region/supply hypotheses.

No facade, no flat term, no `forgetHopf`, no rep/perm.  `right_eq` (5c-2) and discharging the supply
hypotheses are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1i — `product_eq` from the region/supply data.**  Assembles the product
factorization from the left factor equality (5c-1e), the right factor equality (5c-1g/1h), and the two
connectors identifying the abstract image's projections with the concrete forests.  All remaining
obligations are the parametric supply hypotheses (forest/union disjointness `hPD`/`hLP`, survivor/remnant
generator equalities + injectivities, remnant/survivor disjointness, and the connectors). -/
theorem product_eq_of_region_data
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G)
    (hPD : (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements})
      |>.PairwiseDisjoint s.promotedComponentElements)
    (hLP : Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
      ((resolvedPromotedOfSupply D G).promotedOf s).elements)
    (survivorInj : ∀ γ₁ ∈ s.rightComponents.attach, ∀ γ₂ ∈ s.rightComponents.attach,
      R.survivorComponent s γ₁ = R.survivorComponent s γ₂ → γ₁ = γ₂)
    (survivorGen : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} //
        x ∈ s.rightComponents},
      resolvedComponentGenTerm (R.survivorComponent s γ) = resolvedComponentGenTerm γ.1.1)
    (remnantInj : ∀ γ₁ ∈ s.forestComponents.attach, ∀ γ₂ ∈ s.forestComponents.attach,
      M.remnantComponent s (s.forestComponentOccurrence γ₁)
        = M.remnantComponent s (s.forestComponentOccurrence γ₂) → γ₁ = γ₂)
    (remnantGen : ∀ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} //
        x ∈ s.forestComponents},
      resolvedComponentGenTerm (M.remnantComponent s (s.forestComponentOccurrence γ))
        = D.rightFactorOf s γ.1)
    (hCross : ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
      γ ≠ δ → γ.Disjoint δ)
    (hDisj : Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements)
    (hSel : resolvedSelectedOuterTerm (imageOf s)
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s))
    (hQuot : resolvedForestLeftTerm ((M.remnantForest s).union (R.rightSurvivorForest s) hCross)
      = resolvedForestLeftTerm (imageOf s).quotientForest) :
    D.resolvedSplitChoiceProduct s
      = resolvedSelectedOuterTerm (imageOf s) ⊗ₜ[ℚ] resolvedForestLeftTerm (imageOf s).quotientForest :=
  D.product_eq_of_factors s
    ((leftFactorProduct_eq_selectedOuterRawTerm s hPD hLP).trans hSel.symm)
    ((D.rightFactorProduct_eq_quotientForestTerm R M s
        (rightSurvivor_region_eq R s survivorInj survivorGen)
        (remnant_region_eq M s remnantInj remnantGen) hCross hDisj).trans hQuot)

end GaugeGeometry.QFT.Combinatorial
