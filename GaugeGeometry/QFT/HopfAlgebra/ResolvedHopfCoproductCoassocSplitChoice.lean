import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGlobalCover

/-!
# R-6c-4f (part 1) — the resolved branch split-choice index + term (concrete)

Towards the global splitPhi cover `FL`, this fixes the **branch side concretely** (the part already
fully built in R-6c-3a): a *resolved split choice* is a pair `(input outer forest A, global component
choice p)`, and its **branch weight** is the associator applied to `(∏ component-choice terms) ⊗
rightTerm A` — exactly the global-choice summand from `coassocLeftTail_resolvedForestLeftTerm_choiceSum`
(R-6c-3a-3b).

This pins the resolved analogue of the flat `forestComponentSplitChoiceSigma` /
`forestComponentChoiceSigmaTerm` (the LEFT factor is the product over the chosen local terms, whose
left-selected part is the *selected* sub-forest — the deconcatenation that crosses outer forests).
The image side, the `resolvedSplitPhi` map, and the cover layer remain to be built (the genuine
de-contraction geometry); the **term agreement** `resolvedSplitPhi_*_term_eq` will relate
`resolvedSplitChoiceTerm` to the image weight along `resolvedSplitPhi`.

Landed:

* `ResolvedCoassocSplitChoice D G` — the branch index: `(A, p)` with `A` a carrier forest and `p` a
  global component choice (reusing the R-6c-3a `localChoiceCarrier` Pi);
* `ResolvedCoproductProperForestData.resolvedSplitChoiceTerm` — the branch weight in `ResolvedHopfH3`
  (the global-choice summand).

No facade, no flat term, no `forgetHopf`; the image/φ/cover are deferred.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- **R-6c-4f — the resolved branch split-choice index.**  A split choice is a carrier outer forest
`A` together with a global component choice `p` (each component picks a primitive leg or a sub-forest,
via the R-6c-3a `localChoiceCarrier`).  The resolved analogue of flat `forestComponentSplitChoiceSigma`. -/
def ResolvedCoassocSplitChoice (D : ResolvedCoproductProperForestData) (G : ResolvedFeynmanGraph) :
    Type :=
  Σ A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G},
    ∀ γ ∈ A.1.elements.attach, (Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx)

/-- **R-6c-4f — the resolved branch weight.**  The associator applied to `(∏ component-choice terms) ⊗
rightTerm A` — the global-choice summand of `coassocLeftTail_resolvedForestLeftTerm_choiceSum`.  The
resolved analogue of flat `forestComponentChoiceSigmaTerm`; its left factor's left-selected part is the
*selected* outer sub-forest. -/
noncomputable def ResolvedCoproductProperForestData.resolvedSplitChoiceTerm {G : ResolvedFeynmanGraph}
    (s : ResolvedCoassocSplitChoice D G) : ResolvedHopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
    ((∏ γ ∈ (s.1.1.elements.attach).attach,
        D.localChoiceTerm (γ.1.1.toResolvedFeynmanGraph) (componentCD s.1.1 γ.1) (s.2 γ.1 γ.2))
      ⊗ₜ[ℚ] (D.supply G).rightTerm s.1)

/-- The branch weight summed over all split choices of one outer forest `A` is the inner left tail of
that forest summand (`coassocLeftTail_resolvedForestLeftTerm_choiceSum`), repackaged with
`resolvedSplitChoiceTerm`. -/
theorem ResolvedCoproductProperForestData.coassocLeftTail_eq_splitChoiceTermSum
    {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A)
      = ∑ p ∈ (A.1.elements.attach).pi
            (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
          D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G) := by
  rw [show (D.supply G).leftTerm A = resolvedForestLeftTerm A.1 from rfl,
    D.coassocLeftTail_resolvedForestLeftTerm_choiceSum A.1 ((D.supply G).rightTerm A)]
  rfl

end GaugeGeometry.QFT.Combinatorial
