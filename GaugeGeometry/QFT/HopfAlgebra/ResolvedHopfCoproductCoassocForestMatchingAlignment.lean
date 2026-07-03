import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchReindexCorrection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputTailsOnlyCapstone
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightInner
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBoundaryTailStep

/-!
# R-6c-body-91 — forest_matching alignment: the two expansion endpoints + the (A,p) ↔ (A,B) bijection

Ninety-first genuine-body step, aligning `forest_matching` (body-90's single coassoc leaf) with the flat
nested-forest `Finset.sum_bij`.  Both expansion ENDPOINTS are proved here (the image and branch sides in their
concrete index forms), reducing `forest_matching` to the concrete bijection `(A, component choice) ↔ (A,
quotient sub-forest)`.

## The two expansion endpoints (PROVED)

At every representative `G`:

* IMAGE — `resolved_regroupImage_quotient_form`:
  `regroupImageSum (G.gen) = 1 ⊗ forestSum G + ∑_A leftTerm A ⊗ Δᵣ(rightTerm A)`
  (via `regroupImageSum_eq_outerSum` + `outer_image_boundary_tail_split` + `coassocRightTail_tmul`).  This is
  the resolved flat `forestTermE2 + forestTermF` (image boundary `1 ⊗ forestSum` + `∑_A A ⊗ Δ([Γ/A])`);
* BRANCH — `resolved_regroupBranch_splitChoice_form`:
  `regroupBranchSum (G.gen) = assoc(forestSum G ⊗ 1) + ∑_A ∑_{p ∈ piCarrier A} resolvedSplitChoiceTerm ⟨A, p⟩`
  (via `resolved_regroupBranchSum_boundary_tail` + `coassocLeftTail_eq_splitChoiceTermSum`).  This is the
  resolved flat `forestTermC + forestTermE` (branch boundary `assoc(forestSum ⊗ 1)` + `∑_A assoc(Δ(A) ⊗ [Γ/A])`
  in component-choice form).

So `forest_matching` (`regroupImageSum = regroupBranchSum`) is EXACTLY the equality of these two forms.

## The alignment table (flat ↔ resolved)

| flat (`Coassoc`) | resolved |
|---|---|
| `forestTermF = ∑_A A ⊗ Δ([Γ/A])` | `∑_A leftTerm A ⊗ Δᵣ(rightTerm A)` (`coproduct_rightTerm`: `Δᵣ(rightTerm A) = primitive + ∑_B leftTerm B ⊗ rightTerm B`) |
| `forestTermE = ∑_A assoc(Δ(A) ⊗ [Γ/A])` | `∑_A ∑_{p ∈ piCarrier A} splitTerm ⟨A, p⟩` (component choices `p`) |
| image boundary `forestTermE2 = 1 ⊗ forestSum` | `1 ⊗ forestSum G` |
| branch boundary `forestTermC = assoc(forestSum ⊗ 1)` | `assoc(forestSum G ⊗ 1)` |
| RHS index: quotient-forest pair `(A, B)` | `(A, B)` — `A ∈ carrier`, `B` a sub-forest of `A.contractWithStars` |
| LHS index: component choice `(A, p)` | `(A, p)` — `p ∈ (A.elements.attach).pi localChoiceCarrier` |
| core `sum_bij` `forestComponentChoiceSigmaTerm ↔ quotientForestSigmaTerm` | the `(A, p) ↔ (A, B)` matching + summand agreement |

## The remaining leaf

`ResolvedForestMatchingAlignmentSupply.aligned_matching` fields the equality of the two proved forms at each
representative — i.e. the concrete nested-forest matching `1 ⊗ forestSum + ∑_A leftTerm A ⊗ Δᵣ(rightTerm A) =
assoc(forestSum ⊗ 1) + ∑_A ∑_p splitTerm ⟨A, p⟩`.  With a representative lift, `forest_matching` follows (via the
two proved endpoints), then `coassoc_gen` (body-90/88).  So the single deep leaf is now this concrete `(A, p) ↔
(A, B)` bijection + summand agreement — the flat `…_of_factorization` `sum_bij` to be ported.

Per the HALT: the `sum_bij` is NOT proved (it is `aligned_matching`); the two expansion endpoints ARE proved;
the flat↔resolved alignment is fixed; no flat `HopfH` transport, no star-allocation detail.

Landed:

* `resolved_regroupImage_quotient_form` / `resolved_regroupBranch_splitChoice_form` — the two endpoints (PROVED);
* `ResolvedForestMatchingAlignmentSupply D` — the aligned matching + representative lift;
* `.forest_matching` / `.coassoc_gen` — via the endpoints, to body-90/88.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-91 — the IMAGE expansion endpoint** (quotient-forest form).  `regroupImageSum (G.gen) =
1 ⊗ forestSum + ∑_A leftTerm A ⊗ Δᵣ(rightTerm A)` — the resolved flat `forestTermE2 + forestTermF`. -/
theorem resolved_regroupImage_quotient_form (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupImageSum (G.toResolvedHopfGen hCD)
      = (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A) := by
  rw [D.regroupImageSum_eq_outerSum G hCD, outer_image_boundary_tail_split]
  exact congrArg (_ + ·) (Finset.sum_congr rfl (fun A _ => D.coassocRightTail_tmul _ _))

/-- **R-6c-body-91 — the BRANCH expansion endpoint** (component-choice form).  `regroupBranchSum (G.gen) =
assoc(forestSum ⊗ 1) + ∑_A ∑_p splitTerm ⟨A, p⟩` — the resolved flat `forestTermC + forestTermE`. -/
theorem resolved_regroupBranch_splitChoice_form (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.regroupBranchSum (G.toResolvedHopfGen hCD)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ A ∈ (D.supply G).forestCarrier,
            ∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
              D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G) := by
  rw [resolved_regroupBranchSum_boundary_tail hCD]
  exact congrArg (_ + ·) (Finset.sum_congr rfl (fun A _ => D.coassocLeftTail_eq_splitChoiceTermSum A))

/-- **R-6c-body-91 — the forest-matching alignment supply.**  The concrete nested-forest matching (image
quotient-forest form = branch component-choice form) at each representative, plus a representative lift.  The
single deep leaf: the `(A, p) ↔ (A, B)` `sum_bij` + summand agreement. -/
structure ResolvedForestMatchingAlignmentSupply (D : ResolvedCoproductProperForestData) where
  /-- The nested-forest matching: image quotient-forest form = branch component-choice form. -/
  aligned_matching : ∀ (G : ResolvedFeynmanGraph),
    (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
            ((D.supply G).sum ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + ∑ A ∈ (D.supply G).forestCarrier,
            ∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
              D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-91 — `forest_matching` from the aligned matching** (via the two proved endpoints). -/
def ResolvedForestMatchingAlignmentSupply.toForestMatchingSupply
    (S : ResolvedForestMatchingAlignmentSupply D) : ResolvedForestMatchingSupply D where
  forest_matching := by
    intro x
    rw [S.rep_gen x, resolved_regroupImage_quotient_form (S.repCD x),
      resolved_regroupBranch_splitChoice_form (S.repCD x)]
    exact S.aligned_matching (S.rep x)

/-- **R-6c-body-91 — `coassoc_gen` from the aligned matching** (via body-90/88). -/
theorem ResolvedForestMatchingAlignmentSupply.coassoc_gen
    (S : ResolvedForestMatchingAlignmentSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestMatchingSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
