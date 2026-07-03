import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlignedMatchingBijection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOutputBoundaryCovers
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageCoverBody

/-!
# R-6c-body-93 — nested_matching sum-bij scaffold: primitives peeled off, only the forest core remains

Ninety-third genuine-body step, splitting `nested_matching` (body-92's single deep leaf) into its PRIMITIVE part
(now PROVED, no bijection) and a clean forest CORE (the genuine nested-forest `Finset.sum_bij`).  The two global
boundaries and the whole primitive `X ⊗ 1 + 1 ⊗ X` disappear into split-choice vocabulary via body-70 and two
one-line term identities; what remains is a boundary-free equation between the three pure-primitive/forest
component classes and the full component-choice sum.

## The primitive term (PROVED)

`resolved_allLeftPrimitive_splitTerm` — the sibling of body-65's all-RIGHT lemma, for the all-LEFT choice
`p_L = fun _ _ => Sum.inl true`:

```text
splitTerm ⟨A, p_L⟩ = leftTerm A ⊗ (1 ⊗ rightTerm A)
```

(via `∏ (X ⊗ 1) = leftTerm A ⊗ 1` with `includeLeft` + `assoc_tmul`).  Together with body-65's all-RIGHT
`splitTerm ⟨A, p_R⟩ = 1 ⊗ (leftTerm A ⊗ rightTerm A)` these are the two pure primitives.

## The reshuffle (the four boundary/primitive identities)

`rightTerm A = X(quotGen A)`, so `leftTerm A ⊗ primitive(quotGen A) = leftTerm A ⊗ (rightTerm A ⊗ 1) +
leftTerm A ⊗ (1 ⊗ rightTerm A)`.  The four global pieces then match up:

| `nested_matching` piece | becomes | by |
|---|---|---|
| image boundary `1 ⊗ forestSum` | `∑_A splitTerm ⟨A, p_R⟩` | `resolved_image_boundary_eq_allRightPrimitive_sum` (body-70) |
| branch boundary `assoc(forestSum ⊗ 1)` | `∑_A leftTerm A ⊗ (rightTerm A ⊗ 1)` | `resolved_branch_boundary_eq_primitive_outer` (body-70) |
| primitive `X ⊗ 1` leg `leftTerm A ⊗ (rightTerm A ⊗ 1)` | cancels the branch boundary | `abel` |
| primitive `1 ⊗ X` leg `leftTerm A ⊗ (1 ⊗ rightTerm A)` | `splitTerm ⟨A, p_L⟩` | `resolved_allLeftPrimitive_splitTerm` |

So the `X ⊗ 1` primitive leg IS the branch boundary (they cancel), the `1 ⊗ X` leg IS the all-left split term,
and the image boundary IS the all-right split term.  Everything primitive/boundary is discharged.

## The remaining core (the genuine bijection)

What survives is boundary-free:

```text
∑_A splitTerm ⟨A, p_R⟩ + ∑_A splitTerm ⟨A, p_L⟩
  + ∑_A ∑_{B ∈ quotCarrier A} leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)
    = ∑_A ∑_{p ∈ piCarrier A} splitTerm ⟨A, p⟩
```

`ResolvedNestedForestCoreSupply.forest_core` fields exactly this — the pure nested-forest `Finset.sum_bij`
between the two pure-primitive choices `{p_R, p_L}` plus the forest-carrying choices (matched to quotient
forests `B`) and the full component-choice sum.  `.toNestedForestBijectionSupply` discharges the primitives and
boundaries (the reduction above) to recover body-92's `nested_matching`; `.coassoc_gen` chains body-92/91/90/88.

Per the HALT: the forest `sum_bij` is NOT proved (it is `forest_core`); the primitive term IS proved
(`resolved_allLeftPrimitive_splitTerm`); the boundary/primitive reshuffle is fixed (body-70 + two term
identities); no full quotient-forest union construction, no star/retarget detail.

Landed:

* `resolved_allLeftPrimitive_splitTerm` — the all-left primitive split term (PROVED);
* `resolved_image_primitive_split` — `leftTerm A ⊗ primitive = leftTerm A ⊗ (rightTerm A ⊗ 1) + splitTerm ⟨A,
  p_L⟩` (PROVED);
* `ResolvedNestedForestCoreSupply D` — the boundary-free forest core + representative lift;
* `.toNestedForestBijectionSupply` / `.coassoc_gen` — to body-92/91/90/88.

No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-93 — the all-LEFT-primitive split term** (sibling of body-65's all-right).  For the all-left
choice `p_L = fun _ _ => Sum.inl true`, `splitTerm ⟨A, p_L⟩ = leftTerm A ⊗ (1 ⊗ rightTerm A)` — the `1 ⊗ X`
primitive leg of the quotient. -/
theorem resolved_allLeftPrimitive_splitTerm
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm A ⊗ₜ[ℚ] ((1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  unfold ResolvedCoproductProperForestData.resolvedSplitChoiceTerm
  simp only [ResolvedCoproductProperForestData.localChoiceTerm, Sum.elim_inl, cond_true]
  have hprod : (∏ γ ∈ (A.1.elements.attach).attach,
      MvPolynomial.X ((γ.1.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD A.1 γ.1))
        ⊗ₜ[ℚ] (1 : ResolvedHopfH))
      = (D.supply G).leftTerm A ⊗ₜ[ℚ] (1 : ResolvedHopfH) := by
    simp only [← Algebra.TensorProduct.includeLeft_apply (S := ℚ) (R := ℚ)]
    rw [← map_prod]
    congr 1
    rw [Finset.prod_attach (A.1.elements.attach)
      (fun γ' => MvPolynomial.X ((γ'.1.toResolvedFeynmanGraph).toResolvedHopfGen (componentCD A.1 γ')))]
    rfl
  rw [hprod, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]

/-- **R-6c-body-93 — the per-`A` primitive split.**  `leftTerm A ⊗ primitive(quotGen A)` is the branch-boundary
`X ⊗ 1` leg plus the all-left split term (`1 ⊗ X` leg).  Uses `rightTerm A = X(quotGen A)` definitionally. -/
theorem resolved_image_primitive_split
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (D.supply G).leftTerm A ⊗ₜ[ℚ]
        resolvedCoproductGenPrimitive
          ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
      = (D.supply G).leftTerm A ⊗ₜ[ℚ] ((D.supply G).rightTerm A ⊗ₜ[ℚ] (1 : ResolvedHopfH))
        + D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G) := by
  rw [resolvedCoproductGenPrimitive, TensorProduct.tmul_add, resolved_allLeftPrimitive_splitTerm A]
  rfl

/-- **R-6c-body-93 — the nested-forest CORE supply.**  The boundary-free equation between the two pure primitive
choices `{p_R, p_L}` plus the forest-carrying choices (matched to quotient forests `B`) and the full
component-choice sum — the genuine nested-forest `Finset.sum_bij`, with all boundaries/primitives already peeled
off.  A representative lift completes the descent. -/
structure ResolvedNestedForestCoreSupply (D : ResolvedCoproductProperForestData) where
  /-- The boundary-free forest core: `{p_R, p_L}` + forests = full component-choice sum. -/
  forest_core : ∀ (G : ResolvedFeynmanGraph),
      (∑ A ∈ (D.supply G).forestCarrier,
          D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl false⟩ : ResolvedCoassocSplitChoice D G))
        + (∑ A ∈ (D.supply G).forestCarrier,
            D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G))
        + (∑ A ∈ (D.supply G).forestCarrier,
            ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ]
                ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                  ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
    = ∑ A ∈ (D.supply G).forestCarrier,
        ∑ p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)),
          D.resolvedSplitChoiceTerm (⟨A, p⟩ : ResolvedCoassocSplitChoice D G)
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-93 — body-92's `nested_matching` from the forest core.**  Discharge the two boundaries (body-70)
and the primitive `X ⊗ 1 + 1 ⊗ X` legs (the two term identities), leaving exactly `forest_core`. -/
def ResolvedNestedForestCoreSupply.toNestedForestBijectionSupply
    (S : ResolvedNestedForestCoreSupply D) : ResolvedNestedForestBijectionSupply D where
  nested_matching := fun G => by
    rw [resolved_image_boundary_eq_allRightPrimitive_sum,
      resolved_branch_boundary_eq_primitive_outer,
      show (∑ A ∈ (D.supply G).forestCarrier,
            ((D.supply G).leftTerm A ⊗ₜ[ℚ]
                resolvedCoproductGenPrimitive
                  ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
              + ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
                  (D.supply G).leftTerm A ⊗ₜ[ℚ]
                    ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                      ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)))
          = (∑ A ∈ (D.supply G).forestCarrier,
              (D.supply G).leftTerm A ⊗ₜ[ℚ] ((D.supply G).rightTerm A ⊗ₜ[ℚ] (1 : ResolvedHopfH)))
            + (∑ A ∈ (D.supply G).forestCarrier,
                D.resolvedSplitChoiceTerm (⟨A, fun _ _ => Sum.inl true⟩ : ResolvedCoassocSplitChoice D G))
            + (∑ A ∈ (D.supply G).forestCarrier,
                ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
                  (D.supply G).leftTerm A ⊗ₜ[ℚ]
                    ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                      ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)) from by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun A _ => by
          rw [resolved_image_primitive_split A])]
    rw [← S.forest_core G]
    abel
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-93 — `coassoc_gen` from the forest core** (via body-92/91/90/88). -/
theorem ResolvedNestedForestCoreSupply.coassoc_gen
    (S : ResolvedNestedForestCoreSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toNestedForestBijectionSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
