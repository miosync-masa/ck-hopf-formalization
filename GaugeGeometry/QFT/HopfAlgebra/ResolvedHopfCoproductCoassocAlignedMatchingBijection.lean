import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestMatchingAlignment
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightInner

/-!
# R-6c-body-92 — aligned_matching bijection skeleton: the quotient index is `primitive ⊕ forests`

Ninety-second genuine-body step, decomposing `aligned_matching` (body-91's single deep leaf) into a resolved
`Finset.sum_bij` skeleton.  The image side distributes (PROVED) into a PRIMITIVE part plus a per-quotient-forest
sum, so the quotient index is `primitive ⊕ {nonempty quotient forests}` — the primitive lives OUTSIDE the
carrier, sidestepping the `∅` problem that recurred throughout bodies 68–86.

## The image side distributes (PROVED)

`resolved_image_summand_distribute`: for each outer `A`,

```text
leftTerm A ⊗ Δᵣ(rightTerm A)
  = leftTerm A ⊗ primitive(quotGen A)              -- the PRIMITIVE part (quotient stays whole)
    + ∑_{B ∈ quotCarrier A} leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)   -- the FOREST parts
```

via `coproduct_rightTerm` (`Δᵣ(rightTerm A) = primitive(quotGen A) + (D.supply quotGraph A).sum`) + `tmul_add` +
`tmul_sum`, where `quotGraph A = A.contractWithStars (D.starOf G A.1)` and `quotCarrier A =
(D.supply quotGraph A).forestCarrier` are the quotient graph's PROPER forests.

## The quotient index: `primitive ⊕ forests` (not a carrier `∅`)

So the image RHS per `A` is indexed by `{primitive} ⊕ quotCarrier A` — the primitive `leftTerm A ⊗
primitive(quotGen A)` is a SEPARATE summand, NOT a `B = ∅` carrier forest.  This is the key: the quotient stays
whole (primitive) is NOT an empty-forest carrier element; it is its own index slot.  So the nested-forest
bijection

```text
(A, component choice p)   ↔   (A, primitive)  or  (A, quotient forest B)
```

is over `piCarrier A ≃ {primitive-marker} ⊕ quotCarrier A` — no `∅` forest needed.  This matches the flat
argument's boundary/core split (the primitives absorb the boundary terms `1 ⊗ forestSum` / `assoc(forestSum ⊗
1)`, and the forests match the core).

## The skeleton

`ResolvedNestedForestBijectionSupply` fields the per-`A` matching in the DISTRIBUTED form: the branch
component-choice sum `∑_p splitTerm ⟨A, p⟩` equals the image `primitive + forest` distributed sum, with the two
global boundaries reshuffled.  `resolved_image_summand_distribute` rewrites the image side into that form; the
remaining content is the `Finset.sum_bij` `p ↔ (primitive | B)` with summand agreement (`splitTerm ⟨A, p⟩` =
the corresponding image term) — the resolved port of the flat `…_of_factorization`.  Its
`.toForestMatchingAlignmentSupply` recovers body-91's `aligned_matching`.

Per the HALT: the `sum_bij` inverse laws are NOT proved (they are `nested_matching`); the image distribution IS
proved; the `primitive ⊕ forests` quotient-index shape is fixed (no carrier `∅`); no flat `HopfH` transport, no
star-allocation detail.

Landed:

* `resolved_image_summand_distribute` — the image per-`A` distribution (primitive + forests), PROVED;
* `ResolvedNestedForestBijectionSupply D` — the per-`A` distributed matching + representative lift;
* `.toForestMatchingAlignmentSupply` / `.coassoc_gen` — to body-91/90/88.

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

/-- **R-6c-body-92 — the image per-`A` distribution.**  `leftTerm A ⊗ Δᵣ(rightTerm A)` distributes into the
PRIMITIVE part `leftTerm A ⊗ primitive(quotGen A)` (quotient stays whole) plus the FOREST sum over the quotient
graph's proper forests `B`.  So the quotient index is `primitive ⊕ quotCarrier A` — the primitive is a separate
slot, NOT an empty-forest carrier element. -/
theorem resolved_image_summand_distribute
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A)
      = (D.supply G).leftTerm A ⊗ₜ[ℚ]
          resolvedCoproductGenPrimitive
            ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
        + ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
            (D.supply G).leftTerm A ⊗ₜ[ℚ]
              ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B) := by
  rw [D.coproduct_rightTerm G A, TensorProduct.tmul_add, ResolvedCoproductForestSummandSupply.sum,
    TensorProduct.tmul_sum]

/-- **R-6c-body-92 — the nested-forest bijection skeleton.**  The per-`A` matching in distributed form: the
branch component-choice sum equals the image `primitive + forests` sum, with the two boundaries reshuffled.  The
quotient index is `primitive ⊕ quotCarrier A` (no carrier `∅`).  The genuine content is the `Finset.sum_bij`
`component choice p ↔ (primitive | quotient forest B)` with summand agreement. -/
structure ResolvedNestedForestBijectionSupply (D : ResolvedCoproductProperForestData) where
  /-- The nested-forest matching, image distributed to `primitive + forests`. -/
  nested_matching : ∀ (G : ResolvedFeynmanGraph),
    (1 : ResolvedHopfH) ⊗ₜ[ℚ] (D.supply G).sum
        + ∑ A ∈ (D.supply G).forestCarrier,
            ((D.supply G).leftTerm A ⊗ₜ[ℚ]
                resolvedCoproductGenPrimitive
                  ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
              + ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
                  (D.supply G).leftTerm A ⊗ₜ[ℚ]
                    ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                      ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B))
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

/-- **R-6c-body-92 — body-91's `aligned_matching` from the distributed bijection.**  Fold the image side back via
`resolved_image_summand_distribute`. -/
def ResolvedNestedForestBijectionSupply.toForestMatchingAlignmentSupply
    (S : ResolvedNestedForestBijectionSupply D) : ResolvedForestMatchingAlignmentSupply D where
  aligned_matching := fun G => by
    rw [show (∑ A ∈ (D.supply G).forestCarrier,
          (D.supply G).leftTerm A ⊗ₜ[ℚ] D.coproduct ((D.supply G).rightTerm A))
        = ∑ A ∈ (D.supply G).forestCarrier,
            ((D.supply G).leftTerm A ⊗ₜ[ℚ]
                resolvedCoproductGenPrimitive
                  ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2))
              + ∑ B ∈ (D.supply (A.1.contractWithStars (D.starOf G A.1))).forestCarrier,
                  (D.supply G).leftTerm A ⊗ₜ[ℚ]
                    ((D.supply (A.1.contractWithStars (D.starOf G A.1))).leftTerm B
                      ⊗ₜ[ℚ] (D.supply (A.1.contractWithStars (D.starOf G A.1))).rightTerm B)) from
        Finset.sum_congr rfl (fun A _ => resolved_image_summand_distribute A)]
    exact S.nested_matching G
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-92 — `coassoc_gen` from the distributed bijection** (via body-91/90/88). -/
theorem ResolvedNestedForestBijectionSupply.coassoc_gen
    (S : ResolvedNestedForestBijectionSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toForestMatchingAlignmentSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
