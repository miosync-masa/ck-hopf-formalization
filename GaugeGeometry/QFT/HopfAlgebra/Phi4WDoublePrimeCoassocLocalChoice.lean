import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeCoassocLeaves

/-!
# QFT-R1-body-594 — boundary-completed family local-choice expansion

Body-591 issued the genuine φ⁴ resolved coproduct `Δᵣ = coproduct_resolved_phi4`.  Body-593 pinned the
live-domain leaf owner.  This body re-keys the OLD abstract local-choice / product-of-sums pair
(`ResolvedHopfCoproductCoassocLocalChoice.lean` Steps 1-2 + `ResolvedHopfCoproductCoassocProdSum.lean`
Step 3) into the φ⁴ family, with the **correct inner ambient**.

The critical fix: the old chain expanded a component coproduct on `γ.toResolvedFeynmanGraph`, which in φ⁴
DISCARDS the induced boundary that body-589 restored.  Here every component representative is body-589's
`γ.toResolvedPhi4HopfGenBoundaryCompleted` — the boundary-ID-completed generator on
`γ.boundaryCompletedResolvedGraph`.  Because body-591's `summandSupply` `ForestIdx` is literally
`{B // B ∈ (index γ.boundaryCompletedResolvedGraph).carrier}`, the `Sum.inr` leg of the local-choice carrier
carries the LIVE carrier membership for free — the Step-4 banking that feeds body-593's leaf supply later.

## Contents

* Step 1 — `phi4LocalChoiceCarrier` / `phi4LocalChoiceTerm` (per-component choice carrier + term, inner
  ambient `γ.boundaryCompletedResolvedGraph`).
* Step 2 — `phi4gen_eq_localChoiceSum` (the per-component coproduct decomposition into the disjSum).
* Step 3 — `coproduct_resolved_phi4_toResolvedPhi4HopfH` (the forest-left aggregate coproduct as a product of
  component gens) + `coproduct_resolved_phi4_toResolvedPhi4HopfH_prodSum` (`Finset.prod_sum` expansion into
  global component choices).
* Step 4 — `phi4LocalChoice_inr_mem` (the anchor exposing the `Sum.inr` carrier membership).

Per the HALT: no `γ.toResolvedFeynmanGraph` as a component representative (inner ambient is
`γ.boundaryCompletedResolvedGraph`); no selectedOuter / split geometry / alpha / correspondence / coassoc;
no Measure / E / rep* old supply; no dedup (`.attach` and the `{B // …}` membership subtype are kept); zero
new `class`/`structure`/`instance`; zero forbidden divergence classes in any type; no `sorry`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

/-! ## Step 1 — local choice (inner ambient = boundaryCompletedResolvedGraph) -/

/-- **body-594 (Step 1) — the φ⁴ local choice carrier for a component `γ`.**  The two primitive legs
(`Bool`) disjointly united with the forest carrier of body-591's `summandSupply` on the **boundary-completed**
inner ambient `γ.boundaryCompletedResolvedGraph`.  The `Sum.inr` index type is exactly
`{B // B ∈ (index γ.boundaryCompletedResolvedGraph).carrier}` — the live carrier membership, banked for
free. -/
noncomputable def phi4LocalChoiceCarrier {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G) :
    Finset (Bool ⊕
        (phi4WDoublePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) :=
  (Finset.univ : Finset Bool).disjSum
    (phi4WDoublePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).forestCarrier

/-- **body-594 (Step 1) — the φ⁴ local choice term.**  The two primitive legs `X γ̂ ⊗ 1` / `1 ⊗ X γ̂` (with
`γ̂ = γ.toResolvedPhi4HopfGenBoundaryCompleted`, the body-589 boundary-completed generator), and per live
carrier member `B` the forest summand `leftTerm B ⊗ rightTerm B` of body-591's `summandSupply`. -/
noncomputable def phi4LocalChoiceTerm {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    (Bool ⊕
        (phi4WDoublePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) →
      ResolvedPhi4HopfH ⊗[ℚ] ResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD) ⊗ₜ[ℚ]
        (1 : ResolvedPhi4HopfH)
      else (1 : ResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD))
    (fun B => (phi4WDoublePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).leftTerm B
      ⊗ₜ[ℚ] (phi4WDoublePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).rightTerm B)

/-! ## Step 2 — component decomposition -/

/-- **body-594 (Step 2) — the per-component coproduct decomposition.**  `Δᵣ` on the boundary-completed
component generator is the finite disjSum of its two primitive legs plus its live-carrier forest summands.
The component representative is the body-589 boundary-completed generator (its `.val` is
`γ.boundaryCompletedResolvedGraph.toResolvedClass`), and the forest sum descends to the boundary-completed
inner ambient's `summandSupply.sum`. -/
theorem phi4gen_eq_localChoiceSum {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    phi4WDoublePrimeResolvedCoproductSupply.gen (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD)
      = ∑ b ∈ phi4LocalChoiceCarrier γ, phi4LocalChoiceTerm γ hCD b := by
  unfold phi4LocalChoiceCarrier phi4LocalChoiceTerm
  rw [Finset.sum_disjSum]
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool, cond_true, cond_false]
  simp only [ResolvedCoproductGenSupplyFor.gen,
    ResolvedFeynmanSubgraph.toResolvedPhi4HopfGenBoundaryCompleted_val,
    ResolvedCoproductGenSupplyFor.forestSum_mk, phi4WDoublePrimeResolvedCoproductSupply,
    ResolvedCoproductForestSummandSupplyFor.sum, resolvedCoproductGenPrimitiveFor]

/-! ## Step 3 — global choice expansion -/

/-- **body-594 (Step 3) — the resolved coproduct of the forest-left aggregate as a product of component
gens.**  `A.toResolvedPhi4HopfH` (body-590) is a product of `X γ̂` over the components; `coproduct_resolved_phi4`
is an algebra hom, so `map_prod` distributes and `coproduct_resolved_phi4_X` sends each factor to its
component gen (on the boundary-completed inner ambient). -/
theorem coproduct_resolved_phi4_toResolvedPhi4HopfH {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    coproduct_resolved_phi4 A.toResolvedPhi4HopfH
      = ∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach,
          phi4WDoublePrimeResolvedCoproductSupply.gen (γ.1.toResolvedPhi4HopfGenBoundaryCompleted
            (γ.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
              (@ResolvedAdmissibleSubgraph.isConnectedDivergent phi4DivergenceMeasureFamily G A
                γ.1 γ.2))) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  simp only [ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH, map_prod]
  exact Finset.prod_congr rfl (fun γ _ => coproduct_resolved_phi4_X _)

/-- **body-594 (Step 3, TARGET) — the product-of-sums expansion of the forest-left aggregate coproduct.**
Feeding the per-component decomposition (Step 2) through `Finset.prod_sum`: `Δᵣ(A.toResolvedPhi4HopfH)` is the
sum over **global component choices** `p` (a local choice per component) of the product of the chosen local
terms.  Every inner ambient is the boundary-completed `γ.boundaryCompletedResolvedGraph`. -/
theorem coproduct_resolved_phi4_toResolvedPhi4HopfH_prodSum {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    coproduct_resolved_phi4 A.toResolvedPhi4HopfH
      = ∑ p ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.pi
              (fun γ => phi4LocalChoiceCarrier γ.1),
          ∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
            phi4LocalChoiceTerm γ.1.1
              (γ.1.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
                (@ResolvedAdmissibleSubgraph.isConnectedDivergent phi4DivergenceMeasureFamily G A
                  γ.1.1 γ.1.2))
              (p γ.1 γ.2) := by
  rw [coproduct_resolved_phi4_toResolvedPhi4HopfH,
    Finset.prod_congr rfl (fun γ _ => phi4gen_eq_localChoiceSum γ.1 _), Finset.prod_sum]

/-! ## Step 4 — membership banking (anchor) -/

/-- **body-594 (Step 4, ANCHOR) — the `Sum.inr` leg carries live carrier membership.**  Because the forest
part of `phi4LocalChoiceCarrier` is indexed by `{B // B ∈ (index γ.boundaryCompletedResolvedGraph).carrier}`,
each choice `B` yields, for free, the live carrier membership `B.1 ∈ (index …).carrier` on the
**boundary-completed** inner ambient — exactly the datum body-593's leaf supply consumes downstream.  No
re-wrapping, no re-derivation. -/
theorem phi4LocalChoice_inr_mem {G : ResolvedFeynmanGraph} (γ : ResolvedFeynmanSubgraph G)
    (B : {B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph //
        B ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
          γ.boundaryCompletedResolvedGraph
          (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph)}) :
    B.1 ∈ @ResolvedProperForestFiniteIndex.carrier phi4DivergenceMeasureFamily
        γ.boundaryCompletedResolvedGraph
        (phi4WDoublePrimeCanonicalSupply.index γ.boundaryCompletedResolvedGraph) := B.2

end GaugeGeometry.QFT.Combinatorial
