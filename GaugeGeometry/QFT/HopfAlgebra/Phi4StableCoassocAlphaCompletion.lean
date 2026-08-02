import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoassocAlphaBridge

/-!
# QFT-R1-body-650b — the STABLE coassoc alpha completion, Steps 4–8 + the graph coassoc HEADLINE

Body-650a delivered Steps 1–3 (the two iterated coproducts, the stable local-choice expansion of `Δˢ` on the
left aggregate, the pure-choice partition).  This body defines the COMMON alpha part once, expands BOTH iterated
coproducts on a graph generator into `commonPart + (respective 649 sum)`, and closes the graph-generator
coassociativity via the 649 finite-sum reindex.

## Steps
* **Step 4 — pure-branch evaluation.**  `stableGlobalChoiceProduct_allRight` /
  `stableGlobalChoiceProduct_allLeft`: the global choice product at the all-RIGHT / all-LEFT pure choice
  collapses (via `stableLocalChoiceTerm_factor` + `stable_prod_tmul_factor` + the 630/633 branch simp lemmas +
  `Finset.prod_const_one` + `Finset.prod_attach`) to `1 ⊗ stableLeftAggregate` / `stableLeftAggregate ⊗ 1`.
* **Step 5 — the common alpha part.**  `stableCoassocPrimitivePart` (the three primitive H3 terms) and
  `stableCoassocCommonPart` (primitive part + the forest-carrier sum of the three common H3 forest terms).
* **Step 6 — primitive-tail helpers.**  `stableCoassocLeftTail_primitive_of_graph` /
  `stableCoassocRightTail_primitive_of_graph`: push the 629 generator formula through each tail.
* **Step 7 — LEFT alpha expansion.**  `stableCoassocLeft_of_graph_alpha`: the LEFT iterated coproduct on a
  graph generator = `commonPart + stableMixedSplitChoiceFiniteSum`.
* **Step 8 — RIGHT alpha expansion.**  `stableCoassocRight_of_graph_alpha`: the RIGHT iterated coproduct on a
  graph generator = `commonPart + stableInverseCodomainTripleSum`.
* **HEADLINE — graph-generator coassociativity.**  `coproduct_resolved_stable_phi4_coassoc_of_graph`:
  `stableCoassocLeft (X g) = stableCoassocRight (X g)` via Steps 7/8 + the 649 reindex.

## Ownership boundary
649 / 650a / 629 / 640 / 633 / 630 consumed as BLACK BOXES; ZERO geometry / star / `τ` / boundary / count
re-proof; ZERO consumption of the OLD abstract-coassoc structures or any forbidden divergence class in ANY
declaration TYPE.  NO representative descent / arbitrary generator / full polynomial coassoc (651).

## HALT compliance
ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`;
`stableCoassocCommonPart` / `stableCoassocPrimitivePart` are `def`s); ZERO `cast` / `HEq` / graph-data `▸`;
ZERO `sorry` / `admit` / `native_decide`; all existing files UNEDITED; axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open scoped TensorProduct
open scoped BigOperators

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally so the carrier/aggregate types
elaborate (providable instance, NO forbidden class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily650b :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 4 — the pure-branch evaluations -/

/-- **body-650b (Step 4) — the all-RIGHT global choice product.**  Each local choice term at `Sum.inl false`
factors `1 ⊗ (X gen)` (LEFT branch `1`, RIGHT branch the boundary-completed generator), so the product is
`(∏ 1) ⊗ (∏ X gen) = 1 ⊗ stableLeftAggregate`. -/
theorem stableGlobalChoiceProduct_allRight (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
        stableLocalChoiceTerm hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl false))
      = (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] stableLeftAggregate A hSt := by
  have h1 : ∀ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
      stableLocalChoiceTerm hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl false)
        = (1 : StableResolvedPhi4HopfH)
          ⊗ₜ[ℚ] stableLocalRightFactor hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl false) := by
    intro γ _
    rw [stableLocalChoiceTerm_factor, stableLocalLeftFactor_inl_false]
  rw [Finset.prod_congr rfl h1, stable_prod_tmul_factor, Finset.prod_const_one]
  congr 1
  rw [Finset.prod_attach (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach
      (fun δ => stableLocalRightFactor hSt δ.1 (A.isConnectedDivergent δ.1 δ.2) (Sum.inl false))]
  unfold stableLeftAggregate
  exact Finset.prod_congr rfl (fun δ _ =>
    stableLocalRightFactor_inl_false hSt δ.1 (A.isConnectedDivergent δ.1 δ.2))

/-- **body-650b (Step 4) — the all-LEFT global choice product.**  Each local choice term at `Sum.inl true`
factors `(X gen) ⊗ 1` (LEFT branch the boundary-completed generator, RIGHT branch `1`), so the product is
`(∏ X gen) ⊗ (∏ 1) = stableLeftAggregate ⊗ 1`. -/
theorem stableGlobalChoiceProduct_allLeft (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
        stableLocalChoiceTerm hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl true))
      = stableLeftAggregate A hSt ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH) := by
  have h1 : ∀ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
      stableLocalChoiceTerm hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl true)
        = stableLocalLeftFactor hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (Sum.inl true)
          ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH) := by
    intro γ _
    rw [stableLocalChoiceTerm_factor, stableLocalRightFactor_inl_true]
  rw [Finset.prod_congr rfl h1, stable_prod_tmul_factor, Finset.prod_const_one]
  congr 1
  rw [Finset.prod_attach (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach
      (fun δ => stableLocalLeftFactor hSt δ.1 (A.isConnectedDivergent δ.1 δ.2) (Sum.inl true))]
  unfold stableLeftAggregate
  exact Finset.prod_congr rfl (fun δ _ =>
    stableLocalLeftFactor_inl_true hSt δ.1 (A.isConnectedDivergent δ.1 δ.2))

/-! ## Step 5 — the common alpha part -/

/-- **body-650b (Step 5) — the primitive alpha part** in `StableResolvedPhi4HopfH3`: the three primitive
tensors `X x ⊗ (1 ⊗ 1) + 1 ⊗ (X x ⊗ 1) + 1 ⊗ (1 ⊗ X x)`. -/
noncomputable def stableCoassocPrimitivePart (x : StableResolvedPhi4HopfGen) :
    StableResolvedPhi4HopfH3 :=
  MvPolynomial.X x ⊗ₜ[ℚ] ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH))
    + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] (MvPolynomial.X x ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH))
    + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X x)

/-- **body-650b (Step 5) — the common alpha part** in `StableResolvedPhi4HopfH3`: the primitive part plus the
forest-carrier sum of the three common H3 forest terms `1 ⊗ (left ⊗ right)`, `left ⊗ (right ⊗ 1)`,
`left ⊗ (1 ⊗ right)`.  Shared by BOTH the LEFT and RIGHT iterated coproduct alpha normal forms. -/
noncomputable def stableCoassocCommonPart (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) : StableResolvedPhi4HopfH3 :=
  stableCoassocPrimitivePart (G.toStableResolvedPhi4HopfGen hCD hSt)
    + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
        ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] stableForestSummand hSt A
          + (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
              StableResolvedPhi4HopfH).toAlgHom (stableForestSummand hSt A ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH))
          + stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
              ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ]
                stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                  (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                  (stableResolvedBoundaryIds_contractWithStars A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))

/-! ## Step 6 — the primitive-tail helpers -/

/-- **body-650b (Step 6) — the LEFT primitive tail on a graph generator.**  Pushing the 629 generator formula
through the LEFT tail: the primitive two terms contribute the primitive part plus the forest-carrier sum of the
`assoc (forestSummand ⊗ 1)` terms. -/
theorem stableCoassocLeftTail_primitive_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stableCoassocLeftTail
        (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt) ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH)
          + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = stableCoassocPrimitivePart (G.toStableResolvedPhi4HopfGen hCD hSt)
        + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
            (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
                StableResolvedPhi4HopfH).toAlgHom (stableForestSummand hSt A ⊗ₜ[ℚ]
              (1 : StableResolvedPhi4HopfH)) := by
  rw [map_add, stableCoassocLeftTail_tmul, stableCoassocLeftTail_tmul,
    coproduct_resolved_stable_phi4_of_graph G hCD hSt, coproduct_resolved_stable_phi4_one,
    stableCoassocPrimitivePart]
  unfold stableForestSum
  rw [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.add_tmul,
    TensorProduct.sum_tmul, map_add, map_add, map_sum]
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]
  abel

/-- **body-650b (Step 6) — the RIGHT primitive tail on a graph generator.**  Pushing the 629 generator formula
through the RIGHT tail: the primitive two terms contribute the primitive part plus the forest-carrier sum of the
`1 ⊗ forestSummand` terms. -/
theorem stableCoassocRightTail_primitive_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stableCoassocRightTail
        (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt) ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH)
          + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = stableCoassocPrimitivePart (G.toStableResolvedPhi4HopfGen hCD hSt)
        + ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
            (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] stableForestSummand hSt A := by
  rw [map_add, stableCoassocRightTail_tmul, stableCoassocRightTail_tmul,
    coproduct_resolved_stable_phi4_one, coproduct_resolved_stable_phi4_of_graph G hCD hSt,
    stableCoassocPrimitivePart]
  unfold stableForestSum
  rw [Algebra.TensorProduct.one_def, TensorProduct.tmul_add, TensorProduct.tmul_add,
    TensorProduct.tmul_sum]
  abel

/-! ## Step 7 — the LEFT alpha expansion -/

/-- **body-650b (Step 7, CRUX) — the mixed-inner sum equals the 649 finite mixed sum.**  The forest-carrier
sum of the per-outer mixed-choice sum of `assoc ((∏ choiceTerm) ⊗ outerRight)` IS
`stableMixedSplitChoiceFiniteSum` (the 649 source sum).  The two carriers align by defeq
(`(phi4WTriplePrimeCanonicalSupply.index G).carrier = phi4WTriplePrimeIndex G`), the inner `.attach` by
`Finset.sum_attach`, and the per-`(A,p)` summand by `Finset.prod_attach` (double-attach ↦ single-attach) against
`stableSplitChoiceTerm (E ⟨A,p⟩).1` (the 649 packaging `Equiv` `E`). -/
theorem stableMixedInner_eq_finiteSum (hSt : StableResolvedBoundaryIds G) :
    (∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
      ∑ p ∈ stablePhi4MixedChoiceCarrier hSt A.1,
        (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
            StableResolvedPhi4HopfH).toAlgHom
          ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A.1).attach.attach,
              stableLocalChoiceTerm hSt γ.1.1 (A.1.isConnectedDivergent γ.1.1 γ.1.2) (p γ.1 γ.2))
            ⊗ₜ[ℚ] stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
              (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
              (stableResolvedBoundaryIds_contractWithStars A.1
                (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))
      = stableMixedSplitChoiceFiniteSum hSt := by
  rw [stableMixedSplitChoiceFiniteSum_sigma]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [← Finset.sum_attach (stablePhi4MixedChoiceCarrier hSt A.1)
    (fun p => (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
        StableResolvedPhi4HopfH).toAlgHom
      ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A.1).attach.attach,
          stableLocalChoiceTerm hSt γ.1.1 (A.1.isConnectedDivergent γ.1.1 γ.1.2) (p γ.1 γ.2))
        ⊗ₜ[ℚ] stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
          (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
          (stableResolvedBoundaryIds_contractWithStars A.1
            (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hprod := Finset.prod_attach
    (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A.1).attach
    (fun δ => stableLocalChoiceTerm hSt δ.1 (A.1.isConnectedDivergent δ.1 δ.2)
      (p.1 δ (Finset.mem_attach _ δ)))
  exact congrArg (fun z => (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH
      StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom
    (z ⊗ₜ[ℚ] stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
      (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
      (stableResolvedBoundaryIds_contractWithStars A.1
        (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt))) hprod

/-- **body-650b (Step 7) — the LEFT tail on one forest summand.**  `assoc (Δˢ(leftAgg) ⊗ outerRight)` via the
650a product-of-sums expansion + the pure-choice partition + the Step-4 pure evals: the pure branches give the
`1 ⊗ summand` and `leftAgg ⊗ (1 ⊗ outerRight)` common terms, the mixed branch the per-`p` split-choice sum. -/
theorem stableCoassocLeftTail_forestSummand (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    stableCoassocLeftTail (stableForestSummand hSt A)
      = ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] stableForestSummand hSt A
          + stableLeftAggregate A.1 hSt ⊗ₜ[ℚ] ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ]
              stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                (stableResolvedBoundaryIds_contractWithStars A.1
                  (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))
        + ∑ p ∈ stablePhi4MixedChoiceCarrier hSt A.1,
            (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
                StableResolvedPhi4HopfH).toAlgHom
              ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A.1).attach.attach,
                  stableLocalChoiceTerm hSt γ.1.1 (A.1.isConnectedDivergent γ.1.1 γ.1.2) (p γ.1 γ.2))
                ⊗ₜ[ℚ] stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                  (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                  (stableResolvedBoundaryIds_contractWithStars A.1
                    (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)) := by
  have hne := stableWTriplePrime_elements_nonempty (A := A.1) A.2
  rw [show stableForestSummand hSt A
        = stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
            stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
              (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
              (stableResolvedBoundaryIds_contractWithStars A.1
                (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt) from rfl,
    stableCoassocLeftTail_tmul, coproduct_resolved_stable_phi4_stableLeftAggregate_prodSum hSt A.1,
    TensorProduct.sum_tmul, map_sum,
    stablePureChoicePartition hSt A.1 hne
      (fun p => (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
          StableResolvedPhi4HopfH).toAlgHom
        ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A.1).attach.attach,
            stableLocalChoiceTerm hSt γ.1.1 (A.1.isConnectedDivergent γ.1.1 γ.1.2) (p γ.1 γ.2))
          ⊗ₜ[ℚ] stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
            (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
            (stableResolvedBoundaryIds_contractWithStars A.1
              (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))]
  simp only [stableGlobalChoiceProduct_allRight, stableGlobalChoiceProduct_allLeft,
    stableForestSummand, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    Algebra.TensorProduct.assoc_tmul]

/-- **body-650b (Step 7, HEADLINE) — the LEFT iterated coproduct alpha normal form.**  On a graph generator the
LEFT iterated coproduct is `commonPart + stableMixedSplitChoiceFiniteSum`: the 629 formula through the LEFT
tail, the primitive tail (Step 6) contributing the primitive part + the `assoc (forestSummand ⊗ 1)` sum, and
each forest summand (Step 7 per-summand) contributing the `1 ⊗ forestSummand` / `left ⊗ (1 ⊗ right)` common
terms plus the mixed split-choice sum (crux). -/
theorem stableCoassocLeft_of_graph_alpha (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stableCoassocLeft (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = stableCoassocCommonPart G hCD hSt + stableMixedSplitChoiceFiniteSum hSt := by
  rw [stableCoassocLeft_apply, coproduct_resolved_stable_phi4_of_graph G hCD hSt, map_add,
    stableCoassocLeftTail_primitive_of_graph G hCD hSt]
  unfold stableForestSum
  rw [map_sum, Finset.sum_congr rfl (fun A _ => stableCoassocLeftTail_forestSummand hSt A),
    Finset.sum_add_distrib, Finset.sum_add_distrib, stableMixedInner_eq_finiteSum hSt,
    stableCoassocCommonPart, Finset.sum_add_distrib, Finset.sum_add_distrib]
  abel

/-! ## Step 8 — the RIGHT alpha expansion -/

/-- **body-650b (Step 8) — the RIGHT tail on one forest summand.**  `leftAgg ⊗ Δˢ(outerRight)`: the 629 formula
on the star-contraction generator `outerRight = X (contraction gen)` gives the primitive `left ⊗ (right ⊗ 1)`
and `left ⊗ (1 ⊗ right)` common terms plus `left ⊗ stableForestSum(contraction)` — the inner triple sum. -/
theorem stableCoassocRightTail_forestSummand (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    stableCoassocRightTail (stableForestSummand hSt A)
      = ((Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
              StableResolvedPhi4HopfH).toAlgHom (stableForestSummand hSt A ⊗ₜ[ℚ]
            (1 : StableResolvedPhi4HopfH))
          + stableLeftAggregate A.1 hSt ⊗ₜ[ℚ] ((1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ]
              stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
                (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
                (stableResolvedBoundaryIds_contractWithStars A.1
                  (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)))
        + ∑ B ∈ (phi4WTriplePrimeCanonicalSupply.index
              (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))).carrier.attach,
            stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
              stableForestSummand (stableResolvedBoundaryIds_contractWithStars A.1
                (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt) B := by
  rw [show stableForestSummand hSt A
        = stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
            stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
              (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
              (stableResolvedBoundaryIds_contractWithStars A.1
                (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt) from rfl,
    stableCoassocRightTail_tmul]
  rw [show stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
          (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
          (stableResolvedBoundaryIds_contractWithStars A.1
            (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)
        = MvPolynomial.X ((A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
            ).toStableResolvedPhi4HopfGen
            ((ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
                phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
                (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))).mp
              (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2))
            (stableResolvedBoundaryIds_contractWithStars A.1
              (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)) from rfl,
    coproduct_resolved_stable_phi4_of_graph
      (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1)) _ _]
  unfold stableForestSum
  rw [TensorProduct.tmul_add, TensorProduct.tmul_add, TensorProduct.tmul_sum]
  simp only [AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul,
    stableForestSummand]

/-- **body-650b (Step 8, CRUX) — the inner triple sum equals the 649 inverse-codomain triple sum.**  The
forest-carrier double sum of `leftAgg_A ⊗ forestSummand(contraction, B)` IS `stableInverseCodomainTripleSum`
(the 649 target sum): the two carrier levels align by defeq, and each summand `leftAgg_A ⊗ forestSummand B`
is `rfl`-equal to `stableQuotientTripleTerm hSt ⟨A,B⟩`. -/
theorem stableInverseInner_eq_tripleSum (hSt : StableResolvedBoundaryIds G) :
    (∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach,
      ∑ B ∈ (phi4WTriplePrimeCanonicalSupply.index
            (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))).carrier.attach,
        stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
          stableForestSummand (stableResolvedBoundaryIds_contractWithStars A.1
            (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt) B)
      = stableInverseCodomainTripleSum hSt := by
  rw [stableInverseCodomainTripleSum_sigma]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rfl

/-- **body-650b (Step 8, HEADLINE) — the RIGHT iterated coproduct alpha normal form.**  On a graph generator the
RIGHT iterated coproduct is `commonPart + stableInverseCodomainTripleSum`: the 629 formula through the RIGHT
tail, the primitive tail (Step 6) contributing the primitive part + the `1 ⊗ forestSummand` sum, and each
forest summand (Step 8 per-summand) contributing the `assoc (forestSummand ⊗ 1)` / `left ⊗ (1 ⊗ right)` common
terms plus the inner triple sum (crux). -/
theorem stableCoassocRight_of_graph_alpha (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stableCoassocRight (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = stableCoassocCommonPart G hCD hSt + stableInverseCodomainTripleSum hSt := by
  rw [stableCoassocRight_apply, coproduct_resolved_stable_phi4_of_graph G hCD hSt, map_add,
    stableCoassocRightTail_primitive_of_graph G hCD hSt]
  unfold stableForestSum
  rw [map_sum, Finset.sum_congr rfl (fun A _ => stableCoassocRightTail_forestSummand hSt A),
    Finset.sum_add_distrib, Finset.sum_add_distrib, stableInverseInner_eq_tripleSum hSt,
    stableCoassocCommonPart, Finset.sum_add_distrib, Finset.sum_add_distrib]
  abel

/-! ## HEADLINE — the graph-generator coassociativity -/

/-- **body-650b (HEADLINE) — the stable resolved φ⁴ coproduct is coassociative on a graph generator.**  Both
iterated coproducts land on the SAME `commonPart`; their residual sums (`stableMixedSplitChoiceFiniteSum` for
the LEFT, `stableInverseCodomainTripleSum` for the RIGHT) coincide by the 649 finite-sum reindex. -/
theorem coproduct_resolved_stable_phi4_coassoc_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    stableCoassocLeft (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = stableCoassocRight (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt)) := by
  rw [stableCoassocLeft_of_graph_alpha G hCD hSt, stableCoassocRight_of_graph_alpha G hCD hSt,
    stableForestBlock_finiteSum_reindex hSt]

end GaugeGeometry.QFT.Combinatorial
