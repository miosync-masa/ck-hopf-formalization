import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeGenuineForestBlockEquiv

/-!
# QFT-R1-body-624 — family-native forest-block summand agreement: terms + factorization PROVED, three geometric identities are a RED-LINE STOP

Body-623 delivered the genuine whole forest-block `Equiv`
`phi4WTriplePrime_forestBlockEquiv : Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃
Phi4WTriplePrimeInverseCodomain G`.  This body was to put the algebraic "weight" on that bijection: show each
summand TERM agrees, `splitChoiceTerm s = quotientTripleTerm (forestBlockEquiv s)`.

## What this body PROVES (the family-native algebraic backbone — Steps 1–2)

* **Step 1 — family-native terms.**  `ResolvedPhi4HopfH3`, the two tensor legs
  `phi4EdgeCompleteLocalLeftFactor` / `phi4EdgeCompleteLocalRightFactor` of body-601's
  `phi4EdgeCompleteLocalChoiceTerm`, the split-choice branch weight `phi4WTriplePrime_splitChoiceTerm`
  (`assoc ((∏γ localChoiceTerm) ⊗ rightTerm s.outer)`), and the quotient triple term
  `phi4WTriplePrime_quotientTripleTerm z = leftTerm z.outer ⊗ (leftTerm z.quotient ⊗ rightTerm z.quotient)`.
  These are the φ⁴-family mirrors of the OLD class-fixed `resolvedSplitChoiceTerm` — the polluted
  `ResolvedCoproductProperForestData`-keyed versions are NOT consumed.
* **Step 2 — pure-tensor factorization (PROVED).**  `phi4EdgeCompleteLocalChoiceTerm_factor`
  (`localChoiceTerm = leftFactor ⊗ rightFactor`), `phi4_prod_tmul_factor` (product of pure tensors, commutative
  tensor ring), and `phi4WTriplePrime_splitChoiceTerm_factor`:
  `splitChoiceTerm s = (∏γ leftFactor) ⊗ ((∏γ rightFactor) ⊗ rightTerm s.outer)`.
  Pure algebra — the family-native mirror of the old body-99 `resolved_splitChoiceTerm_factor`.

## RED-LINE STOP — Step 3's three geometric identities are NOT family-native available (truthful STOP)

Step 4's forward summand agreement reduces, via the Step-2 factorization, to THREE geometric identities.  With
`A := selectedOuter s`, `Q := selectedOuterContractGraph s = A.contractWithStars starOf_G`,
`B := quotientForest s`:

* **(1) left product** — `∏γ phi4EdgeCompleteLocalLeftFactor = (summandSupply G).leftTerm ⟨A, selectedOuter_mem⟩`
  (`= A.toResolvedPhi4HopfH`).  Reading `A = leftOf ∪ promotedOf` MULTIPLICITY-EXACT needs the family-native
  branch products `left_primitive_factor` (left-primitive legs → `leftOf`) and `promoted_factor` (forest legs'
  `leftTerm B = ∏_{B.elements} X` telescoping into `promotedOf`'s promoted boundary-completed generators, i.e.
  promotion-invariance of `toResolvedPhi4HopfGenBoundaryCompleted`).  The abstract arc built these ONLY in the
  polluted `D`-keyed setting (`resolved_selectedOuter_left_factor_eq_of_parts_raw`, abstract body-258, whose
  section carries the forbidden `[IsPermInvariantDivergence]` / `[IsAmbientInvariantDivergence]`).  **No φ⁴
  family-native version exists.**
* **(2) right product** — `∏γ phi4EdgeCompleteLocalRightFactor = (summandSupply Q).leftTerm ⟨B, quotientForest_mem⟩`
  (`= B.toResolvedPhi4HopfH`).  Reading `B = survivor ∪ remnant` MULTIPLICITY-EXACT needs the survivor branch
  (right-primitive legs → survivors) and the remnant branch (forest legs' `rightTerm B` aggregated over the
  quotient forest).  Only the per-occurrence `phi4WTriplePrime_remnant_rightTerm_eq` (body-605) exists; the
  aggregated family-native branch products (abstract `resolved_quotientForest_right_factor_eq_of_parts`) are
  **not ported.**
* **(3) outer right — THE load-bearing identity** — `(summandSupply G).rightTerm ⟨A, selectedOuter_mem⟩`
  is `rightTerm s.outer` in the factorization; the target is `(summandSupply Q).rightTerm ⟨B, quotientForest_mem⟩`.
  Via `resolvedForestRightTermFor_class_eq` (body-588) this reduces EXACTLY to the two-stage contraction
  **class equality**
  `(s.outer.contractWithStars starOf_G).toResolvedClass = (B.contractWithStars starOf_Q).toResolvedClass`
  — the genuine Δᵣ-coassoc `quot_eq`.  A correcting permutation is ALLOWED here, but the two contractions live
  over DIFFERENT ambients (`G` vs `Q`), with DIFFERENT star assignments and DIFFERENT element sets
  (`s.outer.elements` vs `quotientForest.elements`), so the only generic tool
  `ResolvedAdmissibleSubgraph.mapPerm_contractWithStars_toResolvedClass` (single-contraction mapPerm invariance)
  does NOT bridge them.  In the abstract arc `quot_eq` is a FIELDED obligation discharged only through the
  whole bodies-511/519–529 `contract_class_eq` campaign (three whole-graph field equalities + a globally
  assembled correcting permutation `σ`), every piece carrying the forbidden abstract/divergence machinery.
  **No φ⁴ family-native `quot_eq`, and no generic reusable two-stage contraction class lemma, exists.**

Because all three identities are unavailable family-natively (and the polluted `D`-keyed versions are forbidden
to consume — they carry the forbidden divergence classes in their types), Step 3 cannot close from the current
infrastructure, and hence Steps 4–5 (`phi4WTriplePrime_forestBlockForward_summand_agree`, the headline
`phi4WTriplePrime_forestBlockEquiv_summand_agree`) cannot be stated without an unavailable rewrite.  This is a
TRUTHFUL STOP — never a forced or fabricated agreement.  The maximal honest deliverable is Steps 1–2 above
(the family-native terms + the pure-tensor factorization), which are genuine, reusable progress a follow-up
body can consume once the three family-native geometric identities are supplied.

## Resolution route (revised roadmap — the three identities are ported as INDEPENDENT bodies, bundled only at 628)
What body-623 proved is the CORRESPONDENCE of terms; what 624+ must prove is that the CORRESPONDING TERMS HAVE
EQUAL WEIGHT — and inside that weight equality hides `quot_eq`, the geometric core of CK coassociativity.
The type has exposed `index Equiv ≠ weighted summand agreement`.
* **body-625** — family-native LEFT-factor product identity (1): `∏ leftFactor = (summandSupply G).leftTerm ⟨A,_⟩`.
  Read abstract body-258 as a BLUEPRINT only; do NOT consume the polluted theorem. `Finset.prod_bij` over
  `leftOf ∪ promotedOf`, multiplicity-exact.
* **body-626** — aggregate RIGHT-factor product identity (2): `∏ rightFactor = (summandSupply Q).leftTerm ⟨B,_⟩`.
  Promote body-605's per-occurrence `rightTerm` equality to a product over the `survivor ∪ remnant` partition,
  multiplicity-exact.
* **body-627** — the two-stage resolved quotient CLASS equality `quot_eq` (3), THE genuine geometric battle:
  `(s.outer.contractWithStars starOf_G).toResolvedClass = (B.contractWithStars starOf_Q).toResolvedClass`, up to
  a correcting permutation (class equality only; strict canonical-star equality PERMANENTLY FORBIDDEN).
* **body-628** — summand agreement ASSEMBLY: rewrite Step-2 factorization by (1)/(2)/(3), then Step 5 =
  body-623's `_apply` `rfl` anchor ∘ Step 4. (The three identities are banked as independent theorems and
  bundled ONLY here — no pre-emptive structure.)
* **body-629–631** — `Finset.sum_bij` (via `forestBlockEquiv`) → alpha → generator coassoc → full algebra coassoc.

## HALT compliance
Steps 1–2 build, axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence
classes in any declaration type; NO old class-fixed `resolvedSplitChoiceTerm` / `localLeftFactor` /
`localRightFactor` consumed; NO `Finset.sum_bij` (that is body-625); NO strict canonical-star equality; NO
public `HEq` / `cast` / `▸`; NO orbit quotient / dedup (products use `.attach`, multiplicity-preserving); NO
`sorry` / `admit` / `native_decide`; bodies 601/605/607/623 unedited; ONE new file; a file-local
`local instance` for the divergence measure family (as in prior bodies), no other new `class` / `instance`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

noncomputable local instance phi4Inst624 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-- The φ⁴ triple-tensor codomain. -/
abbrev ResolvedPhi4HopfH3 := ResolvedPhi4HopfH ⊗[ℚ] (ResolvedPhi4HopfH ⊗[ℚ] ResolvedPhi4HopfH)

/-! ## Step 1 — Family-Native Terms -/

/-- **body-624 (Step 1) — the left tensor leg of `phi4EdgeCompleteLocalChoiceTerm`.** -/
noncomputable def phi4EdgeCompleteLocalLeftFactor {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    (Bool ⊕
        (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) →
      ResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD)
      else (1 : ResolvedPhi4HopfH))
    (fun B => (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).leftTerm B)

/-- **body-624 (Step 1) — the right tensor leg of `phi4EdgeCompleteLocalChoiceTerm`.** -/
noncomputable def phi4EdgeCompleteLocalRightFactor {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    (Bool ⊕
        (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) →
      ResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then (1 : ResolvedPhi4HopfH)
      else MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD))
    (fun B => (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).rightTerm B)

/-- **body-624 (Step 1) — the family-native split-choice branch weight** in `ResolvedPhi4HopfH3`. -/
noncomputable def phi4WTriplePrime_splitChoiceTerm
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) : ResolvedPhi4HopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedPhi4HopfH ResolvedPhi4HopfH ResolvedPhi4HopfH).toAlgHom
    ((∏ γ ∈ (s.outer.elements.attach).attach,
        phi4EdgeCompleteLocalChoiceTerm γ.1.1
          (γ.1.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
            (s.outer.isConnectedDivergent γ.1.1 γ.1.2))
          (s.choice γ.1 γ.2))
      ⊗ₜ[ℚ] (phi4WTriplePrimeCanonicalSupply.summandSupply G).rightTerm ⟨s.outer, s.outer_mem⟩)

/-- **body-624 (Step 1) — the family-native quotient triple term** for a codomain pair `z`. -/
noncomputable def phi4WTriplePrime_quotientTripleTerm
    (z : Phi4WTriplePrimeInverseCodomain G) : ResolvedPhi4HopfH3 :=
  (phi4WTriplePrimeCanonicalSupply.summandSupply G).leftTerm z.1
    ⊗ₜ[ℚ]
    ((phi4WTriplePrimeCanonicalSupply.summandSupply
        (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))).leftTerm z.2
      ⊗ₜ[ℚ]
      (phi4WTriplePrimeCanonicalSupply.summandSupply
        (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))).rightTerm z.2)

/-! ## Step 2 — Pure Tensor Factorization -/

/-- **body-624 (Step 2) — `phi4EdgeCompleteLocalChoiceTerm` is a pure tensor.** -/
theorem phi4EdgeCompleteLocalChoiceTerm_factor {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF))
    (c : Bool ⊕
      (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) :
    phi4EdgeCompleteLocalChoiceTerm γ hCD c
      = phi4EdgeCompleteLocalLeftFactor γ hCD c ⊗ₜ[ℚ] phi4EdgeCompleteLocalRightFactor γ hCD c := by
  cases c with
  | inl b => cases b <;> rfl
  | inr B => rfl

/-- **body-624 (Step 2) — product of pure tensors factors** (commutative tensor ring). -/
theorem phi4_prod_tmul_factor {ι : Type*} (s : Finset ι) (f g : ι → ResolvedPhi4HopfH) :
    (∏ x ∈ s, (f x ⊗ₜ[ℚ] g x)) = (∏ x ∈ s, f x) ⊗ₜ[ℚ] (∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction with
  | empty => exact Algebra.TensorProduct.one_def
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- **body-624 (Step 2) — the split-term tensor factorization** (for ANY choice). -/
theorem phi4WTriplePrime_splitChoiceTerm_factor
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_splitChoiceTerm s
      = (∏ γ ∈ (s.outer.elements.attach).attach,
            phi4EdgeCompleteLocalLeftFactor γ.1.1
              (γ.1.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
                (s.outer.isConnectedDivergent γ.1.1 γ.1.2))
              (s.choice γ.1 γ.2))
        ⊗ₜ[ℚ]
          ((∏ γ ∈ (s.outer.elements.attach).attach,
              phi4EdgeCompleteLocalRightFactor γ.1.1
                (γ.1.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
                  (s.outer.isConnectedDivergent γ.1.1 γ.1.2))
                (s.choice γ.1 γ.2))
            ⊗ₜ[ℚ] (phi4WTriplePrimeCanonicalSupply.summandSupply G).rightTerm ⟨s.outer, s.outer_mem⟩) := by
  unfold phi4WTriplePrime_splitChoiceTerm
  rw [Finset.prod_congr rfl (fun γ _ =>
      phi4EdgeCompleteLocalChoiceTerm_factor γ.1.1
        (γ.1.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
          (s.outer.isConnectedDivergent γ.1.1 γ.1.2))
        (s.choice γ.1 γ.2)),
    phi4_prod_tmul_factor, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, Algebra.TensorProduct.assoc_tmul]

end GaugeGeometry.QFT.Combinatorial
