import GaugeGeometry.QFT.HopfAlgebra.Phi4StableFiniteSumReindex

/-!
# QFT-R1-body-650a — the STABLE coassoc alpha bridge, Steps 1–3 (iterated coproducts + choice expansion)

Body-649 proved the finite-sum reindex `stableForestBlock_finiteSum_reindex hSt :
stableMixedSplitChoiceFiniteSum hSt = stableInverseCodomainTripleSum hSt`.  Body-650 builds the two ITERATED
coproducts' alpha normal forms on a graph generator and shows they AGREE via that reindex.

**HONEST SPLIT (genuine volume).**  This file delivers the COMPLETE, axiom-clean **650a = Steps 1–3**:
the two iterated coproduct algebra homs (Step 1), the stable local-choice expansion of `Δˢ` on a local
generator and the product-of-sums expansion of `Δˢ` on the stable left aggregate (Step 2), and the generic
pure-choice partition of the component-choice sum (Step 3).  The remaining **650b = Steps 4–7** (the common
alpha part, the left/right alpha expansions, and the headline graph-generator coassociativity
`stableCoassocLeft (X g) = stableCoassocRight (X g)`) imports this file and is NOT attempted here — the
product-of-sums expansion (Step 2) plus the pure-choice partition (Step 3) matched against the 649 sigma
anchors is already a full body's worth of work.

## Steps delivered here (650a)
* **Step 1 — iterated coproducts.**  `stableCoassocLeftTail` / `stableCoassocLeft = tail ∘ Δˢ` (via
  `Algebra.TensorProduct.map Δˢ id` then `assoc`), `stableCoassocRightTail` / `stableCoassocRight = tail ∘ Δˢ`
  (via `Algebra.TensorProduct.map id Δˢ`, no associator), with thin `_apply` `rfl` anchors.  Both land in
  `StableResolvedPhi4HopfH3 = H ⊗ (H ⊗ H)`.
* **Step 2 — stable local-choice expansion.**  `stableLocalGen_eq_choiceSum` expands `Δˢ (X (local gen))` via
  the 629 `_of_graph` at the STABLE local completion + `Finset.sum_disjSum` (`Bool ⊕` carrier) into
  `∑ c ∈ stablePhi4LocalChoiceCarrier hSt γ, stableLocalChoiceTerm …`;
  `coproduct_resolved_stable_phi4_stableLeftAggregate_prodSum` pushes it through the left-aggregate PRODUCT via
  `map_prod` + `Finset.prod_sum` into the global-choice sum-of-products.
* **Step 3 — pure-choice partition.**  the generic `sum_extract_two` (re-derived `private`) + the two pure
  choices' global membership + their distinctness from `A.elements.Nonempty`, assembled into
  `stablePureChoicePartition`: the global-choice sum splits into all-RIGHT + all-LEFT + the mixed-carrier sum.
  `stableWTriplePrime_elements_nonempty` supplies the nonemptiness from W‴ membership (`IsProperForest.1`).

## Ownership boundary
The 649 reindex / 640 weight / 629 coproduct formula (`coproduct_resolved_stable_phi4_of_graph`) are consumed as
BLACK BOXES; ZERO geometry / star / `τ` / boundary / count re-proof.  ZERO consumption of the OLD abstract
coassoc structures (`ResolvedCoproductProperForestData`, `ResolvedForestBlockSupply`, …) or any forbidden
divergence class (`IsPermInvariantDivergence`, `IsIsoInvariantDivergence`, `IsAmbientInvariantDivergence`,
`IsDivergencePreservedByContract`, `IsDivergencePreservedByAdmissibleForestContract`,
`IsDivergenceReflectedByAdmissibleForestContract`) in ANY declaration TYPE; the generic `sum_extract_two` is
re-derived `private` (the old one lives in a polluted file).  NO representative descent; NO full polynomial
coassoc (651).

## HALT compliance
NO consume of old abstract-coassoc terms; NO representative descent / full-poly coassoc; ZERO new `structure` /
`class` / permanent `instance` (one file-local `local instance`; the iterated coproducts + tails are `def`
AlgHoms); ZERO `cast` / `HEq` / graph-data `▸`; ZERO `sorry` / `admit` / `native_decide`; all existing files
UNEDITED; axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open scoped TensorProduct
open scoped BigOperators

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally so the carrier/aggregate types that
mention `phi4DivergenceMeasureFamily` elaborate (providable instance, NO forbidden class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily650 :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 1 — the two iterated coproducts -/

/-- **body-650a (Step 1) — the LEFT iterated-coproduct tail** `assoc ∘ (Δˢ ⊗ id)`, an algebra hom
`H ⊗ H →ₐ H ⊗ (H ⊗ H)`. -/
noncomputable def stableCoassocLeftTail :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
      StableResolvedPhi4HopfH).toAlgHom.comp
    (Algebra.TensorProduct.map coproduct_resolved_stable_phi4 (AlgHom.id ℚ StableResolvedPhi4HopfH))

/-- **body-650a (Step 1) — the LEFT iterated coproduct** `stableCoassocLeft = assoc ∘ (Δˢ ⊗ id) ∘ Δˢ`. -/
noncomputable def stableCoassocLeft :
    StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3 :=
  stableCoassocLeftTail.comp coproduct_resolved_stable_phi4

/-- **body-650a (Step 1) — `stableCoassocLeft` factors through its tail after `Δˢ` (definitional).** -/
theorem stableCoassocLeft_apply (y : StableResolvedPhi4HopfH) :
    stableCoassocLeft y = stableCoassocLeftTail (coproduct_resolved_stable_phi4 y) := rfl

/-- **body-650a (Step 1) — the LEFT tail on a pure tensor.** -/
theorem stableCoassocLeftTail_tmul (a b : StableResolvedPhi4HopfH) :
    stableCoassocLeftTail (a ⊗ₜ[ℚ] b)
      = (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
          StableResolvedPhi4HopfH).toAlgHom (coproduct_resolved_stable_phi4 a ⊗ₜ[ℚ] b) := by
  simp only [stableCoassocLeftTail, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply]

/-- **body-650a (Step 1) — the RIGHT iterated-coproduct tail** `id ⊗ Δˢ`, an algebra hom
`H ⊗ H →ₐ H ⊗ (H ⊗ H)` (no associator). -/
noncomputable def stableCoassocRightTail :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3 :=
  Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH) coproduct_resolved_stable_phi4

/-- **body-650a (Step 1) — the RIGHT iterated coproduct** `stableCoassocRight = (id ⊗ Δˢ) ∘ Δˢ`. -/
noncomputable def stableCoassocRight :
    StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3 :=
  stableCoassocRightTail.comp coproduct_resolved_stable_phi4

/-- **body-650a (Step 1) — `stableCoassocRight` factors through its tail after `Δˢ` (definitional).** -/
theorem stableCoassocRight_apply (y : StableResolvedPhi4HopfH) :
    stableCoassocRight y = stableCoassocRightTail (coproduct_resolved_stable_phi4 y) := rfl

/-- **body-650a (Step 1) — the RIGHT tail on a pure tensor.** -/
theorem stableCoassocRightTail_tmul (a b : StableResolvedPhi4HopfH) :
    stableCoassocRightTail (a ⊗ₜ[ℚ] b) = a ⊗ₜ[ℚ] coproduct_resolved_stable_phi4 b := by
  simp only [stableCoassocRightTail, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-! ## Step 2 — the stable local-choice expansion -/

/-- **body-650a (Step 2) — `Δˢ` on a stable LOCAL generator is the local component-choice sum.**  Apply the
629 `_of_graph` generator rule at the STABLE local completion `stableLocalBoundaryCompletedGraph γ`, then read
the primitive part as the two `Bool` legs and the forest part as the inner W‴ forest sum, joined by
`Finset.sum_disjSum` over the `Bool ⊕ StableLocalForestIdx` carrier. -/
theorem stableLocalGen_eq_choiceSum (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    coproduct_resolved_stable_phi4
        (MvPolynomial.X ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)))
      = ∑ c ∈ stablePhi4LocalChoiceCarrier hSt γ, stableLocalChoiceTerm hSt γ hCDγ c := by
  rw [coproduct_resolved_stable_phi4_of_graph (stableLocalBoundaryCompletedGraph γ)
      (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
      (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)]
  unfold stablePhi4LocalChoiceCarrier
  rw [Finset.sum_disjSum, Fintype.sum_bool]
  rfl

/-- **body-650a (Step 2) — `Δˢ` on the stable LEFT AGGREGATE is the global component-choice sum-of-products.**
`stableLeftAggregate A hSt` is a PRODUCT of local generators; `Δˢ` is an algebra hom (`map_prod`), each factor
expands by `stableLocalGen_eq_choiceSum`, and `Finset.prod_sum` turns the product-of-sums into the sum over
the global component-choice carrier `stablePhi4GlobalChoiceCarrier hSt A` of the product of chosen local
terms. -/
theorem coproduct_resolved_stable_phi4_stableLeftAggregate_prodSum
    (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    coproduct_resolved_stable_phi4 (stableLeftAggregate A hSt)
      = ∑ p ∈ stablePhi4GlobalChoiceCarrier hSt A,
          ∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach.attach,
            stableLocalChoiceTerm hSt γ.1.1 (A.isConnectedDivergent γ.1.1 γ.1.2) (p γ.1 γ.2) := by
  unfold stableLeftAggregate
  rw [map_prod]
  rw [Finset.prod_congr rfl (fun γ _ =>
    stableLocalGen_eq_choiceSum hSt γ.1 (A.isConnectedDivergent γ.1 γ.2))]
  exact Finset.prod_sum
    (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).attach
    (fun γ => stablePhi4LocalChoiceCarrier hSt γ.1)
    (fun γ c => stableLocalChoiceTerm hSt γ.1 (A.isConnectedDivergent γ.1 γ.2) c)

/-! ## Step 3 — the pure-choice partition -/

/-- **body-650a (Step 3) — generic two-element extraction.**  For distinct `a, b ∈ s`, the sum splits off
`f a` and `f b` from the `(· ≠ a ∧ · ≠ b)`-filtered remainder.  Re-derived `private` (the old one lives in a
type-polluted file). -/
private theorem stable_sum_extract_two {M : Type*} [AddCommMonoid M] {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → M) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∑ x ∈ s, f x = f a + f b + ∑ x ∈ s.filter (fun x => x ≠ a ∧ x ≠ b), f x := by
  have hset : (s.erase a).erase b = s.filter (fun x => x ≠ a ∧ x ≠ b) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  rw [← Finset.add_sum_erase s f ha,
    ← Finset.add_sum_erase (s.erase a) f (Finset.mem_erase.mpr ⟨hab.symm, hb⟩),
    ← add_assoc, hset]

/-- **body-650a (Step 3) — the all-RIGHT choice lies in the global carrier.** -/
theorem stableAllRight_mem_globalChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (fun _ _ => Sum.inl false : StablePhi4ComponentChoice A) ∈ stablePhi4GlobalChoiceCarrier hSt A :=
  stablePhi4_mem_globalChoiceCarrier hSt A _

/-- **body-650a (Step 3) — the all-LEFT choice lies in the global carrier.** -/
theorem stableAllLeft_mem_globalChoiceCarrier (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) :
    (fun _ _ => Sum.inl true : StablePhi4ComponentChoice A) ∈ stablePhi4GlobalChoiceCarrier hSt A :=
  stablePhi4_mem_globalChoiceCarrier hSt A _

/-- **body-650a (Step 3) — the W‴ outer forest has at least one component.**  From `IsProperForest.1`
(`isNonempty_of_isProperForest`), extracted from the W‴ membership certificate. -/
theorem stableWTriplePrime_elements_nonempty
    {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G}
    (hA : A ∈ phi4WTriplePrimeIndex G) :
    (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty :=
  ResolvedAdmissibleSubgraph.isNonempty_of_isProperForest ((mem_phi4WTriplePrimeIndex G A).mp hA).2.2.2.2.1

/-- **body-650a (Step 3) — the two pure choices are distinct** (from a component). -/
theorem stableAllRight_ne_allLeft
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hne : (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty) :
    (fun _ _ => Sum.inl false : StablePhi4ComponentChoice A) ≠ (fun _ _ => Sum.inl true) := by
  obtain ⟨v, hv⟩ := hne
  intro h
  have hfalse := congrFun (congrFun h ⟨v, hv⟩) (Finset.mem_attach _ _)
  simp only [Sum.inl.injEq] at hfalse
  exact absurd hfalse Bool.false_ne_true

/-- **body-650a (Step 3, HEADLINE) — the pure-choice partition.**  The sum over the global component-choice
carrier splits into the all-RIGHT term, the all-LEFT term, and the sum over the mixed carrier — for ANY
weight `g`.  `sum_extract_two` at `a := allRight`, `b := allLeft`; membership by Step 3's two lemmas;
distinctness from `A.elements.Nonempty`; and the filtered remainder is exactly the mixed carrier (the mixed
predicate `(∃ ≠ inl false) ∧ (∃ ≠ inl true)` IS `(· ≠ allRight) ∧ (· ≠ allLeft)` pointwise). -/
theorem stablePureChoicePartition {M : Type*} [AddCommMonoid M]
    (hSt : StableResolvedBoundaryIds G)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (hne : (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A).Nonempty)
    (g : StablePhi4ComponentChoice A → M) :
    ∑ p ∈ stablePhi4GlobalChoiceCarrier hSt A, g p
      = g (fun _ _ => Sum.inl false) + g (fun _ _ => Sum.inl true)
        + ∑ p ∈ stablePhi4MixedChoiceCarrier hSt A, g p := by
  have hfilter : (stablePhi4GlobalChoiceCarrier hSt A).filter
        (fun c => c ≠ (fun _ _ => Sum.inl false) ∧ c ≠ (fun _ _ => Sum.inl true))
      = stablePhi4MixedChoiceCarrier hSt A := by
    unfold stablePhi4MixedChoiceCarrier
    refine Finset.filter_congr (fun c _ => ?_)
    have hR : (c ≠ (fun _ _ => Sum.inl false)) ↔ (∃ a hatt, c a hatt ≠ Sum.inl false) := by
      rw [Function.ne_iff]
      constructor
      · rintro ⟨a, ha⟩
        rw [Function.ne_iff] at ha
        obtain ⟨hatt, h⟩ := ha
        exact ⟨a, hatt, h⟩
      · rintro ⟨a, hatt, h⟩
        exact ⟨a, fun heq => h (congrFun heq hatt)⟩
    have hL : (c ≠ (fun _ _ => Sum.inl true)) ↔ (∃ a hatt, c a hatt ≠ Sum.inl true) := by
      rw [Function.ne_iff]
      constructor
      · rintro ⟨a, ha⟩
        rw [Function.ne_iff] at ha
        obtain ⟨hatt, h⟩ := ha
        exact ⟨a, hatt, h⟩
      · rintro ⟨a, hatt, h⟩
        exact ⟨a, fun heq => h (congrFun heq hatt)⟩
    rw [hR, hL]
  rw [stable_sum_extract_two (stablePhi4GlobalChoiceCarrier hSt A) g
      (stableAllRight_mem_globalChoiceCarrier hSt A)
      (stableAllLeft_mem_globalChoiceCarrier hSt A)
      (stableAllRight_ne_allLeft A hne),
    hfilter]

end GaugeGeometry.QFT.Combinatorial
