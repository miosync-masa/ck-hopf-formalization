import GaugeGeometry.QFT.HopfAlgebra.Phi4StableGenuineForestBlockEquiv

/-!
# QFT-R1-body-649 — the STABLE finite-sum REINDEX (bijection ⇒ finite sum equality)

Body-648 delivered the genuine stable forest-block `Equiv`
`stablePhi4ForestBlockEquiv : StablePhi4MixedSplitChoice G hSt ≃ Phi4WTriplePrimeInverseCodomain G` and the
finite-source packaging `Equiv` `stablePhi4FiniteForestBlockEquiv : StablePhi4MixedChoiceFiniteIndex G hSt ≃
Phi4WTriplePrimeInverseCodomain G` (with the `_apply` `rfl` anchor `E x = stableForestBlockForward (E₀ x)`),
DISCHARGING body-641's single bijectivity obligation.  Body-640 delivered the pointwise summand agreement
`stableForestBlockForward_summand_agree`.  This body PROMOTES that bijection + the weight equality to a genuine
FINITE SUM EQUALITY via `Finset.sum_bij'`, reading BOTH the 648 `Equiv` (maps-to both directions + the two
inverse laws) AND the 640 weight equality (via 641's `stableFiniteForward_summand_agree`) as black boxes.

    stableForestBlock_finiteSum_reindex hSt :
      stableMixedSplitChoiceFiniteSum hSt = stableInverseCodomainTripleSum hSt

## Steps
* **Step 1 — source carrier + full membership.**  `stablePhi4MixedChoiceFiniteCarrier` (the explicit
  `Finset.sigma` over `(phi4WTriplePrimeIndex G).attach` of the per-outer `.attach`ed mixed carrier), and
  `mem_stablePhi4MixedChoiceFiniteCarrier` (EVERY finite-index element is a member — `Finset.mem_sigma` +
  `Finset.mem_attach` twice).
* **Step 2 — the two sums.**  `stableMixedSplitChoiceFiniteSum` (source sum of `stableSplitChoiceTerm (E₀ q).1`)
  and `stableInverseCodomainTripleSum` (target sum of `stableQuotientTripleTerm hSt z`).
* **Step 3 — `Equiv` landing.**  forward `q ↦ E q ∈ target` is `stableForestBlockForward_mem_inverseCodomainCarrier`
  (`E q = stableForestBlockForward (E₀ q)` by 648 `rfl`); backward `z ↦ E.symm z ∈ source` is the Step-1 full
  membership.
* **Step 4 — weighted agreement (READ 640).**  `stablePhi4FiniteForestBlockEquiv_summand_agree` =
  `stableFiniteForward_summand_agree (E₀ q)` — the RHS `stableQuotientTripleTerm hSt (stableForestBlockForward
  (E₀ q))` is DEFEQ to `stableQuotientTripleTerm hSt (E q)` by 648 `_apply` `rfl`.  Body-640's three-factor
  rewrite is NOT rebuilt.
* **Step 5 (HEADLINE) — `Finset.sum_bij'`.**  Forward `i := E`, inverse `j := E.symm`, maps-to = Step 3 (both
  directions), inverse laws = `Equiv.symm_apply_apply` / `Equiv.apply_symm_apply`, summand equality = Step 4.
* **Step 6 — flattening anchors.**  `stableMixedSplitChoiceFiniteSum_sigma` /
  `stableInverseCodomainTripleSum_sigma` re-express each sum as an outer-over-`.attach` / inner-over-`.attach`
  double sum via `Finset.sum_sigma` (for body-650).

## Ownership boundary
The 648 `Equiv` (bijectivity + `symm_apply_apply` / `apply_symm_apply`) and the 640 weight equality are read as
BLACK BOXES; NO geometry / star / `τ` / boundary / count / inverse-law re-proof; NO re-run of body-640's
three-factor rewrite; NO `Finset.image` / dedup / orbit quotient; NO alpha / coproduct / coassoc.

## HALT compliance
NO alpha / coproduct expansion / coassoc; NO `cast` / `HEq` / graph-data `▸`; NO new `structure` / `class` /
permanent `instance`; NO old-623 `Equiv` consumption; upstream unedited; axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical
open scoped BigOperators

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

variable {G : ResolvedFeynmanGraph}

/-- The concrete φ⁴ divergence measure family, registered file-locally so the spelled-out inner W‴ index type in
the Step-6 target flattening anchor elaborates (providable instance, NO forbidden class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily649 :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 1 — the source carrier + full membership -/

/-- **body-649 (Step 1) — the explicit finite source carrier.**  The `Finset.sigma` over the `.attach` of the
outer W‴ index, and for each outer forest `A` the `.attach` of the per-outer mixed choice carrier
`stablePhi4MixedChoiceCarrier hSt A.1`.  Matches body-641's finite-source `Σ` shape (eases the body-650
`sum_sigma`). -/
noncomputable def stablePhi4MixedChoiceFiniteCarrier (G : ResolvedFeynmanGraph)
    (hSt : StableResolvedBoundaryIds G) : Finset (StablePhi4MixedChoiceFiniteIndex G hSt) :=
  (phi4WTriplePrimeIndex G).attach.sigma
    (fun A => (stablePhi4MixedChoiceCarrier hSt A.1).attach)

/-- **body-649 (Step 1) — EVERY finite-index element is a member.**  Both index levels are full `.attach`s, so
membership is `Finset.mem_sigma` + `Finset.mem_attach` twice — no condition on `q`. -/
theorem mem_stablePhi4MixedChoiceFiniteCarrier {hSt : StableResolvedBoundaryIds G}
    (q : StablePhi4MixedChoiceFiniteIndex G hSt) :
    q ∈ stablePhi4MixedChoiceFiniteCarrier G hSt := by
  unfold stablePhi4MixedChoiceFiniteCarrier
  exact Finset.mem_sigma.mpr ⟨Finset.mem_attach _ _, Finset.mem_attach _ _⟩

/-! ## Step 2 — the two finite sums -/

/-- **body-649 (Step 2) — the source finite sum.**  The sum over the explicit finite source carrier of the
stable split-choice branch weight, read through the body-641 packaging `Equiv` `E₀`. -/
noncomputable def stableMixedSplitChoiceFiniteSum (hSt : StableResolvedBoundaryIds G) :
    StableResolvedPhi4HopfH3 :=
  ∑ q ∈ stablePhi4MixedChoiceFiniteCarrier G hSt,
    stableSplitChoiceTerm (stablePhi4MixedChoiceFiniteIndexEquiv hSt q).1

/-- **body-649 (Step 2) — the target finite sum.**  The sum over the raw inverse-codomain carrier of the stable
quotient-triple weight. -/
noncomputable def stableInverseCodomainTripleSum (hSt : StableResolvedBoundaryIds G) :
    StableResolvedPhi4HopfH3 :=
  ∑ z ∈ stablePhi4InverseCodomainCarrier G, stableQuotientTripleTerm hSt z

/-! ## Step 4 — the weighted agreement (READ body-640, do NOT fabricate) -/

/-- **body-649 (Step 4) — the finite-index weighted agreement.**  The source weight at `q` equals the target
weight at the finite forest-block image `E q`.  Read DIRECTLY from body-641's `stableFiniteForward_summand_agree`
(itself body-640's three-factor result) at `E₀ q`: the RHS `stableQuotientTripleTerm hSt (stableForestBlockForward
(E₀ q))` is DEFEQ to `stableQuotientTripleTerm hSt (E q)` by the body-648 `_apply` `rfl`.  NO rebuild of the
body-640 rewrite. -/
theorem stablePhi4FiniteForestBlockEquiv_summand_agree {hSt : StableResolvedBoundaryIds G}
    (q : StablePhi4MixedChoiceFiniteIndex G hSt) :
    stableSplitChoiceTerm (stablePhi4MixedChoiceFiniteIndexEquiv hSt q).1
      = stableQuotientTripleTerm hSt (stablePhi4FiniteForestBlockEquiv hSt q) :=
  stableFiniteForward_summand_agree (stablePhi4MixedChoiceFiniteIndexEquiv hSt q)

/-! ## Step 5 — the HEADLINE finite-sum reindex via `Finset.sum_bij'` -/

/-- **body-649 (Step 5, HEADLINE) — the stable finite-sum reindex.**  The source finite sum equals the target
finite sum: the body-648 finite forest-block `Equiv` `E` reindexes the source carrier onto the inverse-codomain
carrier, and the summands agree at each image by Step 4.  Proved by `Finset.sum_bij'` feeding forward `E`,
inverse `E.symm`, the two landing lemmas (Step 3), the two `Equiv` inverse laws, and the Step-4 weight equality. -/
theorem stableForestBlock_finiteSum_reindex (hSt : StableResolvedBoundaryIds G) :
    stableMixedSplitChoiceFiniteSum hSt = stableInverseCodomainTripleSum hSt := by
  unfold stableMixedSplitChoiceFiniteSum stableInverseCodomainTripleSum
  refine Finset.sum_bij'
    (fun q _ => stablePhi4FiniteForestBlockEquiv hSt q)
    (fun z _ => (stablePhi4FiniteForestBlockEquiv hSt).symm z)
    (fun q _ => stableForestBlockForward_mem_inverseCodomainCarrier
      (stablePhi4MixedChoiceFiniteIndexEquiv hSt q))
    (fun z _ => mem_stablePhi4MixedChoiceFiniteCarrier
      ((stablePhi4FiniteForestBlockEquiv hSt).symm z))
    (fun q _ => (stablePhi4FiniteForestBlockEquiv hSt).symm_apply_apply q)
    (fun z _ => (stablePhi4FiniteForestBlockEquiv hSt).apply_symm_apply z)
    (fun q _ => stablePhi4FiniteForestBlockEquiv_summand_agree q)

/-! ## Step 6 — the flattening anchors (for body-650) -/

/-- **body-649 (Step 6) — the source sum as a double sum.**  Outer over `(phi4WTriplePrimeIndex G).attach`,
inner over the per-outer `.attach`ed mixed carrier, via `Finset.sum_sigma`. -/
theorem stableMixedSplitChoiceFiniteSum_sigma (hSt : StableResolvedBoundaryIds G) :
    stableMixedSplitChoiceFiniteSum hSt
      = ∑ A ∈ (phi4WTriplePrimeIndex G).attach,
          ∑ p ∈ (stablePhi4MixedChoiceCarrier hSt A.1).attach,
            stableSplitChoiceTerm (stablePhi4MixedChoiceFiniteIndexEquiv hSt ⟨A, p⟩).1 := by
  unfold stableMixedSplitChoiceFiniteSum stablePhi4MixedChoiceFiniteCarrier
  exact Finset.sum_sigma _ _ _

/-- **body-649 (Step 6) — the target sum as a double sum.**  Outer over `(phi4WTriplePrimeIndex G).attach`,
inner over the `.attach` of the inner W‴ index of the star-contraction, via `Finset.sum_sigma`. -/
theorem stableInverseCodomainTripleSum_sigma (hSt : StableResolvedBoundaryIds G) :
    stableInverseCodomainTripleSum hSt
      = ∑ A ∈ (phi4WTriplePrimeIndex G).attach,
          ∑ B ∈ (phi4WTriplePrimeIndex
            (A.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))).attach,
            stableQuotientTripleTerm hSt ⟨A, B⟩ := by
  unfold stableInverseCodomainTripleSum stablePhi4InverseCodomainCarrier
  exact Finset.sum_sigma _ _ _

end GaugeGeometry.QFT.Combinatorial
