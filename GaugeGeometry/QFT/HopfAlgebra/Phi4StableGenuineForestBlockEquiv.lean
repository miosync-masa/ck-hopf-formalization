import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForestBlockLeftInverse

/-!
# QFT-R1-body-648 — the genuine STABLE forest-block `Equiv` (the crowning assembly)

Body-646 delivered the STABLE forest-block RIGHT inverse
`stableForestBlockForward (stableRecoveredSplitChoice hSt z) = z`; body-647c delivered the FULL LEFT inverse
`stableRecoveredSplitChoice hSt (stableForestBlockForward s) = s`.  Both hold on the FULL RAW stable carriers
(exact component multiplicity, no orbit quotient, no dedup).  This body is the CORONATION: it reads those two
round-trips as the `Function.Injective` / `Function.Surjective` of `stableForestBlockForward`, DISCHARGES
body-641's single named obligation `StablePhi4ForestBlockForwardBijective`, and emits the genuine `Equiv`

    stablePhi4ForestBlockEquiv : StablePhi4MixedSplitChoice G hSt ≃ Phi4WTriplePrimeInverseCodomain G

whose four fields ARE bodies 640 / 646 / 647c read DIRECTLY (no wrapper re-proof), plus two `rfl` anchors and
the finite-source packaging `Equiv` `stablePhi4FiniteForestBlockEquiv` ready for the body-649 `Finset.sum_bij`.

(File name note: the OLD body-623 `phi4WTriplePrime_forestBlockEquiv` lives in a distinct module over the OLD
carrier and is NEVER consumed — body-641's audit already recorded it as INAPPLICABLE to the stable source; this
genuine stable issuance leaves it intact.)

## Steps
* **Step 1 (Injective)** — `stableForestBlockForward_injective`: `f s = f t` ⇒ `s = t` by `congrArg`
  `stableRecoveredSplitChoice hSt` + body-647c's LEFT inverse read at both ends.
* **Step 2 (Surjective)** — `stableForestBlockForward_surjective`: witness `stableRecoveredSplitChoice hSt z`,
  body-646's RIGHT inverse returned directly.
* **Step 3 (Obligation)** — `stablePhi4ForestBlockForward_bijective`: the body-641 open `Prop`
  `StablePhi4ForestBlockForwardBijective` discharged as `⟨injective, surjective⟩`.
* **Step 4 (HEADLINE `Equiv`)** — `stablePhi4ForestBlockEquiv`: `toFun := stableForestBlockForward`,
  `invFun := stableRecoveredSplitChoice hSt`, `left_inv`/`right_inv` = 647c / 646 read directly.
* **Step 5 (anchors + finite Equiv)** — `_apply` / `_symm_apply` `rfl` anchors, and
  `stablePhi4FiniteForestBlockEquiv` = the body-641 finite-source packaging `Equiv` composed with the headline.

## HALT compliance
NO new geometry / star / `τ` / boundary / count proof; NO body-640 summand-agreement re-proof; NO
`Finset.sum_bij` / alpha / coassoc; NO consumption of the OLD body-623 `Equiv` as a term; NO `cast` / `HEq` /
`▸`; NO new `structure` / `class` / permanent `instance`; upstream unedited; axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`); no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — injectivity from the LEFT inverse (body-647c) -/

/-- **body-648 (Step 1) — `stableForestBlockForward` is injective.**  From body-647c's LEFT inverse
`stableRecoveredSplitChoice hSt (stableForestBlockForward s) = s`: apply `stableRecoveredSplitChoice hSt` to
`f s = f t` and read the round-trip at both ends. -/
theorem stableForestBlockForward_injective (hSt : StableResolvedBoundaryIds G) :
    Function.Injective
      (stableForestBlockForward : StablePhi4MixedSplitChoice G hSt → Phi4WTriplePrimeInverseCodomain G) := by
  intro s t hst
  rw [← stableRecoveredSplitChoice_forestBlockForward s,
    ← stableRecoveredSplitChoice_forestBlockForward t, hst]

/-! ## Step 2 — surjectivity from the RIGHT inverse (body-646) -/

/-- **body-648 (Step 2) — `stableForestBlockForward` is surjective.**  For any raw codomain `z`, the
source-independent recovered split choice `stableRecoveredSplitChoice hSt z` is a preimage by body-646's RIGHT
inverse. -/
theorem stableForestBlockForward_surjective (hSt : StableResolvedBoundaryIds G) :
    Function.Surjective
      (stableForestBlockForward : StablePhi4MixedSplitChoice G hSt → Phi4WTriplePrimeInverseCodomain G) :=
  fun z => ⟨stableRecoveredSplitChoice hSt z, stableForestBlockForward_recoveredSplitChoice hSt z⟩

/-! ## Step 3 — discharge body-641's single named obligation -/

/-- **body-648 (Step 3) — the body-641 obligation is discharged.**  `StablePhi4ForestBlockForwardBijective` —
the single open `Prop` body-641 fixed for the stable forest-block forward map — is now PROVED, bundling
Steps 1 and 2. -/
theorem stablePhi4ForestBlockForward_bijective (hSt : StableResolvedBoundaryIds G) :
    StablePhi4ForestBlockForwardBijective G hSt :=
  ⟨stableForestBlockForward_injective hSt, stableForestBlockForward_surjective hSt⟩

/-! ## Step 4 — the genuine stable forest-block `Equiv` -/

/-- **body-648 (Step 4, HEADLINE) — the genuine stable forest-block `Equiv`.**  `stableForestBlockForward` and
the source-independent `stableRecoveredSplitChoice` are inverse on the FULL RAW stable mixed split-choice index
and the FULL RAW inverse-codomain Sigma — exact component multiplicity, no orbit quotient, no dedup.  The
`left_inv` / `right_inv` fields ARE bodies 647c / 646, read directly (no wrapper re-proof). -/
noncomputable def stablePhi4ForestBlockEquiv (hSt : StableResolvedBoundaryIds G) :
    StablePhi4MixedSplitChoice G hSt ≃ Phi4WTriplePrimeInverseCodomain G where
  toFun := stableForestBlockForward
  invFun := stableRecoveredSplitChoice hSt
  left_inv := stableRecoveredSplitChoice_forestBlockForward
  right_inv := stableForestBlockForward_recoveredSplitChoice hSt

@[simp] theorem stablePhi4ForestBlockEquiv_apply (hSt : StableResolvedBoundaryIds G)
    (s : StablePhi4MixedSplitChoice G hSt) :
    stablePhi4ForestBlockEquiv hSt s = stableForestBlockForward s := rfl

@[simp] theorem stablePhi4ForestBlockEquiv_symm_apply (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) :
    (stablePhi4ForestBlockEquiv hSt).symm z = stableRecoveredSplitChoice hSt z := rfl

/-! ## Step 5 — the finite-source packaging `Equiv` (ready for body-649) -/

/-- **body-648 (Step 5) — the finite-source packaging `Equiv`.**  The body-641 explicit finite source index
`StablePhi4MixedChoiceFiniteIndex G hSt` is equivalent to the raw inverse codomain by composing the body-641
packaging `Equiv` (finite index ≃ stable mixed split choice) with the headline forest-block `Equiv`.  This is
the reindexing bijection body-649 will feed to `Finset.sum_bij` (with body-640's weight equality). -/
noncomputable def stablePhi4FiniteForestBlockEquiv (hSt : StableResolvedBoundaryIds G) :
    StablePhi4MixedChoiceFiniteIndex G hSt ≃ Phi4WTriplePrimeInverseCodomain G :=
  (stablePhi4MixedChoiceFiniteIndexEquiv hSt).trans (stablePhi4ForestBlockEquiv hSt)

@[simp] theorem stablePhi4FiniteForestBlockEquiv_apply (hSt : StableResolvedBoundaryIds G)
    (x : StablePhi4MixedChoiceFiniteIndex G hSt) :
    stablePhi4FiniteForestBlockEquiv hSt x
      = stableForestBlockForward (stablePhi4MixedChoiceFiniteIndexEquiv hSt x) := rfl

end GaugeGeometry.QFT.Combinatorial
