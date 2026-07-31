import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockLeftInverseFull

/-!
# QFT-R1-body-623 — genuine whole forest-block `Equiv`

The crowning assembly.  Bodies 619/621/622b-3 delivered, on the FULL RAW carriers (no orbit quotient, no
dedup, exact component multiplicity):

* **619** — `phi4WTriplePrime_recoveredSplitChoice z : Phi4EdgeCompleteFilteredCoassocSplitChoice G`, the
  source-independent inverse inhabitant for an arbitrary codomain `z`.
* **621** — `phi4WTriplePrime_forestBlockForward_recoveredSplitChoice`, the RIGHT inverse
  `forestBlockForward (recoveredSplitChoice z) = z`.
* **622b-3** — `phi4WTriplePrime_recoveredSplitChoice_forestBlockForward`, the LEFT inverse
  `recoveredSplitChoice (forestBlockForward s) = s`.

This body wires those four facts into a single genuine `Equiv`
`Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃ Phi4WTriplePrimeInverseCodomain G`, plus two `rfl` anchors and
two named round-trip corollaries.  NO new geometry — the two round-trips ARE the `Equiv`'s `left_inv` /
`right_inv` fields, read directly.

(File name note: body-615's `Phi4WTriplePrimeForestBlockEquiv.lean` was the RED-LINE STOP that documented why
the `Equiv` could not yet be emitted; this genuine issuance lives in a distinct module and leaves 615 intact.)

## HALT compliance
Exactly ONE new `Equiv` def + two `@[simp]` `rfl` anchors + two named corollaries; NO new
`structure`/`class`/permanent `instance`; NO geometry / topology / divergence / boundary / star / permutation
re-proof; NO `HEq`/`cast`/`▸`/`Eq.ndrec`; NO corrected forward / global `τ` / orbit quotient / dedup; NO
summand agreement / `sum_bij` / alpha / coassoc; bodies 619/621/622b-3 unedited; axiom-clean
(`propext`, `Classical.choice`, `Quot.sound` only); no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable {G : ResolvedFeynmanGraph}

noncomputable local instance phi4Inst623 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-- **body-623 (HEADLINE) — the genuine whole forest-block `Equiv`.**  The forest-block forward map and the
source-independent recovered split-choice are inverse on the FULL RAW W‴ filtered split-choice index and the
FULL RAW inverse-codomain Sigma — exact component multiplicity, no orbit quotient, no dedup.  The `left_inv` /
`right_inv` fields ARE bodies 622b-3 / 621, read directly (no wrapper re-proof). -/
noncomputable def phi4WTriplePrime_forestBlockEquiv :
    Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃ Phi4WTriplePrimeInverseCodomain G where
  toFun := phi4WTriplePrime_forestBlockForward
  invFun := phi4WTriplePrime_recoveredSplitChoice
  left_inv := phi4WTriplePrime_recoveredSplitChoice_forestBlockForward
  right_inv := phi4WTriplePrime_forestBlockForward_recoveredSplitChoice

@[simp] theorem phi4WTriplePrime_forestBlockEquiv_apply
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_forestBlockEquiv s = phi4WTriplePrime_forestBlockForward s := rfl

@[simp] theorem phi4WTriplePrime_forestBlockEquiv_symm_apply
    (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_forestBlockEquiv.symm z = phi4WTriplePrime_recoveredSplitChoice z := rfl

/-- **body-623 — named `symm_apply_apply` corollary** (LEFT round-trip, restated on the `Equiv`). -/
theorem phi4WTriplePrime_forestBlockEquiv_symm_apply_apply
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_forestBlockEquiv.symm (phi4WTriplePrime_forestBlockEquiv s) = s :=
  phi4WTriplePrime_forestBlockEquiv.symm_apply_apply s

/-- **body-623 — named `apply_symm_apply` corollary** (RIGHT round-trip, restated on the `Equiv`). -/
theorem phi4WTriplePrime_forestBlockEquiv_apply_symm_apply
    (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_forestBlockEquiv (phi4WTriplePrime_forestBlockEquiv.symm z) = z :=
  phi4WTriplePrime_forestBlockEquiv.apply_symm_apply z

end GaugeGeometry.QFT.Combinatorial
