import GaugeGeometry.QFT.HopfAlgebra.Phi4StableTwoStageQuotientEq

/-!
# QFT-R1-body-640 — the STABLE pointwise summand agreement (pure algebraic assembly)

Bodies 632 (LEFT), 638 (RIGHT), 639d (OUTER `quot_eq`) each delivered one of the three tensor factors of the
stable split-choice branch weight.  This body is a **pure algebraic assembly**: it reads those three completed
theorems ONCE each and rewrites the stable split-choice term `stableSplitChoiceTerm s.1` (body-633) into the
stable quotient-triple weight.  NO new geometry / count / star / τ / contract-twice expansion; NO inverse /
round-trip / Equiv; NO `sum_bij` / alpha / coassoc.

With `s : StablePhi4MixedSplitChoice G hSt`:

## Steps
* **Step 1 — stable forward package.**  `stableForestBlockForward s : Phi4WTriplePrimeInverseCodomain G`
  packages `⟨⟨stableSelectedOuter s.1, …⟩, ⟨stableQuotientForest s, …⟩⟩` (FORWARD ONLY; no inverse).  Two
  `[simp]` projection anchors.
* **Step 2 — stable quotient triple term.**  `stableQuotientTripleTerm hSt z` reads off the raw codomain `z`
  the three factors LEFT(selectedOuter) ⊗ (LEFT(quotientForest) ⊗ RIGHT(quotientForest)) in
  `StableResolvedPhi4HopfH3`.
* **Step 3 — forward expansion anchor.**  `stableQuotientTripleTerm_forward s` (`rfl`) unfolds the forward
  package into the three explicit factors.
* **Step 4 — three-factor rewrite.**  Onto `stableSplitChoiceTerm_factor s.1` apply body-632
  `stableSelectedOuter_leftFactor_product`, body-638 `stableRightFactorProduct_eq_quotientForest`, body-639d
  `stableForestRightTerm_outer_eq_quotientForest`.
* **Step 5 (HEADLINE) — `stableForestBlockForward_summand_agree`.**
  `stableSplitChoiceTerm s.1 = stableQuotientTripleTerm hSt (stableForestBlockForward s)`.

## HALT / red lines
NO new geometry / count / star / τ / contract-twice expansion; NO inverse / round-trip / Equiv; NO old resolved
term / old coproduct / old split-choice term consumed (the OLD `phi4WTriplePrime_quotientTripleTerm` /
`phi4WTriplePrime_splitChoiceTerm` are old-type — NOT consumed); NO `Finset.sum_bij` / sum equality / alpha /
coassoc; preserve `.attach` product multiplicity; ZERO new `structure` / `class` / permanent `instance` (one
file-local `local instance` for the φ⁴ family); ZERO `sorry` / `admit` / `native_decide`; ZERO forbidden
divergence class in any declaration TYPE; NO `HEq` / `cast` / graph-data `▸` (Prop-membership `▸` only); NO
`toFinset` / dedup / orbit quotient.  Body-625's no-go and bodies 629-639d / the old carrier are UNEDITED.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily640 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the stable forward package (FORWARD ONLY) -/

/-- **body-640 (Step 1) — the stable forward package.**  Packages the stable selected outer forest and the
stable live quotient forest into the raw inverse codomain `Phi4WTriplePrimeInverseCodomain G` (body-608).
FORWARD ONLY — no inverse / round-trip / `Equiv`. -/
noncomputable def stableForestBlockForward {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) : Phi4WTriplePrimeInverseCodomain G :=
  ⟨⟨stableSelectedOuter s.1, stableSelectedOuter_mem s.1⟩,
    ⟨stableQuotientForest s, stableQuotientForest_mem s⟩⟩

/-- **body-640 (Step 1) — the forward package first projection.** -/
@[simp] theorem stableForestBlockForward_fst {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    (stableForestBlockForward s).1 = ⟨stableSelectedOuter s.1, stableSelectedOuter_mem s.1⟩ := rfl

/-- **body-640 (Step 1) — the forward package second projection.** -/
@[simp] theorem stableForestBlockForward_snd {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    (stableForestBlockForward s).2 = ⟨stableQuotientForest s, stableQuotientForest_mem s⟩ := rfl

/-! ## Step 2 — the stable quotient triple term -/

/-- **body-640 (Step 2) — the stable quotient triple term.**  Reads the three tensor factors LEFT(A) ⊗
(LEFT(B) ⊗ RIGHT(B)) off the raw codomain member `z`, where `A := z.1.1` is the outer forest and `B := z.2.1`
is the inner forest of the star-contraction `A.contractWithStars (starOf G A)`.  Lands in
`StableResolvedPhi4HopfH3`. -/
noncomputable def stableQuotientTripleTerm (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) : StableResolvedPhi4HopfH3 :=
  stableLeftAggregate z.1.1 hSt ⊗ₜ[ℚ]
    (stableLeftAggregate z.2.1
        (stableResolvedBoundaryIds_contractWithStars z.1.1
          (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) hSt)
      ⊗ₜ[ℚ] stableForestRightTerm z.2.1
          (phi4WTriplePrimeCanonicalSupply.starOf _ z.2.1)
          (phi4WTriplePrimeCanonicalSupply.hCD _ z.2.1 z.2.2)
          (stableResolvedBoundaryIds_contractWithStars z.2.1
            (phi4WTriplePrimeCanonicalSupply.starOf _ z.2.1)
            (stableResolvedBoundaryIds_contractWithStars z.1.1
              (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) hSt)))

/-! ## Step 3 — the forward expansion anchor -/

/-- **body-640 (Step 3) — the forward expansion anchor.**  Instantiating the quotient triple term at the forward
package unfolds (`rfl`) to the three explicit stable factors: LEFT(selectedOuter) ⊗ (LEFT(quotientForest) ⊗
RIGHT(quotientForest)).  Pure definitional unfolding — proof irrelevance on the stable witnesses. -/
theorem stableQuotientTripleTerm_forward {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableQuotientTripleTerm hSt (stableForestBlockForward s)
      = stableLeftAggregate (stableSelectedOuter s.1) hSt ⊗ₜ[ℚ]
          (stableLeftAggregate (stableQuotientForest s)
              (stableSelectedOuterContractGraph_stableIds s.1)
            ⊗ₜ[ℚ] stableForestRightTerm (stableQuotientForest s)
                (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
                  (stableQuotientForest s))
                (phi4WTriplePrimeCanonicalSupply.hCD (stableSelectedOuterContractGraph s.1)
                  (stableQuotientForest s) (stableQuotientForest_mem s))
                (stableResolvedBoundaryIds_contractWithStars (stableQuotientForest s)
                  (phi4WTriplePrimeCanonicalSupply.starOf (stableSelectedOuterContractGraph s.1)
                    (stableQuotientForest s))
                  (stableSelectedOuterContractGraph_stableIds s.1))) := rfl

/-! ## Steps 4-5 — the three-factor rewrite + the HEADLINE -/

/-- **body-640 (Step 5, HEADLINE) — the stable pointwise summand agreement.**  The stable split-choice branch
weight (body-633) IS the stable quotient-triple weight at the forward package.  A PURE algebraic assembly: the
LEFT factor by body-632 `stableSelectedOuter_leftFactor_product`, the RIGHT product by body-638
`stableRightFactorProduct_eq_quotientForest`, and the OUTER `quot_eq` factor by body-639d
`stableForestRightTerm_outer_eq_quotientForest`.  NO new geometry; witness differences by proof irrelevance. -/
theorem stableForestBlockForward_summand_agree {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4MixedSplitChoice G hSt) :
    stableSplitChoiceTerm s.1 = stableQuotientTripleTerm hSt (stableForestBlockForward s) := by
  rw [stableQuotientTripleTerm_forward s, stableSplitChoiceTerm_factor s.1,
    stableSelectedOuter_leftFactor_product s.1,
    stableForestRightTerm_outer_eq_quotientForest s]
  congr 1
  congr 1
  exact stableRightFactorProduct_eq_quotientForest hSt s

end GaugeGeometry.QFT.Combinatorial
