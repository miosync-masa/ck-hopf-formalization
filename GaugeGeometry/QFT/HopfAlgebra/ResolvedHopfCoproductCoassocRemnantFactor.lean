import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedFactorSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPartition

/-!
# R-6c-body-123 — remnant factor: the FOURTH (last) factor product, reduced to the remnant de-contraction

Hundred-and-twenty-third genuine-body step, the LAST factor product `remnant_factor` (the `inr` /
forest-choice side of the RIGHT factor).  Its bridge to the existing right-partition machinery is proved (mirror
of body-122), reducing it to the remnant flattening `hForest` (`∏ forestComponents rightFactorOf =
leftTerm(remnantForest)`).  Unlike the promoted flattening (body-122, an EXISTING proved lemma
`forestPart_eq_promotedOf`), the remnant flattening is a de-contraction TRANSPORT — a fielded hypothesis even in
the existing right-factor assembly — reducing to `product_remnantGen_of_decontraction` plus the remnant
component bijection.  With this, all four factor products' bridges are complete; only the transport / `hPD`
leaves remain.

## The bridge (PROVED)

`remnant_factor_of_hForest`: given the remnant flattening `hForest`,

```text
∏_{γ : (p γ).isRight} localRightFactor(p γ) = leftTerm(remnant)
```

by the SAME bridge as body-122 — `prod_attach_filter_val` (double-`attach` → single `attach` of
`forestComponents`), the filter `(p γ).isRight ↔ isForestChoice γ.1`, and the summand `localRightFactor(p γ) =
rightFactorOf q γ.1` (`localChoiceRightFactor` at `choiceAt`).

## The remnant flattening (the de-contraction leaf)

`hForest : ∏_{γ ∈ forestComponents} rightFactorOf q γ = leftTerm(remnantForest)` is the RIGHT mirror of
`forestPart_eq_promotedOf`, but NOT already proved: `rightFactorOf(inr Bᵧ) = rightTerm Bᵧ = X(Bᵧ.contractWithStars
gen)` is the CONTRACTED sub-forest's generator (one generator per forest choice), and `leftTerm(remnantForest) =
∏ X(remnant component gen)`.  The existing `product_remnantGen_of_decontraction` (`ProductGenLeaves`) proves the
per-component identity `X(remnant component gen) = rightFactorOf q γ` (via `remnantGen` /
`rightFactorOf_eq_rightTerm_of_choiceAt_inr`), so `hForest` follows once the remnant components biject with the
forest components — the remnant DE-CONTRACTION transport (`Bᵧ` contracted in its component ↦ a remnant component
in the quotient), the `inr`-side sibling of the right-primitive SURVIVAL transport (body-121).  It is the
`hForest` hypothesis of the existing `rightFactorProduct_eq_quotientForestTerm` (`RightFactorAssembly`).

## All four factor products bridged

| factor | source/bridge | leaf |
|---|---|---|
| `left_primitive` | body-119 (same-graph) | — (fully proved) |
| `right_primitive` | body-120 source | survival transport (body-121) |
| `promoted` | body-122 | `hPD` (nonemptiness) |
| `remnant` | body-123 (this) | remnant de-contraction (`hForest`) |

So the summand-agreement PRODUCT side is fully assembled; the residual leaves are the two quotient transports
(survival / de-contraction), `hPD` / `hLP` (nonemptiness), and the base data.

Per the HALT: `remnant_factor` is reduced to the remnant flattening (`hForest`, PROVED bridge); `hForest` is
isolated as the de-contraction leaf (reducing to `product_remnantGen_of_decontraction` + the remnant bijection);
no occurrence-injectivity / backward map is entered.

Landed:

* `remnant_factor_of_hForest` — the assembly's `remnant_factor` from the remnant flattening (PROVED bridge).

Toolkit body (like body-119/120/122), no new supply.  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **R-6c-body-123 — the remnant factor from the remnant flattening** (PROVED bridge).  `∏_{isRight}
localRightFactor = leftTerm(remnant)` given `hForest : ∏ forestComponents rightFactorOf = leftTerm(remnant)`.
The fourth (last) factor product's bridge; `hForest` is the remnant de-contraction leaf. -/
theorem remnant_factor_of_hForest (q : ResolvedCoassocSplitChoice D G)
    (H : ResolvedFeynmanGraph) (remnant : ResolvedAdmissibleSubgraph H)
    (hForest : (∏ γ ∈ q.forestComponents, D.rightFactorOf q γ) = resolvedForestLeftTerm remnant) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm remnant := by
  rw [← hForest, ResolvedCoassocSplitChoice.forestComponents,
    ← prod_attach_filter_val q.1.1.elements.attach q.isForestChoice (D.rightFactorOf q)]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro γ hγ
    simp only [ResolvedCoassocSplitChoice.isForestChoice, ResolvedCoassocSplitChoice.choiceAt, eq_iff_iff]
    constructor
    · intro h; obtain ⟨B, hB⟩ := Sum.isRight_iff.mp h; exact ⟨B, hB⟩
    · rintro ⟨B, hB⟩; rw [hB]; rfl
  · intro γ hγ
    rw [ResolvedCoproductProperForestData.rightFactorOf, ResolvedCoassocSplitChoice.choiceAt]
    rfl

end GaugeGeometry.QFT.Combinatorial
