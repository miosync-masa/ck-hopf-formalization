import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantFactor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFactorGen
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant

/-!
# R-6c-body-126 — remnant transport PROVED: body-123's `hForest` from the existing region equality

Hundred-and-twenty-sixth genuine-body step, the `inr`-side twin of body-125.  Body-123's fielded remnant
flattening `hForest` (`∏ forestComponents rightFactorOf = leftTerm(remnant)`) is discharged against the EXISTING
remnant region equality `remnant_region_eq` (`RightFactorGen:78`) — the exact sibling of `rightSurvivor_region_eq`
that body-125 used.  Composed with body-123's bridge `remnant_factor_of_hForest`, this closes the FOURTH (last)
factor product `remnant_factor` down to the two honest remnant leaves (`remnantInj` + `remnantGen`), with all the
product-level work already proved by the existing machinery.

## The composition (PROVED)

`remnant_factor_of_region`: given a `ResolvedRemnantComponentSupply D G`, the remnant `Finset` injectivity `hInj`
and the de-contraction generator equality `remnantGen`,

```text
∏_{γ : (p γ).isRight} localRightFactor(p γ) = leftTerm(M.remnantForest q)
```

by `remnant_factor_of_hForest q q.selectedOuterContractGraph (M.remnantForest q)
(remnant_region_eq M q hInj remnantGen)`.  `remnant_region_eq` does the remnant-side `prod_image` bijection
(`hInj`) and the generator matching (`remnantGen`: the de-contraction remnant term = the forest choice's right
factor); `remnant_factor_of_hForest` (body-123) turns the assembly's `∏ localRightFactor(inr)` into the
`forestComponents` product via `prod_attach_filter_val` + `isForestChoice` filter + `localChoiceRightFactor`.  So
the remnant factor is closed to exactly `remnantInj` + `remnantGen`.

Unlike the survivor case (where `survivorGen` is `rfl`-level), the remnant `remnantGen` is the de-contraction
class equality `resolvedComponentGenTerm (remnantComponent (forestComponentOccurrence γ)) = rightFactorOf q γ`
(`rightFactorOf(inr Bᵧ) = rightTerm Bᵧ = X(Bᵧ.contractWithStars gen)` matched to the remnant component's
generator via the contract-twice class eq / `product_remnantGen_of_decontraction`).  It is the genuine
`inr`-side de-contraction leaf; `remnantInj` is the occurrence-injectivity of the remnant `Finset` image.

## All four factor products CLOSED

| factor | bridge | leaf(s) |
|---|---|---|
| `left_primitive` | body-119 | — (fully proved) |
| `right_primitive` | body-120 + body-125 | `survivorInj` + `survivorGen` (rfl) |
| `promoted` | body-122 | `hPD` (nonemptiness) |
| `remnant` | body-123 + body-126 (this) | `remnantInj` + `remnantGen` (de-contraction) |

So the summand-agreement PRODUCT side is fully assembled and every factor is closed to honest leaves; the residual
coassoc content is the map wiring (backward map / inverse laws / contract-twice geometry) and the base data
(carrier proper, measure leaf, the survivor/remnant `Inj`/`Gen` providers).

Per the HALT: `remnant_factor` is discharged against the existing `remnant_region_eq`, parallel to body-125; the
residual is exposed as `remnantInj` + `remnantGen` in the supply; `remnantInj`/`remnantGen` are NOT re-proved and
no backward-map content is entered.

Landed:

* `remnant_factor_of_region` — body-123's `remnant_factor` from `remnant_region_eq` (PROVED given the two leaves);
* `ResolvedRemnantTransportSupply D` — the remnant bundle (`M` + `remnantInj` + `remnantGen`);
* `.remnant_factor` — the assembly's remnant factor, discharged.

Toolkit body (like body-125), one small bundling supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-126 — the remnant factor from the region equality, PROVED.**  Body-123's `remnant_factor`
(`∏_{isRight} localRightFactor = leftTerm(remnantForest q)`) from the existing remnant region equality
(`remnant_region_eq`) composed with body-123's bridge, reduced to the remnant injectivity `hInj` and the
de-contraction generator equality `remnantGen`. -/
theorem remnant_factor_of_region (M : ResolvedRemnantComponentSupply D G)
    (q : ResolvedCoassocSplitChoice D G)
    (hInj : ∀ γ₁ ∈ q.forestComponents.attach, ∀ γ₂ ∈ q.forestComponents.attach,
        M.remnantComponent q (q.forestComponentOccurrence γ₁)
          = M.remnantComponent q (q.forestComponentOccurrence γ₂) → γ₁ = γ₂)
    (remnantGen : ∀ γ : {x : _ // x ∈ q.forestComponents},
        resolvedComponentGenTerm (M.remnantComponent q (q.forestComponentOccurrence γ))
          = D.rightFactorOf q γ.1) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (M.remnantForest q) :=
  remnant_factor_of_hForest q q.selectedOuterContractGraph (M.remnantForest q)
    (remnant_region_eq M q hInj remnantGen)

/-- **R-6c-body-126 — the remnant transport bundle.**  A `ResolvedRemnantComponentSupply` together with the two
remnant leaves (`remnantInj`, `remnantGen`), per split choice — the concrete provider of body-123's remnant
flattening. -/
structure ResolvedRemnantTransportSupply (D : ResolvedCoproductProperForestData) where
  /-- The remnant embedding supply. -/
  remnant : ∀ {G : ResolvedFeynmanGraph}, ResolvedRemnantComponentSupply D G
  /-- The remnant `Finset` occurrence-injectivity (the component bijection leaf). -/
  remnantInj : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ q.forestComponents.attach, ∀ γ₂ ∈ q.forestComponents.attach,
      remnant.remnantComponent q (q.forestComponentOccurrence γ₁)
        = remnant.remnantComponent q (q.forestComponentOccurrence γ₂) → γ₁ = γ₂
  /-- The de-contraction generator equality (the `inr`-side de-contraction leaf). -/
  remnantGen : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ : {x : _ // x ∈ q.forestComponents},
      resolvedComponentGenTerm (remnant.remnantComponent q (q.forestComponentOccurrence γ))
        = D.rightFactorOf q γ.1

/-- **R-6c-body-126 — the assembly's remnant factor from the remnant bundle.**  Discharged by
`remnant_factor_of_region`; only `remnantInj` + `remnantGen` remain. -/
theorem ResolvedRemnantTransportSupply.remnant_factor (S : ResolvedRemnantTransportSupply D)
    (q : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (S.remnant.remnantForest q) :=
  remnant_factor_of_region S.remnant q (S.remnantInj q) (S.remnantGen q)

end GaugeGeometry.QFT.Combinatorial
