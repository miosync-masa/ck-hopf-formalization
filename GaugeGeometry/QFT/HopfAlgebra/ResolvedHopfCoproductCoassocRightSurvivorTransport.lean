import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveSurvivalTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFactorGen
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedFactorSource

/-!
# R-6c-body-125 — right-survivor transport PROVED: body-121's `transport` from the existing region equality

Hundred-and-twenty-fifth genuine-body step, discharging body-121's fielded survival `transport`
(`leftTerm(sourceRightPrim q) = leftTerm(rightSurvivor q)`) against the EXISTING right-survivor region equality
`rightSurvivor_region_eq` (`RightFactorGen`).  The transport was the last leaf of the right-primitive factor
product; here it is reduced to the two honest survivor leaves — the survivor `Finset` injectivity (`survivorInj`)
and the reembed generator equality (`survivorGen`, an `rfl`-level fact) — with the product-level bridge proved.

## The source↔right-components alignment (PROVED)

`sourceRightPrim_eq_rightComponents_prod`: the source right-primitive forest's left term is the product of the
right factors over the right-primitive component `Finset`:

```text
leftTerm(A'.filterElements rightPrimSelected) = ∏_{γ ∈ rightComponents} rightFactorOf q γ
```

by `resolvedForestLeftTerm_eq_prod` (left term = product of component gen terms over the filtered elements),
`prod_attach_filter_val` (the body-122 single-`attach` reindex, elements-`filter` ↦ `attach`-`filter`), the
predicate bridge `rightPrimSelected q γ.1 ↔ isRightPrimitive γ` (both say the choice is `Sum.inl false`), and the
summand `rightFactorOf q γ = resolvedComponentGenTerm γ.1` for right-primitive `γ`
(`rightFactorOf_eq_genTerm_of_isRightPrimitive`).  So `sourceRightPrim` reindexes exactly onto the
`rightComponents` product that `rightSurvivor_region_eq` consumes.

## The transport (PROVED given the two survivor leaves)

`right_survivor_transport`: given a `ResolvedRightSurvivorSupply D G`, the survivor injectivity `hInj` and the
reembed generator equality `survivorGen`,

```text
leftTerm(sourceRightPrim q) = leftTerm(R.rightSurvivorForest q)
```

by `(sourceRightPrim_eq_rightComponents_prod q).trans (rightSurvivor_region_eq R q hInj survivorGen)`.  The
region equality does the survivor-side `prod_image` bijection (`hInj`) and the generator matching (`survivorGen`);
the alignment does the source-side reindex.  This is EXACTLY body-121's `transport`, so
`ResolvedRightSurvivorTransportSupply` (bundling `R` + `hInj` + `survivorGen`) yields the body-121
`ResolvedRightPrimitiveSurvivalTransportSupply` — and hence the assembly's `right_primitive_factor` — with the
transport fully proved down to `survivorInj` + `survivorGen`.

`survivorGen` is the reembed generator equality (`resolvedComponentGenTerm (survivorComponent γ) =
resolvedComponentGenTerm γ.1`), an `rfl`-level fact for the concrete `survivorReembed`
(`survivorReembed_toResolvedFeynmanGraph`, `rightSurvivorComponentOf_gen`); `survivorInj` is the component
injectivity (the `Finset`-bijection leaf, a fielded fact even in the existing right-factor assembly).  So the
right-primitive factor product is now closed modulo exactly these two survivor facts — the remnant `inr` side
(body-123's `hForest`) closes identically against `remnant_region_eq`.

Per the HALT: the transport is proved at term/product level against the existing region equality; the residual is
isolated as `survivorInj` (`hInj`) + `survivorGen` (the reembed `gen_eq`); no remnant / backward-map content is
entered.

Landed:

* `sourceRightPrim_eq_rightComponents_prod` — the source↔right-components product alignment (PROVED);
* `right_survivor_transport` — body-121's transport from `rightSurvivor_region_eq` (PROVED given the two leaves);
* `ResolvedRightSurvivorTransportSupply D` — the survivor bundle (`R` + `hInj` + `survivorGen`);
* `.toRightPrimitiveSurvivalTransportSupply` — the body-121 supply, transport discharged.

Toolkit body (like body-121/122/123), one small bundling supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-125 — the source↔right-components alignment.**  The source right-primitive forest's left term is
the product of the right factors over the right-primitive component `Finset` — the exact left-hand side of
`rightSurvivor_region_eq`. -/
theorem sourceRightPrim_eq_rightComponents_prod (q : ResolvedCoassocSplitChoice D G) :
    resolvedForestLeftTerm (q.1.1.filterElements (fun γ => rightPrimSelected q γ))
      = ∏ γ ∈ q.rightComponents, D.rightFactorOf q γ := by
  rw [resolvedForestLeftTerm_eq_prod, ResolvedAdmissibleSubgraph.filterElements_elements,
    ← prod_attach_filter_val q.1.1.elements (fun δ => rightPrimSelected q δ)
      resolvedComponentGenTerm,
    ResolvedCoassocSplitChoice.rightComponents]
  apply Finset.prod_congr
  · apply Finset.filter_congr
    intro γ hγ
    simp only [ResolvedCoassocSplitChoice.isRightPrimitive, rightPrimSelected,
      ResolvedCoassocSplitChoice.choiceAt, eq_iff_iff]
    exact ⟨fun ⟨_, he⟩ => he, fun he => ⟨γ.2, he⟩⟩
  · intro γ hγ
    rw [Finset.mem_filter] at hγ
    exact (rightFactorOf_eq_genTerm_of_isRightPrimitive hγ.2).symm

/-- **R-6c-body-125 — the right-survivor transport, PROVED.**  Body-121's `transport`
(`leftTerm(sourceRightPrim q) = leftTerm(rightSurvivorForest q)`) from the source↔right-components alignment
composed with the existing right-survivor region equality (`rightSurvivor_region_eq`), reduced to the survivor
injectivity `hInj` and the reembed generator equality `survivorGen`. -/
theorem right_survivor_transport (R : ResolvedRightSurvivorSupply D G)
    (q : ResolvedCoassocSplitChoice D G)
    (hInj : ∀ γ₁ ∈ q.rightComponents.attach, ∀ γ₂ ∈ q.rightComponents.attach,
        R.survivorComponent q γ₁ = R.survivorComponent q γ₂ → γ₁ = γ₂)
    (survivorGen : ∀ γ : {x : _ // x ∈ q.rightComponents},
        resolvedComponentGenTerm (R.survivorComponent q γ) = resolvedComponentGenTerm γ.1.1) :
    resolvedForestLeftTerm (q.1.1.filterElements (fun γ => rightPrimSelected q γ))
      = resolvedForestLeftTerm (R.rightSurvivorForest q) :=
  (sourceRightPrim_eq_rightComponents_prod q).trans (rightSurvivor_region_eq R q hInj survivorGen)

/-- **R-6c-body-125 — the right-survivor transport bundle.**  A `ResolvedRightSurvivorSupply` together with the
two survivor leaves (`survivorInj`, `survivorGen`), per split choice — the concrete provider of body-121's
survival transport. -/
structure ResolvedRightSurvivorTransportSupply (D : ResolvedCoproductProperForestData) where
  /-- The right-survivor embedding supply. -/
  survivor : ∀ {G : ResolvedFeynmanGraph}, ResolvedRightSurvivorSupply D G
  /-- The survivor `Finset` injectivity (the component bijection leaf). -/
  survivorInj : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ q.rightComponents.attach, ∀ γ₂ ∈ q.rightComponents.attach,
      survivor.survivorComponent q γ₁ = survivor.survivorComponent q γ₂ → γ₁ = γ₂
  /-- The reembed generator equality (an `rfl`-level fact for the concrete survivor reembed). -/
  survivorGen : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ : {x : _ // x ∈ q.rightComponents},
      resolvedComponentGenTerm (survivor.survivorComponent q γ) = resolvedComponentGenTerm γ.1.1

/-- **R-6c-body-125 — body-121's survival-transport supply from the survivor bundle.**  The transport is
discharged by `right_survivor_transport`; only `survivorInj` + `survivorGen` remain. -/
noncomputable def ResolvedRightSurvivorTransportSupply.toRightPrimitiveSurvivalTransportSupply
    (S : ResolvedRightSurvivorTransportSupply D) :
    ResolvedRightPrimitiveSurvivalTransportSupply D where
  rightSurvivor {G} q := S.survivor.rightSurvivorForest q
  transport {G} q := right_survivor_transport S.survivor q (S.survivorInj q) (S.survivorGen q)

end GaugeGeometry.QFT.Combinatorial
