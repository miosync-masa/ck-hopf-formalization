import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductGrandSupply
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantDecontraction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromoteGen

/-!
# R-6c-leaf-2 — Product `survivorGen` / `remnantGen` from the concrete de-contraction supplies

Second leaf-discharge step.  Two of the twelve `ResolvedProductEqGrandSupply` leaves (6a-11b) — the two
generator equalities — are discharged from the already-built concrete supplies:

* `survivorGen` — the concrete right-survivor supply (6a-3c, `resolvedConcreteRightSurvivorSupply`) re-embeds
  each right-primitive component keeping its own graph, so its component generator IS `γ`'s.  Both sides are
  connected-divergent (the component is a CD component of `s.1.1`), so `resolvedComponentGenTerm_of_cd`
  reduces both to `X (componentGen …)` and the re-embed's `toResolvedFeynmanGraph = γ` closes it (`congr 1`).
* `remnantGen` — the remnant de-contraction supply (6a-4b, `ResolvedRemnantDecontractionSupply.remnantGen`)
  gives `resolvedComponentGenTerm (remnantComponent o) = o.rightTermOf`; and `rightTermOf` of the forest
  occurrence is exactly `D.rightFactorOf s γ.1` (`rightFactorOf_eq_rightTerm_of_choiceAt_inr` at the
  occurrence's `hchoice`).

Per the HALT, `survivorInj` / `remnantInj` are NOT proved; no `hSel` / `hQuot`; no containment / CD discharge.

Landed:

* `product_survivorGen_of_concreteSurvivor` — the `survivorGen` field for `resolvedConcreteRightSurvivorSupply`;
* `product_remnantGen_of_decontraction` — the `remnantGen` field for any `M` matching a de-contraction family.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-2 — the Product `survivorGen` leaf from the concrete right-survivor supply.**  The concrete
survivor re-embeds each right-primitive component keeping its own resolved graph, so its component generator
term is `γ.1.1`'s.  Both are CD (the component is a CD component of `s.1.1`). -/
theorem product_survivorGen_of_concreteSurvivor
    (hne : ∀ (s : ResolvedCoassocSplitChoice D G)
      (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
      γ.1.1.vertices.Nonempty)
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}) :
    resolvedComponentGenTerm ((resolvedConcreteRightSurvivorSupply D G hne).survivorComponent s γ)
      = resolvedComponentGenTerm γ.1.1 := by
  have hCDγ : γ.1.1.forget.IsConnectedDivergent := s.1.1.isConnectedDivergent γ.1.1 γ.1.2
  have hCDsurv := (resolvedConcreteRightSurvivorSupply D G hne).survivorCD s γ
  rw [resolvedComponentGenTerm_of_cd hCDsurv, resolvedComponentGenTerm_of_cd hCDγ]
  congr 1

/-- **R-6c-leaf-2 — the Product `remnantGen` leaf from a remnant de-contraction family.**  For any remnant
component supply `M` whose components agree with a per-split de-contraction family `Geo`, the de-contraction
`remnantGen` (`= o.rightTermOf`) composed with `rightFactorOf_eq_rightTerm_of_choiceAt_inr` gives the Product
`remnantGen` target `D.rightFactorOf s γ.1`. -/
theorem product_remnantGen_of_decontraction
    (M : ResolvedRemnantComponentSupply D G)
    (Geo : ∀ s : ResolvedCoassocSplitChoice D G, ResolvedRemnantDecontractionSupply D G s)
    (hM : ∀ (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence),
      M.remnantComponent s o = (Geo s).remnantComponent o)
    (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents}) :
    resolvedComponentGenTerm (M.remnantComponent s (s.forestComponentOccurrence γ))
      = D.rightFactorOf s γ.1 := by
  rw [hM s (s.forestComponentOccurrence γ), (Geo s).remnantGen]
  exact (rightFactorOf_eq_rightTerm_of_choiceAt_inr (s.forestComponentOccurrence γ).hchoice).symm

end GaugeGeometry.QFT.Combinatorial
