import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteRoundTripQuotient

/-!
# R-6c-heart-6a-8c-fix-3c-3a — right-inverse quotient-star case (route 3)

The first `corrRightInv` (`toFun ∘ invFun = id`) case: a two-stage **quotient** star round-trips to itself.
Mirror of the left-inverse quotient case (fix-3c-1a):

```
two-stage quotient star j → corrInvFun: twoStarRecover j → quotientStarEquiv.symm → one-stage right/forest star
  → corrToFun: oneStarRecover recovers it → ¬isLeft → quotientStarEquiv back → j
```

The forward step's `¬ isLeft` comes from the recovered index's `hasQuotientStar` (disjoint from `isLeft` by
5b-1).  Hypotheses: `htwoInv` (`twoStarRecover (j.toStarVertex) = j`) and `honeInv`
(`oneStarRecover ∘ toStarVertex = id`) — both free from the concrete recoveries (6a-8b-2).

Per the HALT, only the quotient-star right-inverse case; no survivor cases, no full `corrRightInv`.

Landed:

* `threeRoute_rightInv_quotientStar` — the route-3 right-inverse round trip (on `j.toStarVertex`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **fix-3c-3a — the route-3 right-inverse round trip.**  A two-stage quotient star round-trips to itself. -/
theorem threeRoute_rightInv_quotientStar (S : ResolvedThreeRouteInverseLawSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (j : TwoStageStarIndex D G imageOf s)
    (htwoInv : S.route.twoStarRecover s j.toStarVertex = j)
    (honeInv : ∀ i : OneStageStarIndex D G s, S.route.oneStarRecover s i.toStarVertex = i) :
    threeRouteCorrToFun S.route.toResolvedThreeRouteToFunSupply s
        (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s
          ⟨j.vertex, star_mem_contractWithStars (imageOf s).quotientForest
            (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
            j.toStarVertex.2⟩)
      = ⟨j.vertex, star_mem_contractWithStars (imageOf s).quotientForest
          (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
          j.toStarVertex.2⟩ := by
  set w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices} :=
    ⟨j.vertex, star_mem_contractWithStars (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      j.toStarVertex.2⟩ with hw
  have hstar : isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1 :=
    j.toStarVertex.2
  -- the inverse recovers k = (quotientStarEquiv).symm j
  have hwj : (⟨w.1, hstar⟩ : {v : VertexId // isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) v})
      = j.toStarVertex := Subtype.ext rfl
  have hinv : (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1
      = ((S.route.quotientStarEquiv s).symm j).1.toStarVertex.1 := by
    rw [threeRouteCorrInvFun_star_val S.route.toResolvedThreeRouteInvFunSupply s w hstar, hwj, htwoInv]
  set k := (S.route.quotientStarEquiv s).symm j with hk
  have hinvstar : isContractStarVertex s.1.1 (D.starOf G s.1.1)
      (threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1 := by
    rw [hinv]; exact k.1.toStarVertex.2
  have hrec : S.route.oneStarRecover s
      ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hinvstar⟩ = k.1 := by
    have he : (⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hinvstar⟩ :
        {v : VertexId // isContractStarVertex s.1.1 (D.starOf G s.1.1) v}) = k.1.toStarVertex :=
      Subtype.ext hinv
    rw [he, honeInv]
  have hnotleft : ¬ (S.route.oneStarRecover s
      ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hinvstar⟩).isLeft := by
    rw [hrec]
    exact fun hLeft => k.2.elim (fun hR => s.not_isRightPrimitive_of_isLeftPrimitive hLeft hR)
      (fun hF => s.not_isForestChoice_of_isLeftPrimitive hLeft hF)
  apply Subtype.ext
  rw [threeRouteCorrToFun_quotientStar_val S.route.toResolvedThreeRouteToFunSupply s _ hinvstar hnotleft]
  have hidx : (⟨S.route.oneStarRecover s
      ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hinvstar⟩,
      (S.route.oneStarRecover s
        ⟨(threeRouteCorrInvFun S.route.toResolvedThreeRouteInvFunSupply s w).1, hinvstar⟩).isLeft_or_hasQuotientStar.resolve_left hnotleft⟩
      : {i : OneStageStarIndex D G s // i.hasQuotientStar}) = k := Subtype.ext hrec
  rw [hidx, hk, Equiv.apply_symm_apply]
  rfl

end GaugeGeometry.QFT.Combinatorial
