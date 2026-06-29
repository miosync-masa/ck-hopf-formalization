import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocThreeRouteInverseLaws

/-!
# R-6c-heart-6a-8c-fix-3c-1a — quotient-star round trip (route 3)

The first inverse-law case: a one-stage **right/forest** star round-trips through `corrToFun`/`corrInvFun`
back to itself, by the `quotientStarEquiv` / `twoStarRecover` `Equiv` laws plus the `oneStarRecover_vertex`
agreement.  This is the algebraically-closed case (no surviving / left-star routing).

`corrToFun` on such a vertex takes the star branch, recovers the index, sees `¬ isLeft` (quotient star), and
emits `quotientStarEquiv … |>.toStarVertex`.  `corrInvFun` on that takes the star branch, `twoStarRecover`
inverts `toStarVertex`, `quotientStarEquiv.symm` inverts the forward step, and `oneStarRecover_vertex`
returns the original `VertexId`.

The only extra hypothesis is `twoStarRecover ∘ toStarVertex = id` (the two-stage recovery inverts the
canonical index→vertex map) — supplied here as `htwoInv`; it later comes for free from a concrete
`twoStarRecover` built as `starVertexEquivIndex` (6a-8b-2).

Per the HALT, only the quotient-star case; no surviving / left-star round trips, no concrete
`quotientStarEquiv`, no full `corrLeftInv`.

Landed:

* `threeRouteCorrToFun_quotientStar_val` / `threeRouteCorrInvFun_star_val` — the two dite evaluations;
* `threeRoute_leftInv_quotientStar` — the route-3 left-inverse round trip.

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

/-- **fix-3c-1a — `corrToFun` value on a quotient star.**  In the star + `¬isLeft` branch, the forward map
emits the `quotientStarEquiv` image's star vertex. -/
theorem threeRouteCorrToFun_quotientStar_val (S : ResolvedThreeRouteToFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hstar : isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1)
    (hL : ¬ (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft) :
    (threeRouteCorrToFun S s w).1
      = (S.quotientStarEquiv s ⟨S.oneStarRecover s ⟨w.1, hstar⟩,
          (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft_or_hasQuotientStar.resolve_left hL⟩).toStarVertex.1 := by
  simp only [threeRouteCorrToFun, dif_pos hstar, dif_neg hL]

/-- **fix-3c-1a — `corrInvFun` value on a two-stage star.**  In the star branch, the inverse map emits the
`quotientStarEquiv.symm` image's star vertex. -/
theorem threeRouteCorrInvFun_star_val (S : ResolvedThreeRouteInvFunSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (twoStageContractGraph imageOf s).vertices})
    (hstar : isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest) w.1) :
    (threeRouteCorrInvFun S s w).1
      = ((S.quotientStarEquiv s).symm (S.twoStarRecover s ⟨w.1, hstar⟩)).1.toStarVertex.1 := by
  simp only [threeRouteCorrInvFun, dif_pos hstar]

/-- **fix-3c-1a — the route-3 left-inverse round trip.**  A one-stage right/forest star round-trips to
itself. -/
theorem threeRoute_leftInv_quotientStar (S : ResolvedThreeRouteFullSupply D G imageOf)
    (s : ResolvedCoassocSplitChoice D G) (w : {v : VertexId // v ∈ (oneStageContractGraph s).vertices})
    (hstar : isContractStarVertex s.1.1 (D.starOf G s.1.1) w.1)
    (hL : ¬ (S.oneStarRecover s ⟨w.1, hstar⟩).isLeft)
    (htwoInv : ∀ j : TwoStageStarIndex D G imageOf s,
      S.twoStarRecover s j.toStarVertex = j) :
    threeRouteCorrInvFun S.toResolvedThreeRouteInvFunSupply s
        (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w) = w := by
  -- abbreviations
  set i := S.oneStarRecover s ⟨w.1, hstar⟩ with hi
  set j := S.quotientStarEquiv s ⟨i, i.isLeft_or_hasQuotientStar.resolve_left hL⟩ with hj
  -- the forward output's vertex is j.toStarVertex.1, and it is a two-stage star
  have hfwd : (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1
      = j.toStarVertex.1 :=
    threeRouteCorrToFun_quotientStar_val S.toResolvedThreeRouteToFunSupply s w hstar hL
  have hfwdstar : isContractStarVertex (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)
      (threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1 := by
    rw [hfwd]; exact j.toStarVertex.2
  -- evaluate the inverse on the forward output
  apply Subtype.ext
  rw [threeRouteCorrInvFun_star_val S.toResolvedThreeRouteInvFunSupply s _ hfwdstar]
  -- twoStarRecover recovers j, quotientStarEquiv.symm inverts
  have hrec : S.twoStarRecover s
      ⟨(threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1, hfwdstar⟩ = j := by
    have : (⟨(threeRouteCorrToFun S.toResolvedThreeRouteToFunSupply s w).1, hfwdstar⟩ :
        {v // isContractStarVertex (imageOf s).quotientForest _ v}) = j.toStarVertex :=
      Subtype.ext hfwd
    rw [this, htwoInv]
  rw [hrec, Equiv.symm_apply_apply]
  -- now goal: i.toStarVertex.1 = w.1, i.e. i.vertex = w.1
  exact S.oneStarRecover_vertex s ⟨w.1, hstar⟩

end GaugeGeometry.QFT.Combinatorial
