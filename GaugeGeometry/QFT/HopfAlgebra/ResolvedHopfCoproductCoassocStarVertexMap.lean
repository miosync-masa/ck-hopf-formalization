import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarVertexPartition

/-!
# R-6c-heart-6a-5c-2b — the star-vertex map + the vertex correspondence

The contract-twice vertex bijection (6a-5c-1) is now built from the **surviving = identity, star = supply
bijection** form.  `ResolvedContractStarMapSupply` carries the star-to-star bijection (and the surviving
membership transport, and star freshness) as supply fields; `contractVertexToFun`/`InvFun` are the clean
surviving/star case split (6a-5c-2a); and `.toVertexCorrespondence` assembles the
`ResolvedContractTwiceVertexCorrespondence` — its inverse laws follow from the star bijection's inverse
laws plus the surviving/star disjointness (from freshness).

Per the HALT, `starToStar`'s concrete definition and `surviving_to`'s proof are **not** done — they are
supply fields; only the case-split assembly and its inverse laws are proved.

Landed:

* `surviving_mem_contractWithStars` / `star_mem_contractWithStars` — surviving/star ⇒ contract-graph
  membership;
* `ResolvedContractStarMapSupply` — star bijection + surviving transport + freshness (supply fields);
* `contractVertexToFun` / `contractVertexInvFun` (+ value lemmas) — the surviving/star case split;
* `.toVertexCorrespondence` — the assembled `ResolvedContractTwiceVertexCorrespondence`.

No facade, no flat term, no `forgetHopf`.  Constructing `starToStar` / `surviving_to` (and the field
equalities) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {GA QB : ResolvedFeynmanGraph}

/-- A surviving vertex lies in the contract graph. -/
theorem surviving_mem_contractWithStars (A : ResolvedAdmissibleSubgraph GA)
    (starOf : ResolvedFeynmanSubgraph GA → VertexId) {v : VertexId}
    (h : isContractSurvivingVertex A v) : v ∈ (A.contractWithStars starOf).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr h)

/-- A star vertex lies in the contract graph. -/
theorem star_mem_contractWithStars (A : ResolvedAdmissibleSubgraph GA)
    (starOf : ResolvedFeynmanSubgraph GA → VertexId) {v : VertexId}
    (h : isContractStarVertex A starOf v) : v ∈ (A.contractWithStars starOf).vertices := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices]
  exact Finset.mem_union_right _ h

/-- **R-6c-heart-6a-5c-2b — the star-vertex map supply.**  The de-contraction star bijection (one-stage
stars ↔ two-stage stars), the surviving membership transport (both ways), and star freshness — all supply
fields. -/
structure ResolvedContractStarMapSupply
    (A : ResolvedAdmissibleSubgraph GA) (starA : ResolvedFeynmanSubgraph GA → VertexId)
    (B : ResolvedAdmissibleSubgraph QB) (starB : ResolvedFeynmanSubgraph QB → VertexId) where
  /-- `A`'s stars are fresh (outside `GA`). -/
  freshA : ∀ η ∈ A.elements, starA η ∉ GA.vertices
  /-- `B`'s stars are fresh (outside `QB`). -/
  freshB : ∀ η ∈ B.elements, starB η ∉ QB.vertices
  /-- A surviving vertex of the one-stage contraction is surviving in the two-stage. -/
  surviving_to : ∀ {v}, isContractSurvivingVertex A v → isContractSurvivingVertex B v
  /-- A surviving vertex of the two-stage contraction is surviving in the one-stage. -/
  surviving_from : ∀ {w}, isContractSurvivingVertex B w → isContractSurvivingVertex A w
  /-- One-stage star ↦ two-stage star. -/
  starToStar : {v : VertexId // isContractStarVertex A starA v}
    → {w : VertexId // isContractStarVertex B starB w}
  /-- Two-stage star ↦ one-stage star. -/
  starFromStar : {w : VertexId // isContractStarVertex B starB w}
    → {v : VertexId // isContractStarVertex A starA v}
  /-- The star map's inverse laws. -/
  star_left_inv : Function.LeftInverse starFromStar starToStar
  star_right_inv : Function.RightInverse starFromStar starToStar

variable {A : ResolvedAdmissibleSubgraph GA} {starA : ResolvedFeynmanSubgraph GA → VertexId}
  {B : ResolvedAdmissibleSubgraph QB} {starB : ResolvedFeynmanSubgraph QB → VertexId}

/-- **R-6c-heart-6a-5c-2b — the forward vertex map.**  Surviving ↦ itself, star ↦ `starToStar`. -/
noncomputable def contractVertexToFun (M : ResolvedContractStarMapSupply A starA B starB)
    (v : {v : VertexId // v ∈ (A.contractWithStars starA).vertices}) :
    {w : VertexId // w ∈ (B.contractWithStars starB).vertices} :=
  if h : isContractStarVertex A starA v.1 then
    ⟨(M.starToStar ⟨v.1, h⟩).1, star_mem_contractWithStars B starB (M.starToStar ⟨v.1, h⟩).2⟩
  else
    ⟨v.1, surviving_mem_contractWithStars B starB
      (M.surviving_to ((contractWithStars_vertex_cases A starA v.2).resolve_right h))⟩

/-- **R-6c-heart-6a-5c-2b — the inverse vertex map.**  Surviving ↦ itself, star ↦ `starFromStar`. -/
noncomputable def contractVertexInvFun (M : ResolvedContractStarMapSupply A starA B starB)
    (w : {w : VertexId // w ∈ (B.contractWithStars starB).vertices}) :
    {v : VertexId // v ∈ (A.contractWithStars starA).vertices} :=
  if h : isContractStarVertex B starB w.1 then
    ⟨(M.starFromStar ⟨w.1, h⟩).1, star_mem_contractWithStars A starA (M.starFromStar ⟨w.1, h⟩).2⟩
  else
    ⟨w.1, surviving_mem_contractWithStars A starA
      (M.surviving_from ((contractWithStars_vertex_cases B starB w.2).resolve_right h))⟩

theorem contractVertexToFun_val_star (M : ResolvedContractStarMapSupply A starA B starB)
    (v : {v : VertexId // v ∈ (A.contractWithStars starA).vertices})
    (h : isContractStarVertex A starA v.1) :
    (contractVertexToFun M v).1 = (M.starToStar ⟨v.1, h⟩).1 := by
  simp only [contractVertexToFun, dif_pos h]

theorem contractVertexToFun_val_surviving (M : ResolvedContractStarMapSupply A starA B starB)
    (v : {v : VertexId // v ∈ (A.contractWithStars starA).vertices})
    (h : ¬ isContractStarVertex A starA v.1) : (contractVertexToFun M v).1 = v.1 := by
  simp only [contractVertexToFun, dif_neg h]

theorem contractVertexInvFun_val_star (M : ResolvedContractStarMapSupply A starA B starB)
    (w : {w : VertexId // w ∈ (B.contractWithStars starB).vertices})
    (h : isContractStarVertex B starB w.1) :
    (contractVertexInvFun M w).1 = (M.starFromStar ⟨w.1, h⟩).1 := by
  simp only [contractVertexInvFun, dif_pos h]

theorem contractVertexInvFun_val_surviving (M : ResolvedContractStarMapSupply A starA B starB)
    (w : {w : VertexId // w ∈ (B.contractWithStars starB).vertices})
    (h : ¬ isContractStarVertex B starB w.1) : (contractVertexInvFun M w).1 = w.1 := by
  simp only [contractVertexInvFun, dif_neg h]

/-- **R-6c-heart-6a-5c-2b — the vertex correspondence.**  Assembles `contractVertexToFun`/`InvFun` into
`ResolvedContractTwiceVertexCorrespondence`; the inverse laws follow from the star bijection's inverse
laws plus surviving/star disjointness (freshness). -/
noncomputable def ResolvedContractStarMapSupply.toVertexCorrespondence
    (M : ResolvedContractStarMapSupply A starA B starB) :
    ResolvedContractTwiceVertexCorrespondence (A.contractWithStars starA)
      (B.contractWithStars starB) where
  toFun := contractVertexToFun M
  invFun := contractVertexInvFun M
  left_inv := fun v => Subtype.ext (by
    by_cases h : isContractStarVertex A starA v.1
    · have hw : isContractStarVertex B starB (contractVertexToFun M v).1 :=
        contractVertexToFun_val_star M v h ▸ (M.starToStar ⟨v.1, h⟩).2
      rw [contractVertexInvFun_val_star M _ hw,
        show (⟨(contractVertexToFun M v).1, hw⟩ : {w : VertexId // isContractStarVertex B starB w})
          = M.starToStar ⟨v.1, h⟩ from Subtype.ext (contractVertexToFun_val_star M v h),
        M.star_left_inv ⟨v.1, h⟩]
    · have hsurvB : isContractSurvivingVertex B (contractVertexToFun M v).1 :=
        contractVertexToFun_val_surviving M v h ▸
          M.surviving_to ((contractWithStars_vertex_cases A starA v.2).resolve_right h)
      rw [contractVertexInvFun_val_surviving M _
        (fun hs => contract_surviving_not_star B starB M.freshB hsurvB hs),
        contractVertexToFun_val_surviving M v h])
  right_inv := fun w => Subtype.ext (by
    by_cases h : isContractStarVertex B starB w.1
    · have hv : isContractStarVertex A starA (contractVertexInvFun M w).1 :=
        contractVertexInvFun_val_star M w h ▸ (M.starFromStar ⟨w.1, h⟩).2
      rw [contractVertexToFun_val_star M _ hv,
        show (⟨(contractVertexInvFun M w).1, hv⟩ : {v : VertexId // isContractStarVertex A starA v})
          = M.starFromStar ⟨w.1, h⟩ from Subtype.ext (contractVertexInvFun_val_star M w h),
        M.star_right_inv ⟨w.1, h⟩]
    · have hsurvA : isContractSurvivingVertex A (contractVertexInvFun M w).1 :=
        contractVertexInvFun_val_surviving M w h ▸
          M.surviving_from ((contractWithStars_vertex_cases B starB w.2).resolve_right h)
      rw [contractVertexToFun_val_surviving M _
        (fun hs => contract_surviving_not_star A starA M.freshA hsurvA hs),
        contractVertexInvFun_val_surviving M w h])

end GaugeGeometry.QFT.Combinatorial
