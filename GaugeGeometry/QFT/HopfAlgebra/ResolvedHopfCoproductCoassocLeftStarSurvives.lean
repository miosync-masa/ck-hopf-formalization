import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTransportLeaves

/-!
# R-6c-body-10 — left-primitive stars survive stage 2 (reduced to mem + not-mem)

Tenth genuine-body step, the mismatch-fix core of the LEFT route (6a-8c-0): a left-primitive one-stage
`δ`-star is a two-stage SURVIVOR (it is not re-contracted by the quotient forest).

`isContractSurvivingVertex (imageOf s).quotientForest v = v ∈ (resolvedCoassocQuotientGraph (imageOf s)).vertices
∧ v ∉ (imageOf s).quotientForest.vertices`, so `left_star_toSurvivor` is exactly the conjunction of:

* `left_star_mem_quotientGraph` — the left `δ`-star is a vertex of the quotient (contract) graph (it is a
  selected-outer star, which survives into the contract graph);
* `left_star_not_mem_quotientForest` — the left `δ`-star is NOT in the quotient forest (the quotient forest is
  `Right ⊔ Remnant`; a left star is neither a right-survivor vertex nor a remnant vertex — this is exactly the
  6a-8c-0 correction that left stars are NOT re-contracted).

Both are genuine vertex-region geometry, kept as supply fields.

Per the HALT, the two facts are supply fields; `two_stage_survivor_split` untouched.

Landed:

* `ResolvedLeftStarSurvivalSupply D G imageOf` — `left_star_mem_quotientGraph` + `left_star_not_mem_quotientForest`;
* `.left_star_toSurvivor` — the Transport left-route fact.

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

/-- **R-6c-body-10 — the left-star survival supply.**  The left `δ`-star is a quotient-graph vertex not in the
quotient forest. -/
structure ResolvedLeftStarSurvivalSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- A left-primitive `δ`-star is a vertex of the quotient (contract) graph. -/
  left_star_mem_quotientGraph : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → i.vertex ∈ (resolvedCoassocQuotientGraph (imageOf s)).vertices
  /-- A left-primitive `δ`-star is NOT in the quotient forest (the 6a-8c-0 correction). -/
  left_star_not_mem_quotientForest : ∀ (s : ResolvedCoassocSplitChoice D G) (i : OneStageStarIndex D G s),
    i.isLeft → i.vertex ∉ (imageOf s).quotientForest.vertices

/-- **R-6c-body-10 — the Transport left-route fact (`left_star_toSurvivor`). -/
theorem ResolvedLeftStarSurvivalSupply.left_star_toSurvivor
    (S : ResolvedLeftStarSurvivalSupply D G imageOf) (s : ResolvedCoassocSplitChoice D G)
    (i : OneStageStarIndex D G s) (hL : i.isLeft) :
    isContractSurvivingVertex (imageOf s).quotientForest i.vertex :=
  ⟨S.left_star_mem_quotientGraph s i hL, S.left_star_not_mem_quotientForest s i hL⟩

end GaugeGeometry.QFT.Combinatorial
