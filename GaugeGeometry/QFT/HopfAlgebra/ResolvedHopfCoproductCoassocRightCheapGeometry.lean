import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFinalGeometryData

/-!
# R-6c-heart-6a-6b — cheap RIGHT geometry pieces (the light stones)

Before the genuine `starToStar` / `retargetVertex_eq` / `edge_domain_eq` (6a-6a scout), the CONCRETE and
CHEAP `FinalGeometryData` inputs for the right factor:

1. **`vertexDomain`** — CONCRETE: `rightVertexDomain z = z.selectedOuter.1.retargetVertex (D.starOf G
   z.selectedOuter.1)`, the stage-1 contract map `G → resolvedCoassocQuotientGraph z`.
2. **`leg_domain_eq`** — PROVED (`≈ rfl`): legs are never deleted by `contractWithStars`, so the quotient
   graph's legs are exactly the ambient legs retargeted through `vertexDomain`.  Generic lemma
   `contractWithStars_externalLegs_eq_retarget` + its right instance `right_leg_domain_eq`.
3. **`freshA` / `freshB`** — bundled honest supply.  SCOUT CORRECTION: `ResolvedCoproductProperForestData`
   carries NO star-freshness field (only `carrier`/`starOf`/`hCD`/`carrier_mapPerm`/`star_mapPerm`), so
   freshness is NOT derivable from `D` — it is a genuine obligation, isolated here as
   `ResolvedRightStarFreshSupply` (mirrors how heart-3 `starFreshOf` is a supply field).

Per the HALT, `starToStar`, `retargetVertex_eq`, `edge_domain_eq`, `surviving_to/from` are NOT touched.

Landed:

* `ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_eq_retarget` — generic (legs all retargeted);
* `rightVertexDomain` + `right_leg_domain_eq` — the concrete `vertexDomain` and its proved `leg_domain_eq`;
* `ResolvedRightStarFreshSupply D G imageOf` — the `freshA` / `freshB` obligations, bundled.

No facade, no flat term, no `forgetHopf`.  After this the right side's remaining work is
`starToStar` / `surviving_to/from` / `permExt` / `retargetVertex_eq` / `edge_domain_eq`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-6b — `contractWithStars` legs are all retargets.**  External legs are never deleted
(only retargeted), so the contracted graph's legs are exactly the ambient legs retargeted through the
vertex map.  This is the engine behind the cheap `leg_domain_eq`. -/
theorem ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_eq_retarget
    (Sel : ResolvedAdmissibleSubgraph G) (starSel : ResolvedFeynmanSubgraph G → VertexId) :
    (Sel.contractWithStars starSel).externalLegs
      = G.externalLegs.map (fun ℓ => ℓ.retarget (Sel.retargetVertex starSel)) := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-heart-6a-6b — the concrete `vertexDomain` for the right factor.**  The stage-1 contract map
`G → resolvedCoassocQuotientGraph z` (`selectedOuter` retargeted to its stars). -/
noncomputable def rightVertexDomain (z : ResolvedCoassocQuotientImage D G) : VertexId → VertexId :=
  z.selectedOuter.1.retargetVertex (D.starOf G z.selectedOuter.1)

/-- **R-6c-heart-6a-6b — the proved `leg_domain_eq` for the right factor.**  The ambient legs retargeted
through `rightVertexDomain` are exactly the quotient graph's legs. -/
theorem right_leg_domain_eq (z : ResolvedCoassocQuotientImage D G) :
    G.externalLegs.map (fun ℓ => ℓ.retarget (rightVertexDomain z))
      = (resolvedCoassocQuotientGraph z).externalLegs := by
  unfold rightVertexDomain resolvedCoassocQuotientGraph
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs_eq_retarget]

/-- **R-6c-heart-6a-6b — the right-factor star-freshness supply (honest obligation).**  `D` carries no
star-freshness field, so the `freshA` / `freshB` that `ResolvedContractStarMapSupply` needs are isolated
here: the input outer `s.1.1`'s stars are fresh in `G`, and the quotient forest's stars are fresh in the
quotient graph. -/
structure ResolvedRightStarFreshSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The input outer forest's stars are fresh (outside `G`). -/
  freshA : ∀ s : ResolvedCoassocSplitChoice D G, ∀ η ∈ s.1.1.elements,
    D.starOf G s.1.1 η ∉ G.vertices
  /-- The quotient forest's stars are fresh (outside the quotient graph). -/
  freshB : ∀ s : ResolvedCoassocSplitChoice D G, ∀ η ∈ (imageOf s).quotientForest.elements,
    D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest η
      ∉ (resolvedCoassocQuotientGraph (imageOf s)).vertices

end GaugeGeometry.QFT.Combinatorial
