import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientDisjointConcrete

/-!
# R-6c-body-2 — quotient vertex-cross from a separating region

Second genuine-body step.  `ResolvedQuotientForestVertexCrossSupply.vertex_cross` (leaf-12) — the unconditional
vertex-disjointness of the remnant forest elements from the right-survivor forest elements (which then powers
the Product `hCross` and `hDisj`) — is reduced to a REGION SEPARATION: a separating vertex set that the remnant
components lie inside and the survivor components avoid.

`γ.Disjoint δ = Disjoint γ.vertices δ.vertices`, so `γ.vertices ⊆ separator` and `Disjoint δ.vertices separator`
give `Disjoint γ.vertices δ.vertices` (`Finset.disjoint_of_subset_left … .symm`).  The natural separator is the
outer-star region: remnant components (de-contracted forest pieces) sit at the stars, survivors avoid them
(cf. the 5b-4 `remnantTouches` / `rightAvoidsStars`) — but the exact `⊆` / `Disjoint` witnesses are genuine
geometry, kept as the supply's fields.

Per the HALT, `survivor_avoids` / `remnant_subset` are supply fields (the region geometry); no `occurrence_inj`;
Transport / Perm untouched.

Landed:

* `ResolvedVertexCrossRegionSupply D G R M` — `separator` + `survivor_avoids` + `remnant_subset`;
* `.toQuotientForestVertexCrossSupply` — the leaf-12 `vertex_cross` supply.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-2 — the quotient vertex-cross region supply.**  A separating vertex set: remnant components lie
inside it, survivor components avoid it. -/
structure ResolvedVertexCrossRegionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- The separating vertex set (the outer-star region). -/
  separator : ResolvedCoassocSplitChoice D G → Finset VertexId
  /-- Right survivors avoid the separator. -/
  survivor_avoids : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ δ ∈ (R.rightSurvivorForest s).elements, Disjoint δ.vertices (separator s)
  /-- Remnants lie inside the separator. -/
  remnant_subset : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ ∈ (M.remnantForest s).elements, γ.vertices ⊆ separator s

/-- **R-6c-body-2 — the leaf-12 vertex-cross supply from the region separation. -/
def ResolvedVertexCrossRegionSupply.toQuotientForestVertexCrossSupply
    {R : ResolvedRightSurvivorSupply D G} {M : ResolvedRemnantComponentSupply D G}
    (S : ResolvedVertexCrossRegionSupply D G R M) :
    ResolvedQuotientForestVertexCrossSupply D G R M where
  vertex_cross := fun s γ hγ δ hδ =>
    Finset.disjoint_of_subset_left (S.remnant_subset s γ hγ) (S.survivor_avoids s δ hδ).symm

end GaugeGeometry.QFT.Combinatorial
