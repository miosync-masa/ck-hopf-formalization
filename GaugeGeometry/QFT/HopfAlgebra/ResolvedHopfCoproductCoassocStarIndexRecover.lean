import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightStarIndexBijection

/-!
# R-6c-heart-6a-8b-2 — star-vertex subtype ≃ component index, from `starOf` injectivity

The recoveries `oneStarEquiv` / `twoStarEquiv` (6a-8b-1) are both instances of ONE generic fact: if a star
assignment `starOf` is **injective on a forest's components** (distinct components get distinct stars —
no-collision), then the star vertices of `A.contractWithStars` are in bijection with `A`'s components
(`mem_starVertices` gives surjectivity; injectivity gives the inverse).

So this file isolates `starOf` injectivity-on-components as the genuine canonical-star property and builds
the generic equivalence `{v // isContractStarVertex A starOf v} ≃ {η // η ∈ A.elements}` from it, then
re-packages it into the `OneStageStarIndex` / `TwoStageStarIndex` shape, producing a
`ResolvedRightStarIndexBijectionSupply` from the two recoveries plus `indexEquiv`.

Per the HALT, `star_injective_on_elements` is the supply field (the canonical-star property; not proved),
`indexEquiv` is NOT built, no `componentPartition`.

Landed:

* `ResolvedStarIndexRecoverSupply A starOf` — `starOf` injective on `A`'s components;
* `starVertexEquivIndex` — the generic star-vertex ≃ component-subtype equivalence;
* `oneStage*/twoStage* StarIndexEquivSubtype` — the index ↔ component-subtype repackaging;
* `ResolvedRightStarRecoverSupply D G imageOf` + `.toStarIndexBijectionSupply indexEquiv` — the two
  recoveries + `indexEquiv` ⇒ `ResolvedRightStarIndexBijectionSupply`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8b-2 — `starOf` injective on a forest's components (no-collision).**  The canonical
star property behind the star-vertex recovery. -/
structure ResolvedStarIndexRecoverSupply (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) where
  /-- Distinct components of `A` get distinct stars. -/
  star_injective_on_elements : ∀ {η δ : ResolvedFeynmanSubgraph G}, η ∈ A.elements → δ ∈ A.elements →
    starOf η = starOf δ → η = δ

/-- **R-6c-heart-6a-8b-2 — star vertices ≃ components.**  `mem_starVertices` is the surjection; the
no-collision hypothesis is the inverse. -/
noncomputable def starVertexEquivIndex {A : ResolvedAdmissibleSubgraph G}
    {starOf : ResolvedFeynmanSubgraph G → VertexId} (S : ResolvedStarIndexRecoverSupply A starOf) :
    {v : VertexId // isContractStarVertex A starOf v} ≃
      {η : ResolvedFeynmanSubgraph G // η ∈ A.elements} := by
  refine ⟨fun v => ⟨Classical.choose (ResolvedAdmissibleSubgraph.mem_starVertices.mp v.2),
      (Classical.choose_spec (ResolvedAdmissibleSubgraph.mem_starVertices.mp v.2)).1⟩,
    fun η => ⟨starOf η.1, ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨η.1, η.2, rfl⟩⟩, ?_, ?_⟩
  · intro v
    exact Subtype.ext (Classical.choose_spec (ResolvedAdmissibleSubgraph.mem_starVertices.mp v.2)).2
  · intro η
    refine Subtype.ext ?_
    exact S.star_injective_on_elements
      (Classical.choose_spec (ResolvedAdmissibleSubgraph.mem_starVertices.mp
        (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨η.1, η.2, rfl⟩))).1
      η.2
      (Classical.choose_spec (ResolvedAdmissibleSubgraph.mem_starVertices.mp
        (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨η.1, η.2, rfl⟩))).2

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-heart-6a-8b-2 — `OneStageStarIndex` ≃ its component subtype (record repackaging). -/
def oneStageStarIndexEquivSubtype {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G) :
    OneStageStarIndex D G s ≃ {η : ResolvedFeynmanSubgraph G // η ∈ s.1.1.elements} where
  toFun i := ⟨i.η, i.hη⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- **R-6c-heart-6a-8b-2 — `TwoStageStarIndex` ≃ its component subtype (record repackaging). -/
def twoStageStarIndexEquivSubtype {G : ResolvedFeynmanGraph}
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) :
    TwoStageStarIndex D G imageOf s ≃
      {δ : ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)) //
        δ ∈ (imageOf s).quotientForest.elements} where
  toFun i := ⟨i.δ, i.hδ⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

variable {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-8b-2 — the right star-recovery supply.**  Per split choice, `starOf` is injective on
the input outer forest's components and on the quotient forest's components. -/
structure ResolvedRightStarRecoverSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- `D.starOf G s.1.1` is injective on the input outer forest's components. -/
  oneRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedStarIndexRecoverSupply s.1.1 (D.starOf G s.1.1)
  /-- The quotient graph's star is injective on the quotient forest's components. -/
  twoRecover : ∀ s : ResolvedCoassocSplitChoice D G,
    ResolvedStarIndexRecoverSupply (imageOf s).quotientForest
      (D.starOf (resolvedCoassocQuotientGraph (imageOf s)) (imageOf s).quotientForest)

/-- **R-6c-heart-6a-8b-2 — the index-bijection supply from the recoveries + `indexEquiv`.** -/
noncomputable def ResolvedRightStarRecoverSupply.toStarIndexBijectionSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (R : ResolvedRightStarRecoverSupply D G imageOf)
    (indexEquiv : ∀ s : ResolvedCoassocSplitChoice D G,
      OneStageStarIndex D G s ≃ TwoStageStarIndex D G imageOf s) :
    ResolvedRightStarIndexBijectionSupply D G imageOf where
  oneStarEquiv := fun s =>
    (starVertexEquivIndex (R.oneRecover s)).trans (oneStageStarIndexEquivSubtype s).symm
  twoStarEquiv := fun s =>
    (starVertexEquivIndex (R.twoRecover s)).trans (twoStageStarIndexEquivSubtype imageOf s).symm
  indexEquiv := indexEquiv

end GaugeGeometry.QFT.Combinatorial
