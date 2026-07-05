import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingMapsTo
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-150 — region star facts: the two `toFun_mem` star facts from survivor/remnant vs the star

Hundred-and-fiftieth genuine-body step, the first concrete region-geometry leaf.  Body-132's two star facts
(`mixed_avoids_star` / `forest_touches_star`) — the forward-map classifiers feeding `toFun_mem` — are reduced to
local facts about the quotient forest's components versus the outer star.  The **mixed** fact is proved fully from
the survivor/remnant region facts (survivors avoid the star, the remnant is empty in the mixed case) via the
summand bundle's `union_eq`; the **forest** fact is reduced to a quotient-level touching component.

## The reduction

`resolvedIsForestImage A B := ∃ δ ∈ B.1.elements, ¬ Disjoint δ.vertices (A.1.starVertices …)` — "some component of
`B` touches `A`'s star".  With the quotient forest `B = rightSurvivor ⊔ remnant` (the summand bundle's `union_eq`):

* **mixed** (`¬ resolvedIsForestImage`): given `survivor_avoids` (every survivor component is `Disjoint` from the
  star) and `mixed_remnant_empty` (the remnant is empty in the mixed case), every component of `B` is a survivor
  and avoids the star, so **no** component touches — `mixed_avoids_star` is PROVED (destruct the `union_eq`
  membership, kill the empty remnant);
* **forest** (`resolvedIsForestImage`): a touching component of `B` is exactly the witness — `forest_touches_star`
  is `forest_quotient_touch` verbatim (the definition of `resolvedIsForestImage`).

The forest touching component further reduces to `remnant_touches` (a remnant component meets the star) at a
nonempty remnant — the mirror of the mixed reduction — but the `∪`-membership *construction* on the quotient carrier
hits a `Finset` `DecidableEq` instance diamond (the union's baked-in instance vs the ambient one), so the
touching-component is fielded at the quotient level here; its remnant origin is named.

## The supply

`ResolvedRegionStarFactSupply D S` fields the survivor/remnant region facts (`survivor_avoids`,
`mixed_remnant_empty`, `forest_quotient_touch`); `.mixed_avoids_star` / `.forest_touches_star` prove body-132's two
star facts, and `.toOuterMixingMapsToSupply` bundles them into `ResolvedOuterMixingMapsToSupply` (→ the two
`toFun_mem` membership fields, body-132).  So the `toFun_mem` classifier side of the bijection is now a local
star-geometry fact.

Per the HALT: the mixed fact is proved from the region facts (`survivor_avoids` + `mixed_remnant_empty` via
`union_eq`); the forest touching component is fielded (its remnant origin named), not forced through the `∪`
instance diamond; no inverse-law content is entered.

Landed:

* `ResolvedRegionStarFactSupply D S` — the survivor/remnant vs star region facts;
* `.mixed_avoids_star` (PROVED from the region facts) / `.forest_touches_star`;
* `.toOuterMixingMapsToSupply` — body-132's maps-to supply (→ `toFun_mem`).

Toolkit body (like body-146).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-150 — the region star-fact supply.**  The survivor/remnant vs outer-star facts: survivors avoid
the star, the remnant is empty in the mixed case, and a forest case's quotient forest has a touching component. -/
structure ResolvedRegionStarFactSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- Every right-survivor component avoids the outer star. -/
  survivor_avoids : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ∀ δ ∈ (S.Survivor.survivor.rightSurvivorForest q).elements,
      Disjoint δ.vertices (((S.Forward.imageSupply G).selectedOuterOf q).1.starVertices
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf q).1))
  /-- In the mixed case the remnant is empty (the quotient forest is survivors only). -/
  mixed_remnant_empty : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    q ∈ mixedDomFinset G → (S.Remnant.remnant.remnantForest q).elements = ∅
  /-- In the forest case the quotient forest has a component touching the outer star (its remnant origin). -/
  forest_quotient_touch : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    q ∈ forestCarryingDomFinset G →
    ∃ δ ∈ (S.quotientForest q).1.elements,
      ¬ Disjoint δ.vertices (((S.Forward.imageSupply G).selectedOuterOf q).1.starVertices
        (D.starOf G ((S.Forward.imageSupply G).selectedOuterOf q).1))

namespace ResolvedRegionStarFactSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-150 — body-132's `mixed_avoids_star` from the region facts.**  The quotient forest is survivors
only (mixed ⇒ remnant empty), and survivors avoid the star, so no component touches it. -/
theorem mixed_avoids_star (R : ResolvedRegionStarFactSupply D S) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G) :
    ¬ resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q) := by
  rintro ⟨δ, hδ, htouch⟩
  rw [S.union_eq q] at hδ
  simp only [ResolvedAdmissibleSubgraph.union_elements, R.mixed_remnant_empty q hq,
    Finset.union_empty] at hδ
  exact htouch (R.survivor_avoids q δ hδ)

/-- **R-6c-body-150 — body-132's `forest_touches_star` from the region facts.**  The forest case's quotient forest
has a touching (remnant) component — exactly a `resolvedIsForestImage` witness. -/
theorem forest_touches_star (R : ResolvedRegionStarFactSupply D S) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) (hq : q ∈ forestCarryingDomFinset G) :
    resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q) :=
  R.forest_quotient_touch q hq

/-- **R-6c-body-150 — body-132's maps-to supply from the region star facts** (→ the two `toFun_mem` fields). -/
def toOuterMixingMapsToSupply (R : ResolvedRegionStarFactSupply D S) :
    ResolvedOuterMixingMapsToSupply D S where
  mixed_avoids_star := fun {G} q hq => R.mixed_avoids_star q hq
  forest_touches_star := fun {G} q hq => R.forest_touches_star q hq

end ResolvedRegionStarFactSupply

end GaugeGeometry.QFT.Combinatorial
