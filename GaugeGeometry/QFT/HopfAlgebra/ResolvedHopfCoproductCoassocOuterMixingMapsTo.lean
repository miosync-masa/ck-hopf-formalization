import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBijectionProvider

/-!
# R-6c-body-132 — outer-mixing maps-to classifiers: `toFun_mem` reduced to the star-touch predicate

Hundred-and-thirty-second genuine-body step, closing the lighter half of the bijection provider's classification.
The two forward-membership fields `mixed_toFun_mem` / `forest_toFun_mem` (body-131) are pure `Finset.sigma`
plumbing over the codomain carriers, and they reduce to EXACTLY the star-touch classifier `resolvedIsForestImage`:
a mixed-boundary choice's quotient forest must AVOID the outer star, a forest-carrying choice's must TOUCH it.

## The reduction (PROVED)

`mixedCodFinset` / `forestCarryingCodFinset` are `(D.carrier G).attach.sigma (fun A => forestCarrier.filter …)`
with `forestCarrier = (D.carrier _).attach`; the codomain forest `⟨selectedOuterOf q, quotientForest q⟩` always
lies in the `attach`-sigma, so `Finset.mem_sigma` + `Finset.mem_filter` + `Finset.mem_attach` collapse the
membership to the single filter predicate:

* `mixed_toFun_mem_of_avoids`: from `¬ resolvedIsForestImage (selectedOuterOf q) (quotientForest q)`;
* `forest_toFun_mem_of_touches`: from `resolvedIsForestImage (selectedOuterOf q) (quotientForest q)`.

`resolvedIsForestImage A B := ∃ δ ∈ B.1.elements, ¬ Disjoint δ.vertices (A.1.starVertices (starOf G A.1))` —
"some component of `B` touches the outer star" (body-102, the resolved port of flat `isForestByStar`).

## The two star facts (fielded)

The genuine content is the two forward star facts — that the forward map sends a mixed-boundary choice to a
star-AVOIDING quotient forest and a forest-carrying choice to a star-TOUCHING one.  These are geometric properties
of the (abstract) `quotientForest` against the choice class, so they are exposed as `ResolvedOuterMixingMapsToSupply`
fields; the forest touch is the remnant-touches-star fact (a remnant component, being a de-contracted forest
choice, meets the star), the mixed avoidance is the survivor-avoids-star fact (a right-survivor component, being a
star-avoiding primitive, misses it) with the remnant empty in the mixed class.

`.toBijectionProviderMapsTo` fills the provider's two `toFun_mem` fields from the two star facts; the remaining
seven bijection fields (`invConstruct` + the six membership/inverse laws) are untouched.

Per the HALT: `invConstruct` is not constructed; the two `toFun_mem` are reduced to the star classifier; the star
facts are exposed as exact fields (`mixed_avoids_star` / `forest_touches_star`).

Landed:

* `mixed_toFun_mem_of_avoids` / `forest_toFun_mem_of_touches` — the `Finset.sigma` reduction to the classifier;
* `ResolvedOuterMixingMapsToSupply D S` — the two forward star facts;
* `.mixed_toFun_mem` / `.forest_toFun_mem` — the provider's two `toFun_mem` fields.

Toolkit body (like body-131), one small supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-132 — mixed `toFun_mem` from star avoidance.**  The `Finset.sigma` membership collapses to the
single filter predicate `¬ resolvedIsForestImage`. -/
theorem mixed_toFun_mem_of_avoids (S : ResolvedConcreteSummandBundleSupply D)
    (q : ForestBlockDomType D G)
    (hAvoid : ¬ resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q)) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G := by
  rw [mixedCodFinset, Finset.mem_sigma]
  exact ⟨Finset.mem_attach _ _, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hAvoid⟩⟩

/-- **R-6c-body-132 — forest `toFun_mem` from star touch.**  The `Finset.sigma` membership collapses to the single
filter predicate `resolvedIsForestImage`. -/
theorem forest_toFun_mem_of_touches (S : ResolvedConcreteSummandBundleSupply D)
    (q : ForestBlockDomType D G)
    (hTouch : resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q)) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G := by
  rw [forestCarryingCodFinset, Finset.mem_sigma]
  exact ⟨Finset.mem_attach _ _, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hTouch⟩⟩

/-- **R-6c-body-132 — the outer-mixing maps-to supply.**  The two forward star facts against a fixed summand
bundle `S`: a mixed-boundary choice's quotient forest avoids the outer star, a forest-carrying choice's touches
it. -/
structure ResolvedOuterMixingMapsToSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- A mixed-boundary choice's quotient forest avoids the outer star (survivor-only, remnant empty). -/
  mixed_avoids_star : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    ¬ resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q)
  /-- A forest-carrying choice's quotient forest touches the outer star (a remnant component meets it). -/
  forest_touches_star : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    resolvedIsForestImage ((S.Forward.imageSupply G).selectedOuterOf q) (S.quotientForest q)

/-- **R-6c-body-132 — the provider's mixed `toFun_mem` from the maps-to supply.** -/
theorem ResolvedOuterMixingMapsToSupply.mixed_toFun_mem {S : ResolvedConcreteSummandBundleSupply D}
    (M : ResolvedOuterMixingMapsToSupply D S) (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ mixedDomFinset G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G :=
  mixed_toFun_mem_of_avoids S q (M.mixed_avoids_star q hq)

/-- **R-6c-body-132 — the provider's forest `toFun_mem` from the maps-to supply.** -/
theorem ResolvedOuterMixingMapsToSupply.forest_toFun_mem {S : ResolvedConcreteSummandBundleSupply D}
    (M : ResolvedOuterMixingMapsToSupply D S) (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G :=
  forest_toFun_mem_of_touches S q (M.forest_touches_star q hq)

end GaugeGeometry.QFT.Combinatorial
