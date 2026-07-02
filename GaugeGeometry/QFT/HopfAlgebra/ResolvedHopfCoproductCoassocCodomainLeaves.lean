import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCodomainConcrete

/-!
# R-6c-leaf-15 — Codomain `quotientForest_elements_eq` + `forests_disjoint` from a star filter

Eleventh leaf-body discharge, on the RIGHT side.  The two `ResolvedCodomainConcreteSupply` fields (6a-10d)
are exactly the two halves of a `Finset` filter split: the right-survivor forest is the star-*avoiding*
part of the quotient forest, the remnant forest the star-*touching* part (cf. `ActualSigmaCover` where
`rightComponents := Q.elements.filter (Disjoint · V)`, `remnantComponents := Q.elements.filter (¬ ·)`).

Given the two forests are the `P` / `¬P` filters of `(imageOf s).quotientForest.elements` (the residual star
separator `P`), BOTH fields fall to standard `Finset` lemmas:

* `quotientForest_elements_eq` — `Finset.filter_union_filter_not_eq` (the two filters recover the whole set);
* `forests_disjoint` — `Finset.disjoint_filter_filter_not` (`P` and `¬P` filters are disjoint).

`resolvedCoassocQuotientGraph z = z.selectedOuter.1.contractWithStars …` (ImageWeight) is definitionally the
ambient of `z.quotientForest`, so the filter over `quotientForest.elements` lands in the Codomain forests' type.

Per the HALT, the star-separator filter shape (`hright` / `hremnant`) is a hypothesis (the genuine
`remnantTouches` / `rightAvoidsStars` geometry, 5b-4); Sector / Transport / Perm / Edge untouched.

Landed:

* `codomain_quotientForest_elements_eq_of_star_filter`;
* `codomain_forests_disjoint_of_star_filter`.

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

/-- **R-6c-leaf-15 — the Codomain `quotientForest_elements_eq` field from the star-filter shape.**  The
right / remnant forests are the `P` / `¬P` filters of the quotient forest, so their union is the whole set. -/
theorem codomain_quotientForest_elements_eq_of_star_filter
    (rightForest remnantForest : ∀ s : ResolvedCoassocSplitChoice D G,
      ResolvedAdmissibleSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
    (P : ∀ s : ResolvedCoassocSplitChoice D G,
      ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)) → Prop)
    [inst : ∀ s, DecidablePred (P s)]
    (hright : ∀ s, (rightForest s).elements = (imageOf s).quotientForest.elements.filter (P s))
    (hremnant : ∀ s,
      (remnantForest s).elements = (imageOf s).quotientForest.elements.filter (fun δ => ¬ P s δ))
    (s : ResolvedCoassocSplitChoice D G) :
    (imageOf s).quotientForest.elements = (rightForest s).elements ∪ (remnantForest s).elements := by
  rw [hright, hremnant]
  exact (Finset.filter_union_filter_not_eq (P s) _).symm

/-- **R-6c-leaf-15 — the Codomain `forests_disjoint` field from the star-filter shape.**  The `P` and `¬P`
filters are disjoint. -/
theorem codomain_forests_disjoint_of_star_filter
    (rightForest remnantForest : ∀ s : ResolvedCoassocSplitChoice D G,
      ResolvedAdmissibleSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
    (P : ∀ s : ResolvedCoassocSplitChoice D G,
      ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)) → Prop)
    [inst : ∀ s, DecidablePred (P s)]
    (hright : ∀ s, (rightForest s).elements = (imageOf s).quotientForest.elements.filter (P s))
    (hremnant : ∀ s,
      (remnantForest s).elements = (imageOf s).quotientForest.elements.filter (fun δ => ¬ P s δ))
    (s : ResolvedCoassocSplitChoice D G) :
    Disjoint (rightForest s).elements (remnantForest s).elements := by
  rw [hright, hremnant]
  exact Finset.disjoint_filter_filter_not _ _ (P s)

end GaugeGeometry.QFT.Combinatorial
