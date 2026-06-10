import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Reindex

/-!
# Coassoc weight interface (Track R-4-superfull, Step 7H)

The abstract sum-reindex of Step 7G (`∑ image = ∑ forest + ∑ mixed`) phrased in the
language of a **weight package**: an image weight together with forest/mixed weights
that agree with it along the branch maps.  Specialising the weight to the concrete H5.8
tensor term turns this into the coassociativity reindexing identity.

**Flat target (7H-3 scout).**  The flat summand is
`forestQuotientForestSigmaTerm g q := q.1.1.toHopfH ⊗ₜ
admissibleForestStrictSummandWithCanonicalStars …`, valued in
`HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)`.  The headline
`coassoc_strict_forest_linear_h58` reduces (via
`coassoc_strict_forest_linear_of_h58_indexed_classifier_canonical`, fed
`CoassocStrictForestH58FinitePayloads.indexed_classifier`) to exactly a classifier-based
reindex of this term; the `Algebra.TensorProduct.assoc` associator sits on the rTensor
side of the equation.  So the concrete `Target` is `HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)` and
the concrete `imageWeight` is `forestQuotientForestSigmaTerm` (resolved analogue).
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

/-- **Coassoc weight package.**  An image weight plus forest/mixed weights agreeing with
it along the branch maps — the data a coassociativity reindex needs on top of a finite
branch-map layer.  `Target` is kept generic (concretely `HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)`). -/
structure ResolvedH58WeightData (FL : ResolvedFiniteBranchMapLayer)
    (Target : Type*) [AddCommMonoid Target] where
  /-- The weight on images (concretely the σ-quotient tensor term). -/
  imageWeight : FL.layer.Image → Target
  /-- The weight on forest indices. -/
  forestWeight : FL.layer.ForestIdx → Target
  /-- The weight on mixed indices. -/
  mixedWeight : FL.layer.MixedIdx → Target
  /-- Forest weight agrees with the image weight along the forest branch map. -/
  forestWeight_eq : ∀ q, forestWeight q = imageWeight (FL.layer.forestImage q)
  /-- Mixed weight agrees with the image weight along the mixed branch map. -/
  mixedWeight_eq : ∀ q, mixedWeight q = imageWeight (FL.layer.mixedImage q)

/-- **Coassoc-shaped sum-reindex.**  The image-weight sum splits into the forest- and
mixed-weight sums — the Step 7G identity in coassociativity language, ready to receive
the concrete tensor-term weight. -/
theorem ResolvedH58WeightData.sum_reindex {FL : ResolvedFiniteBranchMapLayer}
    {Target : Type*} [AddCommMonoid Target] (W : ResolvedH58WeightData FL Target) :
    ∑ z ∈ FL.imageCarrier, W.imageWeight z =
      (∑ q ∈ FL.forestCarrier, W.forestWeight q) +
      (∑ q ∈ FL.mixedCarrier, W.mixedWeight q) := by
  simp only [W.forestWeight_eq, W.mixedWeight_eq]
  exact FL.sum_reindex W.imageWeight

/-! **Report (7H).**
* `ResolvedH58WeightData` (generic `Target`) + `sum_reindex` — landed.  The abstract
  H5.8 reindex is now in coassociativity language: `∑ image imageWeight =
  ∑ forest forestWeight + ∑ mixed mixedWeight`, with the branch agreements as fields.
* **Concrete target/weight (7H-3)**: `Target := HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)`;
  `imageWeight := forestQuotientForestSigmaTerm` (resolved analogue) =
  `toHopfH ⊗ₜ admissibleForestStrictSummandWithCanonicalStars …`.  The flat headline
  `coassoc_strict_forest_linear_h58` factors through
  `coassoc_strict_forest_linear_of_h58_indexed_classifier_canonical` +
  `CoassocStrictForestH58FinitePayloads.indexed_classifier`; the `TensorProduct.assoc`
  associator is on the rTensor side.
* **Remaining**: instantiate `imageWeight`/`forestWeight`/`mixedWeight` with the concrete
  tensor terms and discharge `forestWeight_eq`/`mixedWeight_eq` (the branch-map term
  agreements), then match `sum_reindex` to the two sides of
  `coassoc_strict_forest_linear`.  Plus the σ-cover data fields (Step 7E) for the actual
  finite layer.  No new abstract structure needed — only the concrete weight + data. -/

/-! ## Step 7I — concrete weight extraction scout (flat term names)

採寸: the exact flat sources for each `ResolvedH58WeightData` field (all in
`Coassoc.lean`).

| field | flat concrete source | status |
|-------|----------------------|--------|
| `Target` | `HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)` | direct (codomain of the term) |
| `imageWeight` | `forestQuotientForestSigmaTerm g` (≈14427) | existing def |
| `forestWeight` | `forestComponentSplitChoiceSigmaTerm g ∘ Sum.inl` (27517) = `forestComponentChoiceSigmaTerm g` | existing def |
| `mixedWeight` | `forestComponentSplitChoiceSigmaTerm g ∘ Sum.inr` (27517) = `forestComponentChoiceSigmaTerm g` | existing def |
| `forestWeight_eq` | `forestComponentSplitPhi_term_eq_of_split` (27718), forest branch | existing lemma, fed `hForestTerm` |
| `mixedWeight_eq` | `forestComponentSplitPhi_term_eq_of_split` (27718), mixed branch | existing lemma, fed `hMixedTerm` |
| (per-branch term agreement) | `forestComponentChoiceSigmaTerm_eq_quotientForestSigmaTerm_of_factorization` (27348) | existing lemma |
| (branch map φ) | `forestComponentSplitPhi g` (27537) | existing def |
| (LHS index) | `forestComponentSplitChoiceSigmaIndex = forestIdx.disjSum mixedIdx` (27510) | existing |
| (RHS index) | `forestQuotientForestSigmaIndex g` | existing |
| (closest pure sum equality) | reindex inside `coassoc_strict_forest_linear_of_h58_indexed_classifier` (37025), via the bijective `forestComponentSplitPhiIndexedBranchClassifier` (28031) | existing |

**Key finding.**  The term agreement `forestWeight_eq`/`mixedWeight_eq` is *exactly*
`forestComponentSplitPhi_term_eq_of_split` — already flat-proven, assembled from the
per-branch factorization lemma (27348).  And the flat `…IndexedBranchClassifier` (28031)
is a *bijection* (`preimage` + `right_inv` + `forest_inv`/`mixed_inv`), richer than the
Prop `∃!` of `ResolvedIndexedBranchClassifier`; the resolved instantiation reuses
`inverse` (Step 7F) for the computational `preimage` and the `∃!` for the inverse laws.

So weight instantiation needs **no new mathematics**: the concrete `imageWeight`/
`forestWeight`/`mixedWeight` are existing defs and the two `_eq` fields are existing
lemmas — only the resolved-side wrappers + the σ-cover data fields remain. -/

end GaugeGeometry.QFT.Combinatorial
