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
structure ResolvedH58WeightData (FL : ResolvedCarrierFiniteBranchMapLayer)
    (Target : Type*) [AddCommMonoid Target] where
  /-- The weight on images (concretely the σ-quotient tensor term). -/
  imageWeight : FL.sep.Image → Target
  /-- The weight on forest indices. -/
  forestWeight : FL.sep.ForestIdx → Target
  /-- The weight on mixed indices. -/
  mixedWeight : FL.sep.MixedIdx → Target
  /-- Forest weight agrees with the image weight along the forest branch map. -/
  forestWeight_eq : ∀ q, forestWeight q = imageWeight (FL.sep.forestImage q)
  /-- Mixed weight agrees with the image weight along the mixed branch map. -/
  mixedWeight_eq : ∀ q, mixedWeight q = imageWeight (FL.sep.mixedImage q)

/-- **Coassoc-shaped sum-reindex.**  The image-weight sum splits into the forest- and
mixed-weight sums — the Step 7G identity in coassociativity language, ready to receive
the concrete tensor-term weight. -/
theorem ResolvedH58WeightData.sum_reindex {FL : ResolvedCarrierFiniteBranchMapLayer}
    {Target : Type*} [AddCommMonoid Target] (W : ResolvedH58WeightData FL Target) :
    ∑ z ∈ FL.imageCarrier, W.imageWeight z =
      (∑ q ∈ FL.forestCarrier, W.forestWeight q) +
      (∑ q ∈ FL.mixedCarrier, W.mixedWeight q) := by
  simp only [W.forestWeight_eq, W.mixedWeight_eq]
  exact FL.sum_reindex W.imageWeight

/-! ### Carrier-based weight data (P3 fix — parallel path)

The whole-type `forestWeight_eq : ∀ q` above is over-strong: `sum_reindex` only needs it on the
forest/mixed *carriers*.  This carrier-based variant restricts the branch weights and the
agreement to the **carrier subtypes** (`{q // q ∈ forestCarrier}`), so downstream the branch
index maps need no off-carrier (junk) values.  Runs in parallel with the whole-type version. -/

/-- Carrier-based weight data: branch weights and agreement restricted to the carrier subtypes. -/
structure ResolvedH58CarrierWeightData (FL : ResolvedCarrierFiniteBranchMapLayer)
    (Target : Type*) [AddCommMonoid Target] where
  /-- The weight on images. -/
  imageWeight : FL.sep.Image → Target
  /-- The weight on forest carrier indices. -/
  forestWeight : {q // q ∈ FL.forestCarrier} → Target
  /-- The weight on mixed carrier indices. -/
  mixedWeight : {q // q ∈ FL.mixedCarrier} → Target
  /-- Forest weight agrees with the image weight along the forest branch map (carrier-only). -/
  forestWeight_eq : ∀ q, forestWeight q = imageWeight (FL.sep.forestImage q.1)
  /-- Mixed weight agrees with the image weight along the mixed branch map (carrier-only). -/
  mixedWeight_eq : ∀ q, mixedWeight q = imageWeight (FL.sep.mixedImage q.1)

/-- **Carrier-based H5.8 sum-reindex.**  Same split as the whole-type version, with the branch
sums taken over the carrier subtypes (`.attach`). -/
theorem ResolvedH58CarrierWeightData.sum_reindex {FL : ResolvedCarrierFiniteBranchMapLayer}
    {Target : Type*} [AddCommMonoid Target] (W : ResolvedH58CarrierWeightData FL Target) :
    ∑ z ∈ FL.imageCarrier, W.imageWeight z =
      (∑ q ∈ FL.forestCarrier.attach, W.forestWeight q) +
      (∑ q ∈ FL.mixedCarrier.attach, W.mixedWeight q) := by
  simp only [W.forestWeight_eq, W.mixedWeight_eq]
  rw [Finset.sum_attach FL.forestCarrier (fun q => W.imageWeight (FL.sep.forestImage q)),
    Finset.sum_attach FL.mixedCarrier (fun q => W.imageWeight (FL.sep.mixedImage q))]
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

/-! ## Step 7J — concrete weight wrapper (via flat alignment)

The flat H5.8 terms (`forestQuotientForestSigmaTerm`, `forestComponentSplitChoiceSigmaTerm`,
`forestComponentSplitPhi`, `forestComponentSplitPhi_term_eq_of_split`) are **`private`**
to `Coassoc.lean`, so they cannot be named from this standalone track.  We therefore
keep the wrapper **abstract over an alignment**: the alignment carries the flat image
type, term, branch map, the term-agreement, and the maps from the resolved layer's
indices to the flat split indices, with the two commutation squares.  The concrete
alignment (plugging the actual private defs) is the single point where this track meets
`Coassoc.lean`'s privates — to be supplied there. -/

/-- Alignment of a resolved finite branch-map layer to the flat H5.8 indices/terms.
All flat data is abstracted (the concrete flat defs are `private` to `Coassoc.lean`).

The term agreement is **index-conditional** (`splitMem`), matching the flat
`forestComponentSplitPhi_term_eq_of_split` which holds only on
`forestComponentSplitChoiceSigmaIndex`; the resolved split-index maps must land in that
index (`forestSplitOf_mem`/`mixedSplitOf_mem`). -/
structure ResolvedFlatH58WeightAlignment (FL : ResolvedCarrierFiniteBranchMapLayer)
    (Target : Type*) [AddCommMonoid Target] where
  /-- The flat image type (`forestQuotientForestSigma g`). -/
  FlatImage : Type*
  /-- The flat split-choice index type (`forestComponentSplitChoiceSigma g`). -/
  SplitIdx : Type*
  /-- Membership in the flat split-choice index (`· ∈ forestComponentSplitChoiceSigmaIndex g`). -/
  splitMem : SplitIdx → Prop
  /-- The flat image term (`forestQuotientForestSigmaTerm`). -/
  flatTerm : FlatImage → Target
  /-- The flat split term (`forestComponentSplitChoiceSigmaTerm`). -/
  splitTerm : SplitIdx → Target
  /-- The flat branch map (`forestComponentSplitPhi`). -/
  flatBranch : SplitIdx → FlatImage
  /-- The term agreement, index-conditional (`forestComponentSplitPhi_term_eq_of_split`). -/
  splitTerm_eq : ∀ s, splitMem s → splitTerm s = flatTerm (flatBranch s)
  /-- Resolved image → flat image. -/
  flatImageOf : FL.sep.Image → FlatImage
  /-- Resolved forest index → flat split index. -/
  forestSplitOf : FL.sep.ForestIdx → SplitIdx
  /-- Resolved mixed index → flat split index. -/
  mixedSplitOf : FL.sep.MixedIdx → SplitIdx
  /-- Forest split indices land in the flat split index. -/
  forestSplitOf_mem : ∀ q, splitMem (forestSplitOf q)
  /-- Mixed split indices land in the flat split index. -/
  mixedSplitOf_mem : ∀ q, splitMem (mixedSplitOf q)
  /-- Forest commutation square. -/
  forest_comm : ∀ q, flatImageOf (FL.sep.forestImage q) = flatBranch (forestSplitOf q)
  /-- Mixed commutation square. -/
  mixed_comm : ∀ q, flatImageOf (FL.sep.mixedImage q) = flatBranch (mixedSplitOf q)

/-- Pull the flat terms back through the alignment to a concrete `ResolvedH58WeightData`.
The two `_eq` fields are two-line `rw`s using the index-conditional term agreement (at the
`…SplitOf_mem` witness) + the commutation square (no new mathematics). -/
noncomputable def ResolvedFlatH58WeightAlignment.toWeightData {FL : ResolvedCarrierFiniteBranchMapLayer}
    {Target : Type*} [AddCommMonoid Target] (A : ResolvedFlatH58WeightAlignment FL Target) :
    ResolvedH58WeightData FL Target where
  imageWeight := fun z => A.flatTerm (A.flatImageOf z)
  forestWeight := fun q => A.splitTerm (A.forestSplitOf q)
  mixedWeight := fun q => A.splitTerm (A.mixedSplitOf q)
  forestWeight_eq := fun q => by
    rw [A.splitTerm_eq _ (A.forestSplitOf_mem q), A.forest_comm]
  mixedWeight_eq := fun q => by
    rw [A.splitTerm_eq _ (A.mixedSplitOf_mem q), A.mixed_comm]

/-- **Concrete H5.8 sum equality** through the alignment: the flat-term sum over images
splits into the flat split-term sums over the forest and mixed branches. -/
theorem ResolvedFlatH58WeightAlignment.sum_reindex {FL : ResolvedCarrierFiniteBranchMapLayer}
    {Target : Type*} [AddCommMonoid Target] (A : ResolvedFlatH58WeightAlignment FL Target) :
    ∑ z ∈ FL.imageCarrier, A.flatTerm (A.flatImageOf z) =
      (∑ q ∈ FL.forestCarrier, A.splitTerm (A.forestSplitOf q)) +
      (∑ q ∈ FL.mixedCarrier, A.splitTerm (A.mixedSplitOf q)) :=
  A.toWeightData.sum_reindex

/-! **Report (7J).**
* `ResolvedFlatH58WeightAlignment` + `toWeightData` + `sum_reindex` — landed, abstract
  over the (private) flat data.  `forestWeight_eq`/`mixedWeight_eq` are discharged by
  `rw [splitTerm_eq, forest_comm/​mixed_comm]` — exactly the existing
  `forestComponentSplitPhi_term_eq_of_split` plus the commutation squares; **no new
  mathematics**.
* The only remaining flat-facing step is to *construct* the concrete alignment inside
  `Coassoc.lean` (where the privates live): `flatTerm := forestQuotientForestSigmaTerm`,
  `splitTerm := forestComponentSplitChoiceSigmaTerm`, `flatBranch := forestComponentSplitPhi`,
  `splitTerm_eq := forestComponentSplitPhi_term_eq_of_split`, with `flatImageOf`/
  `forestSplitOf`/`mixedSplitOf` the resolved→flat index maps and the two commutation
  squares from the branch-map definitions.  That is the single contact point between this
  standalone track and the flat H5.8 privates. -/

/-! ## Step 7K — Coassoc-local alignment scout (import-cycle + visibility)

**Cycle confirmed (HALT).**  The resolved track imports `Coassoc` (chain:
`ResolvedH58Weight → … → ResolvedCoproduct → Coassoc`).  Therefore `Coassoc.lean`
**cannot** import the resolved files — that would be an import cycle.  So the concrete
alignment can be built *only* in a downstream file (one that imports both `Coassoc` and
this file), using **public wrappers** exposed from `Coassoc`.

**Public wrappers needed in `Coassoc.lean`** (currently `private`; thin public aliases,
no proof change, but they touch the `Main` build — a deliberate step to confirm before
making):
* types: `forestQuotientForestSigma g`, `forestComponentSplitChoiceSigma g`
* index membership: `· ∈ forestQuotientForestSigmaIndex g`,
  `· ∈ forestComponentSplitChoiceSigmaIndex g`
* terms: `forestQuotientForestSigmaTerm g`, `forestComponentSplitChoiceSigmaTerm g`
* branch: `forestComponentSplitPhi g`
* agreement: `forestComponentSplitPhi_term_eq_of_split g` (with its per-branch
  `hForestTerm`/`hMixedTerm` already discharged in the canonical instance)

**Type-fit finding.**  `flatTerm`/`splitTerm`/`flatBranch` fit the fields directly
(target `HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)` matches).  The agreement
`forestComponentSplitPhi_term_eq_of_split` is **index-conditional** (`q ∈
forestComponentSplitChoiceSigmaIndex`) — which is exactly why this file's
`ResolvedFlatH58WeightAlignment` was refined (7K) to a conditional `splitTerm_eq` +
`forestSplitOf_mem`/`mixedSplitOf_mem`.  With that shape the private agreement plugs in
directly.

**Plan.**  (1) expose the public wrappers in `Coassoc` (Main-touching — confirm first);
(2) in a new downstream file `ResolvedH58Bridge.lean` (imports `Coassoc` + this file),
construct `ResolvedFlatH58WeightAlignment` from them; (3) `sum_reindex` then gives the
concrete H5.8 split identity resolved-side.  No new mathematics — only the wrappers + the
resolved→flat index maps + commutation squares. -/

end GaugeGeometry.QFT.Combinatorial
