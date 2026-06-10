import GaugeGeometry.QFT.HopfAlgebra.ResolvedBranchMapInstantiation

/-!
# Generic resolved H5.8 classifier (Track R-4-superfull, Step 7F)

From a `ResolvedBranchMapLayer` (injectivity + cross/separation + cover) the H5.8
reindexing essence falls out generically: **every image has a unique preimage in
exactly one branch** (`∃!`).  This is the resolved analogue of
`forestComponentSplitPhiIndexedBranchClassifierOfSeparatedCover`.

We build it without proving the actual `mixed_inj`/`cover` fields — those stay layer
fields; the classifier is generic in the layer.  A `Classical.choose`-based
computational inverse (`inverse`) is also provided, matching the flat
`forestComponentSplitPhiInverseConstruction` shape.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

/-- **Resolved indexed branch classifier.**  Two branch image families with the
separated-cover property: every image has a *unique* preimage in exactly one branch. -/
structure ResolvedIndexedBranchClassifier where
  /-- Forest-branch index. -/
  ForestIdx : Type*
  /-- Mixed-branch index. -/
  MixedIdx : Type*
  /-- Image index. -/
  Image : Type*
  /-- Forest image map. -/
  forestImage : ForestIdx → Image
  /-- Mixed image map. -/
  mixedImage : MixedIdx → Image
  /-- Every image has a unique preimage in exactly one branch. -/
  classify : ∀ z : Image,
    (∃! qF, forestImage qF = z) ∨ (∃! qM, mixedImage qM = z)

/-- **Build the classifier from a branch-map layer.**  Cover gives existence in some
branch; injectivity upgrades it to uniqueness; separation makes the branches exclusive. -/
def ResolvedBranchMapLayer.toClassifier (L : ResolvedBranchMapLayer) :
    ResolvedIndexedBranchClassifier where
  ForestIdx := L.ForestIdx
  MixedIdx := L.MixedIdx
  Image := L.Image
  forestImage := L.forestImage
  mixedImage := L.mixedImage
  classify := fun z => by
    rcases L.exactly_one_branch z with ⟨⟨x, hx⟩, _⟩ | ⟨⟨y, hy⟩, _⟩
    · exact Or.inl ⟨x, hx, fun x' hx' => L.forest_inj (hx'.trans hx.symm)⟩
    · exact Or.inr ⟨y, hy, fun y' hy' => L.mixed_inj (hy'.trans hy.symm)⟩

/-- **Computational branch inverse** (via `Classical.choose`).  Sends each image to its
unique preimage on the appropriate side — the resolved analogue of the flat
`forestComponentSplitPhiInverseConstruction.inv`. -/
noncomputable def ResolvedIndexedBranchClassifier.inverse
    (C : ResolvedIndexedBranchClassifier) (z : C.Image) : C.ForestIdx ⊕ C.MixedIdx := by
  classical
  by_cases h : ∃ qF, C.forestImage qF = z
  · exact Sum.inl h.choose
  · exact Sum.inr ((C.classify z).resolve_left (fun hu => h hu.exists)).choose

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-- **Build the classifier from branch-map instantiation data.** -/
noncomputable def ResolvedBranchMapInstantiation.toClassifier
    {D : ResolvedSigmaCoverData G} (I : ResolvedBranchMapInstantiation D) :
    ResolvedIndexedBranchClassifier :=
  I.toLayer.toClassifier

/-! **Report (7F).**
* `ResolvedIndexedBranchClassifier` (Prop-level `∃!`) + `ResolvedBranchMapLayer.toClassifier`
  + `ResolvedBranchMapInstantiation.toClassifier` — landed.  The H5.8 reindexing essence
  (unique preimage in exactly one branch) is generic in the layer; no actual
  `mixed_inj`/`cover` proof needed.
* **7F-4 (flat shape)**: the flat proof has both a Prop separated-cover
  (`…BranchInverseCover`: `forest_inj`/`mixed_inj`/`cross`/`cover`) *and* a computational
  inverse (`forestComponentSplitPhiInverseConstruction.inv : RHS → LHS`).  The Prop form
  is exactly `classify`; the computational form is recovered from it via `Classical.choose`
  (`ResolvedIndexedBranchClassifier.inverse`), so both shapes are available.

R-4-superfull remaining now splits cleanly into: (1) supply the actual instantiation
fields (`mixed_inj`, `cover`, image-data graph-work — all σ-cover data per Step 7E); and
(2) the classifier-to-sum-reindex theorem feeding `coassoc_strict_forest_linear_h58`. -/

end GaugeGeometry.QFT.Combinatorial
