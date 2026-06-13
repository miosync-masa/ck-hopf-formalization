import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Bridge

/-!
# Final σ-cover data package (Track R-4-superfull)

The R-4-superfull architecture is complete up to **one** remaining construction: an
actual resolved σ-cover.  This file consolidates the remaining obligations into a single
package `ResolvedActualSigmaCover g`, and shows it delivers the concrete H5.8 sum-reindex
identity and the branch classifier.

What is **embedded in `FL`** (`ResolvedCarrierFiniteBranchMapLayer`) and so *not* duplicated
here: the layer's `cover` (branch-map surjectivity), `forest_inj`/`mixed_inj`, and the
forest/mixed image data carrying `componentCD`/`remnantCD`/disjointness/`avoidsStars`
(all baked in when `FL` is built from the forest/mixed image data via
`ResolvedBranchMapInstantiation.toLayer`).

What remains **external** (the package's own fields): the resolved→flat
`concreteIndexMaps` and the flat `splitTerm_agreement` (σ-cover data, Field Filling 6).

So the entire remaining R-4-superfull obstruction is: *construct one
`ResolvedActualSigmaCover g`*.
-/

set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-! ## Actual construction — the separation data (FC-1)

The branch-map layer's `sep` (the non-carrier, whole-`Image` part) is constructible *now*:
`ForestIdx`/`MixedIdx` are the resolved forest/mixed image-data types, `Image` is the
quotient-forest type, the branch maps are `·.toImage`, and `forest_sat`/`mixed_unsat`
are exactly the `ResolvedForestImageData.forest_sat` / `ResolvedMixedImageData.mixed_unsat`
fields (from `starWitness` / `avoidsStars`).  This is the satisfiable whole-`Image`
separation; the *finite carriers* + `cover_on` + `inj_on` are the remaining σ-cover data. -/

/-- The resolved σ-cover separation data: forest/mixed image data with the
`resolvedIsForestByStar` discriminator.  Satisfiable over *all* image data. -/
noncomputable def resolvedActualSep (D : ResolvedSigmaCoverData G) :
    ResolvedBranchSeparationData where
  ForestIdx := ResolvedForestImageData D
  MixedIdx := ResolvedMixedImageData D
  Image := ResolvedActualQuotientImage D
  discriminator := resolvedIsForestByStar D
  forestImage := fun F => F.toImage
  mixedImage := fun M => M.toImage
  forest_sat := fun F => F.forest_sat
  mixed_unsat := fun M => M.mixed_unsat

/-- **Assemble the carrier-based finite layer** from the actual σ-cover finite data: the
finite forest/mixed/quotient carriers (`ResolvedForestImageData`/`ResolvedMixedImageData`/
quotient images) plus their membership, carrier-cover, and carrier-injectivity.  The
separation data (`sep`) is supplied automatically (`resolvedActualSep`); this constructor
reduces the layer to exactly the remaining finite σ-cover obligations. -/
noncomputable def resolvedActualCarrierLayer (D : ResolvedSigmaCoverData G)
    (forestCarrier : Finset (ResolvedForestImageData D))
    (mixedCarrier : Finset (ResolvedMixedImageData D))
    (imageCarrier : Finset (ResolvedActualQuotientImage D))
    (forestImage_mem : ∀ F ∈ forestCarrier, F.toImage ∈ imageCarrier)
    (mixedImage_mem : ∀ M ∈ mixedCarrier, M.toImage ∈ imageCarrier)
    (cover_on : ∀ z ∈ imageCarrier,
      (∃ F ∈ forestCarrier, F.toImage = z) ∨ (∃ M ∈ mixedCarrier, M.toImage = z))
    (forest_inj_on : ∀ F₁ ∈ forestCarrier, ∀ F₂ ∈ forestCarrier,
      F₁.toImage = F₂.toImage → F₁ = F₂)
    (mixed_inj_on : ∀ M₁ ∈ mixedCarrier, ∀ M₂ ∈ mixedCarrier,
      M₁.toImage = M₂.toImage → M₁ = M₂) :
    ResolvedCarrierFiniteBranchMapLayer where
  sep := resolvedActualSep D
  forestCarrier := forestCarrier
  mixedCarrier := mixedCarrier
  imageCarrier := imageCarrier
  forestImage_mem := forestImage_mem
  mixedImage_mem := mixedImage_mem
  cover_on := cover_on
  forest_inj_on := forest_inj_on
  mixed_inj_on := mixed_inj_on

/-! ## Actual construction — finite carriers (FC-2, option C)

Taking `imageCarrier := forest images ∪ mixed images` makes `forestImage_mem`,
`mixedImage_mem`, and `cover_on` immediate (by construction).  So the finite-carrier data
reduces to just the two finite branch carriers and their carrier-injectivity; the layer is
then assembled with no further membership/cover proofs.  (Matching this union carrier to the
flat RHS quotient index is deferred to `ResolvedH58ConcreteIndexMaps`.) -/

/-- The finite branch carriers (forest/mixed image data) with carrier-injectivity.  The
image carrier is their union of branch images, so cover/membership are automatic. -/
structure ResolvedActualFiniteCarriers (D : ResolvedSigmaCoverData G) where
  /-- Finite forest image-data carrier. -/
  forestCarrier : Finset (ResolvedForestImageData D)
  /-- Finite mixed image-data carrier. -/
  mixedCarrier : Finset (ResolvedMixedImageData D)
  /-- Carrier forest-injectivity. -/
  forest_inj_on : ∀ F₁ ∈ forestCarrier, ∀ F₂ ∈ forestCarrier,
    F₁.toImage = F₂.toImage → F₁ = F₂
  /-- Carrier mixed-injectivity. -/
  mixed_inj_on : ∀ M₁ ∈ mixedCarrier, ∀ M₂ ∈ mixedCarrier,
    M₁.toImage = M₂.toImage → M₁ = M₂

/-- **The carrier-based finite layer from the finite branch carriers** (option C: the image
carrier is the union of branch images, so cover/membership are by construction). -/
noncomputable def ResolvedActualFiniteCarriers.toCarrierLayer {D : ResolvedSigmaCoverData G}
    (C : ResolvedActualFiniteCarriers D) : ResolvedCarrierFiniteBranchMapLayer := by
  classical
  refine resolvedActualCarrierLayer D C.forestCarrier C.mixedCarrier
    (C.forestCarrier.image (fun F => F.toImage) ∪ C.mixedCarrier.image (fun M => M.toImage))
    ?_ ?_ ?_ C.forest_inj_on C.mixed_inj_on
  · intro F hF
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hF)
  · intro M hM
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hM)
  · intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hz; exact Or.inl ⟨F, hF, rfl⟩
    · obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hz; exact Or.inr ⟨M, hM, rfl⟩

/-! ## Actual construction — branch carriers, `inj_on` reduced (FC-3)

The carrier injectivity (`forest_inj_on`/`mixed_inj_on`, stated on `toImage`) reduces to
injectivity at the natural σ-cover index level — `choiceParents` for forest, `components`
for mixed — via the established `toImage_choiceParents_inj` / `components_eq_of_toImage_eq`.
So the branch-carrier data is just the two finite sets with index-level injectivity. -/

/-- The finite branch carriers with **index-level** injectivity (`choiceParents` for forest,
`components` for mixed). -/
structure ResolvedBranchCarriers (D : ResolvedSigmaCoverData G) where
  /-- Finite forest image-data carrier. -/
  forestCarrier : Finset (ResolvedForestImageData D)
  /-- Finite mixed image-data carrier. -/
  mixedCarrier : Finset (ResolvedMixedImageData D)
  /-- Forest carrier is injective in `choiceParents`. -/
  forest_choiceParents_inj : ∀ x ∈ forestCarrier, ∀ y ∈ forestCarrier,
    x.choiceParents = y.choiceParents → x = y
  /-- Mixed carrier is injective in `components`. -/
  mixed_components_inj : ∀ x ∈ mixedCarrier, ∀ y ∈ mixedCarrier,
    x.components = y.components → x = y

/-- Reduce to `ResolvedActualFiniteCarriers`: the `toImage` injectivity follows from
index-level injectivity (forest via `toImage_choiceParents_inj`, mixed via
`components_eq_of_toImage_eq`), fed the payload's `EdgeIdsUnique`/`LegIdsUnique`. -/
def ResolvedBranchCarriers.toFiniteCarriers {D : ResolvedSigmaCoverData G}
    (C : ResolvedBranchCarriers D) (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    ResolvedActualFiniteCarriers D where
  forestCarrier := C.forestCarrier
  mixedCarrier := C.mixedCarrier
  forest_inj_on := fun F₁ hF₁ F₂ hF₂ hImg =>
    C.forest_choiceParents_inj F₁ hF₁ F₂ hF₂
      (ResolvedForestImageData.toImage_choiceParents_inj hEdgeId hLegId
        (congrArg ResolvedAdmissibleSubgraph.elements hImg))
  mixed_inj_on := fun M₁ hM₁ M₂ hM₂ hImg =>
    C.mixed_components_inj M₁ hM₁ M₂ hM₂
      (ResolvedMixedImageData.components_eq_of_toImage_eq hImg)

/-- The carrier-based finite layer directly from branch carriers (+ id-uniqueness). -/
noncomputable def ResolvedBranchCarriers.toLayer {D : ResolvedSigmaCoverData G}
    (C : ResolvedBranchCarriers D) (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    ResolvedCarrierFiniteBranchMapLayer :=
  (C.toFiniteCarriers hEdgeId hLegId).toCarrierLayer

/-- **The actual resolved σ-cover package.**  Consolidates the remaining R-4-superfull
obligations: the finite branch-map layer (carrying cover/injectivity/CD/disjoint), the
id-unique payload family, the resolved→flat index maps, and the flat split-term
agreement. -/
structure ResolvedActualSigmaCover (g : HopfGen) where
  /-- The id-unique payload family (supplies `EdgeIdsUnique`/`LegIdsUnique`). -/
  PFU : ResolvedHopfPayloadFamilyWithUniqueIds
  /-- The finite branch-map layer (carries cover/injectivity/CD/disjoint via its build). -/
  FL : ResolvedCarrierFiniteBranchMapLayer
  /-- Resolved→flat index maps + commutation squares. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g FL
  /-- The flat split-term agreement (σ-cover data). -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

namespace ResolvedActualSigmaCover

variable {g : HopfGen} (S : ResolvedActualSigmaCover g)

/-- The full concrete bridge data assembled from the package. -/
def concreteData : ResolvedH58ConcreteData g S.FL :=
  S.concreteIndexMaps.toConcreteData S.splitTerm_agreement

/-- **The concrete resolved H5.8 sum-reindex** delivered by the package, with the actual
flat tensor terms. -/
theorem concrete_sum_reindex :
    ∑ z ∈ S.FL.imageCarrier, h58BridgeQuotientTerm g (S.concreteData.flatImageOf z) =
      (∑ q ∈ S.FL.forestCarrier, h58BridgeSplitChoiceTerm g (S.concreteData.forestSplitOf q)) +
      (∑ q ∈ S.FL.mixedCarrier, h58BridgeSplitChoiceTerm g (S.concreteData.mixedSplitOf q)) :=
  S.concreteData.concrete_sum_reindex

end ResolvedActualSigmaCover

/-! ## Final constructor (FC-4)

The remaining concrete data, bundled, with the constructor to `ResolvedActualSigmaCover`.
The finite branch-map layer `FL` is built from `branchCarriers` (+ the payload's
id-uniqueness); the package adds the concrete index maps and the flat term agreement.
So the entire R-4-superfull obstruction is now `ResolvedActualSigmaCoverSupply g`. -/

/-- All remaining concrete σ-cover data for one generator: the id-unique payload family,
the σ-cover data, the finite branch carriers, the resolved→flat index maps, and the flat
term agreement. -/
structure ResolvedActualSigmaCoverSupply (g : HopfGen) where
  /-- The id-unique payload family. -/
  PFU : ResolvedHopfPayloadFamilyWithUniqueIds
  /-- The σ-cover data on the payload graph. -/
  D : ResolvedSigmaCoverData (PFU.payload g).G
  /-- The finite branch carriers. -/
  branchCarriers : ResolvedBranchCarriers D
  /-- The resolved→flat index maps for the layer built from `branchCarriers`. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g
    (branchCarriers.toLayer (PFU.edgeIdsUnique g) (PFU.legIdsUnique g))
  /-- The flat split-term agreement. -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

/-- **Assemble `ResolvedActualSigmaCover` from the supply.**  The single remaining
R-4-superfull obstruction is to construct one `ResolvedActualSigmaCoverSupply g`. -/
noncomputable def ResolvedActualSigmaCoverSupply.toActualSigmaCover {g : HopfGen}
    (S : ResolvedActualSigmaCoverSupply g) : ResolvedActualSigmaCover g where
  PFU := S.PFU
  FL := S.branchCarriers.toLayer (S.PFU.edgeIdsUnique g) (S.PFU.legIdsUnique g)
  concreteIndexMaps := S.concreteIndexMaps
  splitTerm_agreement := S.splitTerm_agreement

/-- The concrete H5.8 sum-reindex delivered by the supply (with the actual flat tensor
terms). -/
theorem ResolvedActualSigmaCoverSupply.concrete_sum_reindex {g : HopfGen}
    (S : ResolvedActualSigmaCoverSupply g) :
    ∑ z ∈ S.toActualSigmaCover.FL.imageCarrier,
        h58BridgeQuotientTerm g (S.toActualSigmaCover.concreteData.flatImageOf z) =
      (∑ q ∈ S.toActualSigmaCover.FL.forestCarrier,
          h58BridgeSplitChoiceTerm g (S.toActualSigmaCover.concreteData.forestSplitOf q)) +
      (∑ q ∈ S.toActualSigmaCover.FL.mixedCarrier,
          h58BridgeSplitChoiceTerm g (S.toActualSigmaCover.concreteData.mixedSplitOf q)) :=
  S.toActualSigmaCover.concrete_sum_reindex

/-! ## Canonical specialization — PFU fixed

Fixing `PFU` to the canonical id-unique payload family (`Phase 6c`/`Steps 2–3`, already
constructed) removes it from the final obstruction.  The remaining data is just the
σ-cover data, the branch carriers, the index maps, and the term agreement — over the
canonical payload. -/

/-- The remaining concrete data over the **canonical** id-unique payload family (PFU fixed).
The entire R-4-superfull obstruction is to construct one of these. -/
structure CanonicalResolvedActualSigmaCoverSupply (g : HopfGen) where
  /-- σ-cover data on the canonical payload graph. -/
  D : ResolvedSigmaCoverData (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G
  /-- The finite branch carriers. -/
  branchCarriers : ResolvedBranchCarriers D
  /-- The resolved→flat index maps for the canonical layer. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g
    (branchCarriers.toLayer
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.edgeIdsUnique g)
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.legIdsUnique g))
  /-- The flat split-term agreement. -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

/-- Reduce the canonical supply to the general supply (PFU := canonical). -/
noncomputable def CanonicalResolvedActualSigmaCoverSupply.toSupply {g : HopfGen}
    (S : CanonicalResolvedActualSigmaCoverSupply g) : ResolvedActualSigmaCoverSupply g where
  PFU := canonicalResolvedHopfPayloadFamilyWithUniqueIds
  D := S.D
  branchCarriers := S.branchCarriers
  concreteIndexMaps := S.concreteIndexMaps
  splitTerm_agreement := S.splitTerm_agreement

/-- The concrete H5.8 sum-reindex from the canonical supply. -/
theorem CanonicalResolvedActualSigmaCoverSupply.concrete_sum_reindex {g : HopfGen}
    (S : CanonicalResolvedActualSigmaCoverSupply g) :
    ∑ z ∈ S.toSupply.toActualSigmaCover.FL.imageCarrier,
        h58BridgeQuotientTerm g (S.toSupply.toActualSigmaCover.concreteData.flatImageOf z) =
      (∑ q ∈ S.toSupply.toActualSigmaCover.FL.forestCarrier,
          h58BridgeSplitChoiceTerm g (S.toSupply.toActualSigmaCover.concreteData.forestSplitOf q)) +
      (∑ q ∈ S.toSupply.toActualSigmaCover.FL.mixedCarrier,
          h58BridgeSplitChoiceTerm g (S.toSupply.toActualSigmaCover.concreteData.mixedSplitOf q)) :=
  S.toSupply.concrete_sum_reindex

/-! ## Construction scout — `D` is per-outer-forest (index-parameter finding)

**Critical scout (D source / index granularity).**  The flat RHS quotient index is a
*sigma over outer proper forests*:
`forestQuotientForestSigmaIndex g = (forestOuterProperFinset g).filter (…).sigma
(fun A => forestCoproductProperForestIndex (forestOuterQuotientHopfGen g A))` — for each
outer proper forest `A`, an inner index of quotients of the `A`-contracted graph.  But
`ResolvedSigmaCoverData G` fixes a **single** `Aout`.  So `D` is **per-outer-forest** (one
`Aout`), *not* per-`g`, and the per-`D` `concrete_sum_reindex` is the **inner** sum for one
outer forest.

**Design implication (not a collapse — an outer index).**  The full H5.8 RHS is
`∑ A ∈ outerProperForests, (inner sum for A)`.  So the resolved reindex assembles as an
**outer sum over outer forests of the per-`D` `concrete_sum_reindex`**.  Concretely, either:
* index the supply by the outer forest — `CanonicalResolvedActualSigmaCoverSupply` carries
  a finite family `D`/carriers per outer forest; or
* add a thin `ResolvedH58OuterSum` layer that sums the per-`D` identities over the outer
  proper-forest carrier.

Everything built stays valid: the per-`D` (per-outer-forest) reindex *is* the inner
summand.  The remaining design step is the outer sum over outer proper forests — the last
index parameter, not new mathematics or a facade.  `D` itself is then: `Aout` = a resolved
outer proper forest of the canonical payload graph, `starOf` = canonical fresh stars,
`parents` = the inner proper-forest parents, with `starFresh`/`componentPositiveEdges` from
the canonical construction. -/

/-! ## Outer-forest sum layer (the H5.8 double sum)

The full H5.8 RHS is the **sum over outer proper forests** of the per-outer-forest inner
reindex identities.  `ResolvedH58OuterSumSupply` carries a finite family of per-outer
supplies; `outer_sum_reindex` sums their `concrete_sum_reindex` identities — no new
mathematics, just `Finset.sum_congr`. -/

/-- A finite family of per-outer-forest σ-cover supplies (one inner supply per outer
proper forest). -/
structure ResolvedH58OuterSumSupply (g : HopfGen) where
  /-- The outer proper-forest index. -/
  OuterIdx : Type*
  /-- The finite outer carrier (resolved analogue of `forestOuterProperFinset g`). -/
  outerCarrier : Finset OuterIdx
  /-- The per-outer inner σ-cover supply. -/
  innerSupply : OuterIdx → CanonicalResolvedActualSigmaCoverSupply g

namespace ResolvedH58OuterSumSupply

variable {g : HopfGen} (S : ResolvedH58OuterSumSupply g)

/-- The inner image-weight sum for one outer forest. -/
noncomputable def innerImageSum (A : S.OuterIdx) : HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH) :=
  ∑ z ∈ (S.innerSupply A).toSupply.toActualSigmaCover.FL.imageCarrier,
    h58BridgeQuotientTerm g ((S.innerSupply A).toSupply.toActualSigmaCover.concreteData.flatImageOf z)

/-- The inner forest+mixed branch-weight sum for one outer forest. -/
noncomputable def innerBranchSum (A : S.OuterIdx) : HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH) :=
  (∑ q ∈ (S.innerSupply A).toSupply.toActualSigmaCover.FL.forestCarrier,
      h58BridgeSplitChoiceTerm g
        ((S.innerSupply A).toSupply.toActualSigmaCover.concreteData.forestSplitOf q)) +
  (∑ q ∈ (S.innerSupply A).toSupply.toActualSigmaCover.FL.mixedCarrier,
      h58BridgeSplitChoiceTerm g
        ((S.innerSupply A).toSupply.toActualSigmaCover.concreteData.mixedSplitOf q))

/-- **The H5.8 double sum.**  The outer sum of inner image-weight sums equals the outer sum
of inner branch-weight sums — the full reindex, assembled from the per-outer-forest
`concrete_sum_reindex` identities by `Finset.sum_congr`. -/
theorem outer_sum_reindex :
    ∑ A ∈ S.outerCarrier, S.innerImageSum A = ∑ A ∈ S.outerCarrier, S.innerBranchSum A :=
  Finset.sum_congr rfl (fun A _ => (S.innerSupply A).concrete_sum_reindex)

end ResolvedH58OuterSumSupply

/-! ## Outer carrier fixed to the flat outer proper-forest index

Using the flat outer proper-forest index (`h58BridgeOuterIndex`/`h58BridgeOuterCarrier`,
public wrappers of `forestOuterProperIndex`/`forestOuterProperFinset`-filtered) as the
outer carrier — the resolved lift happens inside `innerSupply`.  So the only remaining datum
is `innerSupply`: a per-outer-forest σ-cover supply for each flat outer proper forest. -/

/-- The outer-sum skeleton: a per-outer-forest inner supply for each flat outer proper
forest.  The outer carrier is fixed (`h58BridgeOuterCarrier g`); only `innerSupply` remains. -/
structure ResolvedH58OuterSkeleton (g : HopfGen) where
  /-- The per-outer-forest inner σ-cover supply, indexed by the flat outer proper forest. -/
  innerSupply : h58BridgeOuterIndex g → CanonicalResolvedActualSigmaCoverSupply g

/-- Assemble the outer-sum supply with the flat outer proper-forest carrier. -/
noncomputable def ResolvedH58OuterSkeleton.toOuterSumSupply {g : HopfGen}
    (Sk : ResolvedH58OuterSkeleton g) : ResolvedH58OuterSumSupply g where
  OuterIdx := h58BridgeOuterIndex g
  outerCarrier := h58BridgeOuterCarrier g
  innerSupply := Sk.innerSupply

/-- **The H5.8 double sum over the actual flat outer proper-forest carrier**, from the
skeleton — `∑ A ∈ h58BridgeOuterCarrier g, (inner image sum) = ∑ A, (inner branch sum)`. -/
theorem ResolvedH58OuterSkeleton.outer_sum_reindex {g : HopfGen}
    (Sk : ResolvedH58OuterSkeleton g) :
    ∑ A ∈ h58BridgeOuterCarrier g, Sk.toOuterSumSupply.innerImageSum A =
      ∑ A ∈ h58BridgeOuterCarrier g, Sk.toOuterSumSupply.innerBranchSum A :=
  Sk.toOuterSumSupply.outer_sum_reindex

/-! ## InnerSupply-1 scout — constructing `D` per outer forest

The remaining datum is `innerSupply A : CanonicalResolvedActualSigmaCoverSupply g` for each
flat outer forest `A : h58BridgeOuterIndex g`.  Its first field is
`D : ResolvedSigmaCoverData (ofFlatGraphWithUniqueIds (repG g))` (the canonical payload
graph).  Scouted field sources:

* `flat A` is `{A : AdmissibleSubgraph (repG g) // A ∈ properDisjointAdmissibleDivergent
  Subgraphs}` — `A.1` is the outer forest, `A.2` its properness.
* **`Aout`** := lift `A.1` (an `AdmissibleSubgraph (repG g) = AdmissibleSubgraph
  ((ofFlatGraphWithUniqueIds (repG g)).forget)`, via `forget_ofFlatGraphWithUniqueIds`) into
  `ResolvedAdmissibleSubgraph (ofFlatGraphWithUniqueIds (repG g))` by **`ofUniqueForgetForest`**
  (the forgetful-ambient lift, same-type round-trip).  The one technical step is the
  `forget`-transport of `A.1` along `forget_ofFlatGraphWithUniqueIds (repG g)`.
* **`starOf`** := the resolved lift of `FeynmanGraph.admissibleForestCanonicalStarOf` (public).
* **`starFresh`** := from canonical-star freshness (a fresh-vertex theorem — needs a public
  `h58Bridge` wrapper if private).
* **`componentPositiveEdges`** := from `A.2` (`properDisjointAdmissibleDivergentSubgraphs`
  membership ⟹ `HasPositiveInternalEdgesComponents`).
* **`parents`** := the inner proper-forest parents
  (`forestCoproductProperForestIndex (forestOuterQuotientHopfGen g A)`) lifted.
* **`containsAoutEdges`** := from the parent construction (may stay a field).

The construction is a fresh sub-sprint: the `forget`-transport for `Aout` + thin public
wrappers for the canonical-star freshness / inner-parent carrier (alias-only, no proof
change to `Coassoc`).  No facade, no new mathematics — `Aout`/`starOf`/`parents` are the
resolved lifts of the (public or wrappable) flat outer-forest data. -/

/-- (transport helper) Lift an admissible forest of *any* graph `G'` equal to the forgotten
unique-id graph, via `subst` on the free index `G'` (avoids `▸` motive failure on the
instance-dependent `AdmissibleSubgraph`). -/
private noncomputable def aoutOfTransport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hDisj : A.IsPairwiseDisjoint) :
    ResolvedAdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf) := by
  subst h; exact ofUniqueForgetForest A hDisj

/-- The transport helper's forget round-trip (heterogeneous — the forget lands in the
forgotten-graph coordinate). -/
private theorem forget_aoutOfTransport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hDisj : A.IsPairwiseDisjoint) :
    HEq (aoutOfTransport h A hDisj).forget A := by
  subst h; exact heq_of_eq (forget_ofUniqueForgetForest A hDisj)

/-- **InnerSupply-1a: `Aout` lift.**  The outer flat forest `A.1` (a proper-disjoint
admissible forest of `repG g`) lifted to a resolved admissible forest of the canonical
unique-id payload graph, via `ofUniqueForgetForest` along `forget_ofFlatGraphWithUniqueIds`. -/
noncomputable def canonicalOuterAoutOfFlatOuter (g : HopfGen) (A : h58BridgeOuterIndex g) :
    ResolvedAdmissibleSubgraph (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G :=
  aoutOfTransport (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1
    (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ A.2)

/-- **InnerSupply-1a: forget round-trip** (heterogeneous — the round-trip lands in the
forgotten-graph coordinate; this is the `forget`-transport made explicit, exactly as
anticipated). -/
theorem forget_canonicalOuterAoutOfFlatOuter (g : HopfGen) (A : h58BridgeOuterIndex g) :
    HEq (canonicalOuterAoutOfFlatOuter g A).forget A.1 :=
  forget_aoutOfTransport _ A.1 _

/-! ### InnerSupply-1b — the `starOf` lift (canonical component-star, forget coordinate)

`starOf` for the resolved σ-cover data is the resolved lift of the public
`FeynmanGraph.admissibleForestCanonicalStarOf`.  Since that flat star takes a flat
`FeynmanSubgraph` and `admissibleForestCanonicalStarOf` requires *no* membership, the lift
is just "forget the resolved component, feed the flat canonical star".  All of it stays in
the **forgotten** coordinate (the `subst`-eliminated free index), so no `▸`/`HEq` clutter
reaches the definition; the only transport is the same `subst` on `G'` used for `Aout`. -/

/-- (transport helper) The canonical component-star of an admissible forest of *any* graph
`G'` equal to the forgotten unique-id graph, evaluated on the *forgotten* resolved component
`η.forget`.  `subst` on the free index `G'` avoids the `▸` motive failure. -/
private noncomputable def starOfTransport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G')
    (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs)
    (η : ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf)) : VertexId := by
  subst h; exact FeynmanGraph.admissibleForestCanonicalStarOf _ A hA η.forget

/-- `aoutOfTransport` at `rfl` is definitionally the forgetful-ambient lift. -/
private theorem aoutOfTransport_rfl {Gf : FeynmanGraph}
    (A : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hDisj : A.IsPairwiseDisjoint) :
    aoutOfTransport rfl A hDisj = ofUniqueForgetForest A hDisj := rfl

/-- `starOfTransport` at `rfl` is definitionally the forget-then-canonical-star. -/
private theorem starOfTransport_rfl {Gf : FeynmanGraph}
    (A : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hA : A ∈ ((ofFlatGraphWithUniqueIds Gf).forget).properDisjointAdmissibleDivergentSubgraphs)
    (η : ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf)) :
    starOfTransport rfl A hA η
      = FeynmanGraph.admissibleForestCanonicalStarOf _ A hA η.forget := rfl

/-- The transport star is **fresh**: it lands outside the unique-id graph's vertices for
every component of the lifted forest.  (Forget preserves vertices definitionally, so the
flat `IsFreshStarAssignment.fresh` lands directly.) -/
private theorem starOfTransport_fresh {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G')
    (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs)
    {η : ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf)}
    (hη : η ∈ (aoutOfTransport h A
      (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA)).elements) :
    starOfTransport h A hA η ∉ (ofFlatGraphWithUniqueIds Gf).vertices := by
  subst h
  rw [aoutOfTransport_rfl, ofUniqueForgetForest_elements] at hη
  obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hη
  rw [starOfTransport_rfl, forget_liftUniqueFromForgetSubgraph]
  exact (FeynmanGraph.admissibleForestCanonicalStarOf_isFreshStarAssignment _ A hA).fresh hδf

/-- **InnerSupply-1b: `starOf` lift.**  The canonical component-star of the outer flat
forest `A.1`, lifted to the resolved σ-cover data's `starOf` (forget the resolved
component, feed the flat canonical star — no membership needed). -/
noncomputable def canonicalOuterStarOf (g : HopfGen) (A : h58BridgeOuterIndex g) :
    ResolvedFeynmanSubgraph (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G →
      VertexId :=
  starOfTransport (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2

/-- **InnerSupply-1b: `starFresh`.**  Every star of `canonicalOuterStarOf` lands outside the
canonical payload graph's vertices — the resolved σ-cover data's `starFresh` obligation. -/
theorem canonicalOuterStarOf_fresh (g : HopfGen) (A : h58BridgeOuterIndex g)
    {η : ResolvedFeynmanSubgraph (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G}
    (hη : η ∈ (canonicalOuterAoutOfFlatOuter g A).elements) :
    canonicalOuterStarOf g A η ∉
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.vertices :=
  starOfTransport_fresh (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2 hη

/-- (transport helper) `starOfTransport` is the flat canonical star of the (transported)
forgotten component. -/
private theorem starOfTransport_eq {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs)
    (η : ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf)) :
    starOfTransport h A hA η = FeynmanGraph.admissibleForestCanonicalStarOf G' A hA (h ▸ η.forget) := by
  subst h; rfl

/-- **S-2b: star alignment.**  `canonicalOuterStarOf` is the flat canonical star
(`h58BridgeOuterCanonicalStar`) of the forgotten component, transported along
`forget_ofFlatGraphWithUniqueIds`. -/
theorem canonicalOuterStarOf_forget (g : HopfGen) (A : h58BridgeOuterIndex g)
    (η : ResolvedFeynmanSubgraph (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G) :
    canonicalOuterStarOf g A η =
      h58BridgeOuterCanonicalStar g A
        (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph ▸ η.forget) :=
  starOfTransport_eq (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2 η

/-! ### S-2c — complement-faithful forget (the id-uniqueness payoff)

`Aout.complementEdges.map forget = A.1.complementEdges`.  `forget` commutes with the complement
subtraction because the subtracted forest edges are `≤` the ambient edges (`map` distributes
over `-` whenever `B ≤ A`, no injectivity needed); the *faithfulness* is that `Aout`'s edges
forget occurrence-faithfully to `A.1`'s (`canonicalOuterAout_internalEdges_forget`, from the
id-unique lift), unlike the lossy `ResolvedAdmissibleSubgraph.forget`. -/

/-- `Multiset.map` distributes over subtraction when the subtrahend is contained (no
injectivity needed). -/
private theorem multiset_map_sub_of_le' {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) {A B : Multiset α} (hBA : B ≤ A) :
    (A - B).map f = A.map f - B.map f := by
  calc (A - B).map f = ((A - B).map f + B.map f) - B.map f := by
        rw [Multiset.add_sub_cancel_right]
    _ = ((A - B + B).map f) - B.map f := by rw [Multiset.map_add]
    _ = A.map f - B.map f := by rw [Multiset.sub_add_cancel hBA]

/-- The transport forest's aggregate edges forget occurrence-faithfully to the flat forest's. -/
private theorem aoutOfTransport_internalEdges_forget {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hDisj : A.IsPairwiseDisjoint) :
    (aoutOfTransport h A hDisj).internalEdges.map ResolvedFeynmanEdge.forget = A.internalEdges := by
  subst h
  rw [aoutOfTransport_rfl]
  exact ofUniqueForgetForest_internalEdges_forget A hDisj

/-- The canonical outer forest's aggregate edges forget faithfully to `A.1`'s. -/
theorem canonicalOuterAout_internalEdges_forget (g : HopfGen) (A : h58BridgeOuterIndex g) :
    (canonicalOuterAoutOfFlatOuter g A).internalEdges.map ResolvedFeynmanEdge.forget
      = A.1.internalEdges :=
  aoutOfTransport_internalEdges_forget _ A.1 _

/-- **S-2c: complement-faithful forget.**  Forgetting the canonical outer forest's complement
edges recovers `A.1`'s complement edges — the id-uniqueness payoff making `forget` faithful
across the complement subtraction. -/
theorem map_forget_complementEdges_canonicalOuterAout (g : HopfGen)
    (A : h58BridgeOuterIndex g) :
    (canonicalOuterAoutOfFlatOuter g A).complementEdges.map ResolvedFeynmanEdge.forget
      = A.1.complementEdges := by
  have hle : (canonicalOuterAoutOfFlatOuter g A).internalEdges ≤
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.internalEdges :=
    resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise _
      (canonicalOuterAoutOfFlatOuter g A).isPairwiseDisjoint
  have hAmb : (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.internalEdges.map
      ResolvedFeynmanEdge.forget = (repG g).toFeynmanGraph.internalEdges :=
    map_forget_uniqueIdEdges (repG g).toFeynmanGraph.internalEdges
  show ((canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.internalEdges
      - (canonicalOuterAoutOfFlatOuter g A).internalEdges).map ResolvedFeynmanEdge.forget
      = A.1.complementEdges
  rw [multiset_map_sub_of_le' ResolvedFeynmanEdge.forget hle, hAmb,
    canonicalOuterAout_internalEdges_forget]
  rfl

/-! ### InnerSupply-1c — component positive-edge count

`componentPositiveEdges : ∀ η ∈ Aout.elements, 0 < η.internalEdges.card`.  The flat outer
forest `A.1` is a *proper* disjoint admissible forest, so membership in
`properDisjointAdmissibleDivergentSubgraphs` yields `HasPositiveInternalEdgesComponents`
(its fourth conjunct).  The unique-id lift preserves per-component edge count
(`liftUniqueFromForgetSubgraph_internalEdges_card`), so each lifted component inherits the
positive count — all in the forgotten coordinate. -/

/-- The transport forest has positive-edge components: every lifted component inherits the
flat forest's positive internal-edge count. -/
private theorem componentPositiveEdges_aoutOfTransport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G')
    (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs)
    {η : ResolvedFeynmanSubgraph (ofFlatGraphWithUniqueIds Gf)}
    (hη : η ∈ (aoutOfTransport h A
      (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA)).elements) :
    0 < η.internalEdges.card := by
  subst h
  rw [aoutOfTransport_rfl, ofUniqueForgetForest_elements] at hη
  obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hη
  rw [liftUniqueFromForgetSubgraph_internalEdges_card]
  exact ((((ofFlatGraphWithUniqueIds Gf).forget).mem_properDisjointAdmissibleDivergentSubgraphs
    A).mp hA).2.2.2 δf hδf

/-- **InnerSupply-1c: `componentPositiveEdges`.**  Every component of the lifted outer forest
has a positive internal-edge count — the resolved σ-cover data's `componentPositiveEdges`
obligation, from the flat forest's properness (`HasPositiveInternalEdgesComponents`). -/
theorem canonicalOuterComponentPositiveEdges (g : HopfGen) (A : h58BridgeOuterIndex g) :
    ∀ η ∈ (canonicalOuterAoutOfFlatOuter g A).elements, 0 < η.internalEdges.card :=
  fun _ hη => componentPositiveEdges_aoutOfTransport
    (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2 hη

/-! ### InnerSupply-1d — the `parents` data interface (de-contraction section, packaged)

The scout (above) found `parents` is **not** a liftable predicate field: it is the genuine
σ-cover insertion set (full subgraphs `γ ⊇ Aout`), and realizing it is the *same*
de-contraction section already isolated as the forest-case `cover` datum
(`ResolvedForestCaseSupply` / `parentOf`).  So rather than construct `parents` in isolation
(which would chase that obstruction twice), we **package it as a supplied datum**: a finite
parent set with the `containsAoutEdges` inclusion.  The four already-landed canonical fields
(`Aout`, `starOf`, `starFresh`, `componentPositiveEdges`) then assemble it into the full
`ResolvedSigmaCoverData` over the canonical payload graph. -/

/-- **InnerSupply-1d data interface.**  The genuine σ-cover parents over the canonical
payload graph: a finite parent set, each containing the canonical outer forest's edges.
This is the de-contraction section as a *supplied datum* (it coincides with the forest-case
`cover` obligation), not a separately-constructed field. -/
structure CanonicalOuterParentsData (g : HopfGen) (A : h58BridgeOuterIndex g) where
  /-- The σ-cover parents (full subgraphs of the payload graph). -/
  parents : Finset (ResolvedFeynmanSubgraph
    (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G)
  /-- Each parent contains the canonical outer forest's internal edges. -/
  containsAoutEdges : ∀ γ ∈ parents,
    (canonicalOuterAoutOfFlatOuter g A).internalEdges ≤ γ.internalEdges

/-- **InnerSupply-1d: assemble `ResolvedSigmaCoverData`.**  From the parents datum plus the
four already-landed canonical fields (`Aout` = `canonicalOuterAoutOfFlatOuter`, `starOf` =
`canonicalOuterStarOf`, `starFresh` = `canonicalOuterStarOf_fresh`, `componentPositiveEdges`
= `canonicalOuterComponentPositiveEdges`), the full resolved σ-cover data over the canonical
payload graph.  Every field is now sourced; `parents`/`containsAoutEdges` is the only
supplied datum (the de-contraction section). -/
noncomputable def canonicalSigmaCoverDataOfParents {g : HopfGen} {A : h58BridgeOuterIndex g}
    (P : CanonicalOuterParentsData g A) :
    ResolvedSigmaCoverData (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G where
  Aout := canonicalOuterAoutOfFlatOuter g A
  starOf := canonicalOuterStarOf g A
  parents := P.parents
  containsAoutEdges := P.containsAoutEdges
  starFresh := fun _ hη => canonicalOuterStarOf_fresh g A hη
  componentPositiveEdges := canonicalOuterComponentPositiveEdges g A

/-! ### InnerSupply-1d assembly — parents datum ⇒ canonical supply

The scout established that in the **carrier-based** layer the cover surjectivity is
*definitional* (`imageCarrier := forestCarrier.image toImage ∪ mixedCarrier.image toImage`,
so `cover_on` holds by construction).  Hence the canonical supply needs **no** separate
`cover`/`forestCaseSupply` field: once the σ-cover data `D` carries the supplied `parents`,
`branchCarriers` enumerates the forest/mixed image data over `D` and the layer is built
directly.  `CanonicalOuterResolvedSupplyData` packages the per-outer-forest supply with `D`
*derived* from the parents datum — the assembly that turns "supply genuine `parents`" into a
full `CanonicalResolvedActualSigmaCoverSupply g`. -/

/-- Per-outer-forest resolved supply, with `D` *derived* from the supplied parents datum.
Bundles the parents datum (the de-contraction section), the finite branch carriers over the
derived `D`, the resolved→flat index maps, and the flat split-term agreement. -/
structure CanonicalOuterResolvedSupplyData (g : HopfGen) (A : h58BridgeOuterIndex g) where
  /-- The σ-cover parents datum (de-contraction section). -/
  parentsData : CanonicalOuterParentsData g A
  /-- The finite branch carriers over the derived σ-cover data. -/
  branchCarriers : ResolvedBranchCarriers (canonicalSigmaCoverDataOfParents parentsData)
  /-- The resolved→flat index maps for the derived layer. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g
    (branchCarriers.toLayer
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.edgeIdsUnique g)
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.legIdsUnique g))
  /-- The flat split-term agreement. -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

/-- **InnerSupply-1d assembly.**  A per-outer-forest supply with `D` derived from the parents
datum reduces to the canonical supply (`D := canonicalSigmaCoverDataOfParents parentsData`). -/
noncomputable def CanonicalOuterResolvedSupplyData.toCanonicalSupply {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterResolvedSupplyData g A) :
    CanonicalResolvedActualSigmaCoverSupply g where
  D := canonicalSigmaCoverDataOfParents S.parentsData
  branchCarriers := S.branchCarriers
  concreteIndexMaps := S.concreteIndexMaps
  splitTerm_agreement := S.splitTerm_agreement

/-- The concrete H5.8 sum-reindex from the parents-datum supply. -/
theorem CanonicalOuterResolvedSupplyData.concrete_sum_reindex {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterResolvedSupplyData g A) :
    ∑ z ∈ S.toCanonicalSupply.toSupply.toActualSigmaCover.FL.imageCarrier,
        h58BridgeQuotientTerm g
          (S.toCanonicalSupply.toSupply.toActualSigmaCover.concreteData.flatImageOf z) =
      (∑ q ∈ S.toCanonicalSupply.toSupply.toActualSigmaCover.FL.forestCarrier,
          h58BridgeSplitChoiceTerm g
            (S.toCanonicalSupply.toSupply.toActualSigmaCover.concreteData.forestSplitOf q)) +
      (∑ q ∈ S.toCanonicalSupply.toSupply.toActualSigmaCover.FL.mixedCarrier,
          h58BridgeSplitChoiceTerm g
            (S.toCanonicalSupply.toSupply.toActualSigmaCover.concreteData.mixedSplitOf q)) :=
  S.toCanonicalSupply.concrete_sum_reindex

/-! ## DeContraction Scout — the parent-section carrier (the genuine `parents` source)

Target: a section of `resolvedParentRemnant Aout starOf` — for a contracted-graph subgraph
`δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)`, build a parent
`γ : ResolvedFeynmanSubgraph G` with `Aout.internalEdges ≤ γ.internalEdges` (containsAoutEdges)
and `resolvedParentRemnant Aout starOf γ = δ` (parent_remnant_eq).  This is the genuine
`CanonicalOuterParentsData` source (and, simultaneously, the forest-case `parentOf`).

**Forward map (fully characterised).**  `resolvedParentRemnant Aout starOf γ =
Aout.quotientRemainderSubgraph starOf γ`, with
```
vertices      := γ.vertices.image (Aout.retargetVertex starOf)
internalEdges := (γ.internalEdges - Aout.internalEdges).map (Aout.retargetEdge starOf)
externalLegs  := γ.externalLegs.map (Aout.retargetExternalLeg starOf)
```
where `retargetVertex` collapses each `Aout`-component to its star (identity off `Aout.vertices`)
and `retargetEdge`/`retargetExternalLeg` are **identity-preserving on `edgeId`/`legId`**.

**KEY FINDING — de-contraction is a submultiset preimage (the id-unique payload was built for
exactly this).**  Because `retargetEdge`/`retargetExternalLeg` keep ids and are **injective on
submultisets of `G.internalEdges`/`G.externalLegs`** under `EdgeIdsUnique`/`LegIdsUnique`
(`retarget_residual_edges_injective` / `retarget_residual_legs_injective`), the edge/leg parts
of the section are *uniquely determined* and *constructible*:
- `δ.internalEdges ≤ (Aout.contractWithStars starOf).internalEdges =
  Aout.complementEdges.map (Aout.retargetEdge starOf)`, so by **`exists_le_map`** there is a
  unique `M ≤ Aout.complementEdges` with `M.map (retargetEdge) = δ.internalEdges`.
- likewise a unique `L ≤ G.externalLegs` with `L.map (retargetExternalLeg) = δ.externalLegs`.

**Decided carrier.**
```
γ.internalEdges := Aout.internalEdges + M          -- M = edge preimage of δ in complementEdges
γ.externalLegs  := L                                -- L = leg preimage of δ
γ.vertices      := Aout.vertices
                     ∪ (endpoints of M in G) ∪ (attachments of L in G)
```
Then `γ.internalEdges - Aout.internalEdges = M` (M ≤ complementEdges = G.internalEdges -
Aout.internalEdges is disjoint from Aout.internalEdges), so the edge/leg halves of
`parent_remnant_eq` hold by construction, and `containsAoutEdges` is `Multiset.le_add_right`.

**HALT — the vertices half is the genuine residual.**  `parent_remnant_eq` needs
`γ.vertices.image (retargetVertex) = δ.vertices`.  With the carrier above, the image is
`Aout.starVertices ∪ (off-Aout endpoints/attachments of M,L)`.  This equals `δ.vertices`
**iff `δ` has no isolated vertices** (every vertex of `δ` is an endpoint of one of its edges
or an attachment of one of its legs) **and** the star vertices appearing in `δ` are exactly
the stars of the `Aout`-components met by `M`,`L`.  Both hold for the **genuine σ-cover
images** (connected-divergent components — the no-isolated-vertex campaign 6C-4/5/6 is
already resolved-side: `feynmanSubgraph_vertex_incident_edge_of_connected_pos` + forget
lift).  So the vertices law is *not* a new obstruction but the saturation argument already
proved for `remnant_vertex_recovery`, re-used in the forward direction.

**Minimal API to land (next sprint, in dependency order).**
1. `edgePreimage Aout starOf δ : Multiset ResolvedFeynmanEdge` (= `(exists_le_map …).choose`
   on `δ.internalEdges ≤ Aout.complementEdges.map retargetEdge`) + `_le` (≤ complementEdges)
   + `_map` (`.map retargetEdge = δ.internalEdges`).  Uniqueness: `retarget_residual_edges_injective`.
2. `legPreimage Aout starOf δ` + `_le` + `_map` (analogous, `retarget_residual_legs_injective`).
3. `parentOfQuotient Aout starOf δ : ResolvedFeynmanSubgraph G` (the carrier above) — the
   `vertices_subset`/`edges_supported`/`legs_supported` proofs from the preimage `_le` + the
   endpoint-union vertex set.
4. `parentOfQuotient_containsAoutEdges` (`le_add_right`) and `parentOfQuotient_remnant_eq`
   (edge/leg halves by `_map`; vertex half by the saturation lemma, restricted to genuine
   σ-cover `δ` — likely a hypothesis `δ` has-no-isolated-vertices / is the image of a CD
   forest).

**Facade check: clean.**  Everything above is the id-unique payload's own
`exists_le_map`/retarget-injectivity machinery + the resolved saturation lemmas.  No flat
facade (`ForestGraphInsertionUniquenessModel` is *replaced* by `retarget_residual_*_injective`;
`PromotedExternalLegsLiftableModel` is unused).  **Verdict: the parent-section is feasible
and its carrier is fixed; the only genuine content is the vertex-saturation law, which is the
forward use of the already-proved `remnant_vertex_recovery` saturation.** -/

/-! ### DeContraction-1 — `quotientEdgePreimage` (the edge half of the section)

The unique-up-to-`retargetEdge` submultiset of `Aout.complementEdges` that the contracted
subgraph `δ`'s internal edges come from.  Existence is `exists_le_map`; this is generic (no
id-uniqueness needed yet — uniqueness enters later for `parent_remnant_eq`). -/

/-- Existence of an edge preimage: `δ`'s internal edges are the `retargetEdge`-image of a
submultiset of `Aout.complementEdges` (since `δ.internalEdges ≤ (contract).internalEdges =
complementEdges.map retargetEdge`). -/
private theorem quotientEdgePreimage_exists
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    ∃ t ≤ Aout.complementEdges, t.map (Aout.retargetEdge starOf) = δ.internalEdges :=
  exists_le_map (Aout.retargetEdge starOf) (s := Aout.complementEdges) (M := δ.internalEdges)
    (by rw [← Aout.contractWithStars_internalEdges starOf]; exact δ.internalEdges_le)

/-- **DeContraction-1: the edge preimage.**  A submultiset of `Aout.complementEdges`
(`= G.internalEdges - Aout.internalEdges`) whose `retargetEdge`-image is `δ.internalEdges` —
the edge half of the parent-section carrier. -/
noncomputable def quotientEdgePreimage
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    Multiset ResolvedFeynmanEdge :=
  (quotientEdgePreimage_exists Aout starOf δ).choose

/-- The edge preimage lies in `Aout.complementEdges` (definitionally `G.internalEdges -
Aout.internalEdges`). -/
theorem quotientEdgePreimage_le
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    quotientEdgePreimage Aout starOf δ ≤ Aout.complementEdges :=
  (quotientEdgePreimage_exists Aout starOf δ).choose_spec.1

/-- The edge preimage retargets back to `δ`'s internal edges. -/
theorem quotientEdgePreimage_map
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    (quotientEdgePreimage Aout starOf δ).map (Aout.retargetEdge starOf) = δ.internalEdges :=
  (quotientEdgePreimage_exists Aout starOf δ).choose_spec.2

/-! ### DeContraction-1 — `quotientLegPreimage` (the leg half of the section)

Identical to the edge half, on `G.externalLegs` (no complement subtraction — the contracted
graph's legs are all of `G`'s legs retargeted). -/

/-- Existence of a leg preimage: `δ`'s external legs are the `retargetExternalLeg`-image of a
submultiset of `G.externalLegs` (since `δ.externalLegs ≤ (contract).externalLegs =
G.externalLegs.map retargetExternalLeg`). -/
private theorem quotientLegPreimage_exists
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    ∃ L ≤ G.externalLegs, L.map (Aout.retargetExternalLeg starOf) = δ.externalLegs :=
  exists_le_map (Aout.retargetExternalLeg starOf) (s := G.externalLegs) (M := δ.externalLegs)
    (by rw [← Aout.contractWithStars_externalLegs starOf]; exact δ.externalLegs_le)

/-- **DeContraction-1: the leg preimage.**  A submultiset of `G.externalLegs` whose
`retargetExternalLeg`-image is `δ.externalLegs` — the leg half of the parent-section carrier. -/
noncomputable def quotientLegPreimage
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    Multiset ResolvedExternalLeg :=
  (quotientLegPreimage_exists Aout starOf δ).choose

/-- The leg preimage lies in `G.externalLegs`. -/
theorem quotientLegPreimage_le
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    quotientLegPreimage Aout starOf δ ≤ G.externalLegs :=
  (quotientLegPreimage_exists Aout starOf δ).choose_spec.1

/-- The leg preimage retargets back to `δ`'s external legs. -/
theorem quotientLegPreimage_map
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) :
    (quotientLegPreimage Aout starOf δ).map (Aout.retargetExternalLeg starOf) = δ.externalLegs :=
  (quotientLegPreimage_exists Aout starOf δ).choose_spec.2

/-! ### DeContraction-2 — `parentOfQuotient` (the parent-section carrier)

The parent subgraph `γ ⊇ Aout` whose remnant is `δ`: edges `Aout.internalEdges + edgePreimage`,
legs `legPreimage`, vertices the `G`-vertices that are in `Aout` or are an endpoint of a
preimage edge/leg.  `vertices_subset` is the filter; `internalEdges_le` is
`Aout.internalEdges + (G.internalEdges - Aout.internalEdges) = G.internalEdges`; the support
proofs need only that `G` is **edge/leg-supported** (the well-formedness `hE`/`hL` — true for
the payload graph, raw `ResolvedFeynmanGraph` does not carry it). -/

/-- Membership in a resolved forest's aggregate internal edges (mirror of flat
`mem_internalEdges`). -/
private theorem resolvedAdmissible_mem_internalEdges
    {A : ResolvedAdmissibleSubgraph G} {e : ResolvedFeynmanEdge} :
    e ∈ A.internalEdges ↔ ∃ γ ∈ A.elements, e ∈ γ.internalEdges := by
  classical
  unfold ResolvedAdmissibleSubgraph.internalEdges
  induction A.elements using Finset.induction_on with
  | empty => simp
  | insert γ s hγs ih => simp [Finset.sum_insert, hγs, ih, Multiset.mem_add]

open Classical in
/-- **DeContraction-2: the parent-section carrier.**  For a contracted-graph subgraph `δ`,
the parent `γ ⊇ Aout` with edges `Aout.internalEdges + quotientEdgePreimage` and legs
`quotientLegPreimage`.  Requires `G` edge/leg-supported (`hE`/`hL`). -/
noncomputable def parentOfQuotient
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    ResolvedFeynmanSubgraph G where
  vertices := G.vertices.filter (fun v =>
    v ∈ Aout.vertices ∨
    (∃ e ∈ quotientEdgePreimage Aout starOf δ, e.source = v ∨ e.target = v) ∨
    (∃ ℓ ∈ quotientLegPreimage Aout starOf δ, ℓ.attachedTo = v))
  internalEdges := Aout.internalEdges + quotientEdgePreimage Aout starOf δ
  externalLegs := quotientLegPreimage Aout starOf δ
  vertices_subset := Finset.filter_subset _ _
  internalEdges_le := by
    have hle : Aout.internalEdges ≤ G.internalEdges :=
      resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise Aout Aout.isPairwiseDisjoint
    calc Aout.internalEdges + quotientEdgePreimage Aout starOf δ
        ≤ Aout.internalEdges + Aout.complementEdges := by
          gcongr
          exact quotientEdgePreimage_le Aout starOf δ
      _ = Aout.internalEdges + (G.internalEdges - Aout.internalEdges) := by
          rw [ResolvedAdmissibleSubgraph.complementEdges]
      _ = G.internalEdges := add_tsub_cancel_of_le hle
  externalLegs_le := quotientLegPreimage_le Aout starOf δ
  edges_supported := by
    intro e he
    rw [Multiset.mem_add] at he
    rcases he with heA | heM
    · obtain ⟨γ, hγ, heγ⟩ := resolvedAdmissible_mem_internalEdges.mp heA
      obtain ⟨hs, ht⟩ := γ.edges_supported e heγ
      have heG : e ∈ G.internalEdges := Multiset.mem_of_le
        (resolvedAdmissibleSubgraph_internalEdges_le_of_pairwise Aout Aout.isPairwiseDisjoint) heA
      obtain ⟨hsG, htG⟩ := hE e heG
      exact ⟨Finset.mem_filter.mpr ⟨hsG, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr
              ⟨γ, hγ, hs⟩)⟩,
             Finset.mem_filter.mpr ⟨htG, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr
              ⟨γ, hγ, ht⟩)⟩⟩
    · have hsub : quotientEdgePreimage Aout starOf δ ≤ G.internalEdges :=
        le_trans (quotientEdgePreimage_le Aout starOf δ)
          (by rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self)
      have heG : e ∈ G.internalEdges := Multiset.mem_of_le hsub heM
      obtain ⟨hsG, htG⟩ := hE e heG
      exact ⟨Finset.mem_filter.mpr ⟨hsG, Or.inr (Or.inl ⟨e, heM, Or.inl rfl⟩)⟩,
             Finset.mem_filter.mpr ⟨htG, Or.inr (Or.inl ⟨e, heM, Or.inr rfl⟩)⟩⟩
  legs_supported := by
    intro ℓ hℓ
    have hℓG : ℓ ∈ G.externalLegs := Multiset.mem_of_le (quotientLegPreimage_le Aout starOf δ) hℓ
    exact Finset.mem_filter.mpr ⟨hL ℓ hℓG, Or.inr (Or.inr ⟨ℓ, hℓ, rfl⟩)⟩

open Classical in
@[simp] theorem parentOfQuotient_vertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (parentOfQuotient Aout starOf δ hE hL).vertices = G.vertices.filter (fun v =>
      v ∈ Aout.vertices ∨
      (∃ e ∈ quotientEdgePreimage Aout starOf δ, e.source = v ∨ e.target = v) ∨
      (∃ ℓ ∈ quotientLegPreimage Aout starOf δ, ℓ.attachedTo = v)) := rfl

/-- **DeContraction-2: `containsAoutEdges`.**  The parent contains the outer forest's edges
(by construction: its edges are `Aout.internalEdges + _`). -/
theorem parentOfQuotient_containsAoutEdges
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    Aout.internalEdges ≤ (parentOfQuotient Aout starOf δ hE hL).internalEdges := by
  show Aout.internalEdges ≤ Aout.internalEdges + quotientEdgePreimage Aout starOf δ
  exact Multiset.le_add_right _ _

/-- **DeContraction-2: remnant internal edges.**  The parent's remnant has exactly `δ`'s
internal edges — the edge half of `parent_remnant_eq` (constructive: `(Aout + M) - Aout = M`,
then `quotientEdgePreimage_map`). -/
theorem parentOfQuotient_remnant_internalEdges
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (resolvedParentRemnant Aout starOf (parentOfQuotient Aout starOf δ hE hL)).internalEdges
      = δ.internalEdges := by
  show ((Aout.internalEdges + quotientEdgePreimage Aout starOf δ) - Aout.internalEdges).map
    (Aout.retargetEdge starOf) = δ.internalEdges
  rw [add_tsub_cancel_left]
  exact quotientEdgePreimage_map Aout starOf δ

/-- **DeContraction-2: remnant external legs.**  The parent's remnant has exactly `δ`'s
external legs — the leg half of `parent_remnant_eq` (`quotientLegPreimage_map`). -/
theorem parentOfQuotient_remnant_externalLegs
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (resolvedParentRemnant Aout starOf (parentOfQuotient Aout starOf δ hE hL)).externalLegs
      = δ.externalLegs := by
  show (quotientLegPreimage Aout starOf δ).map (Aout.retargetExternalLeg starOf) = δ.externalLegs
  exact quotientLegPreimage_map Aout starOf δ

/-! ### DeContraction-3 Scout — the all-star vertex knife-edge

The edge/leg halves of `parent_remnant_eq` are done.  The vertex half
`(parentOfQuotient …).vertices.image (Aout.retargetVertex starOf) = δ.vertices` runs into a
**structural obstruction**, identified here before committing to a proof.

**Observation (all-star containment).**  `parentOfQuotient` puts `Aout.vertices` wholesale into
its vertex filter (`v ∈ Aout.vertices ∨ …`), because `containsAoutEdges` forces the parent to
contain *all* of `Aout`'s edges and (with `componentPositiveEdges` ⟹ no isolated vertices) all
of `Aout.vertices`.  Hence the remnant's vertices
`= (parentOfQuotient …).vertices.image (Aout.retargetVertex starOf)` contain `retargetVertex w =
starOf (componentAt w)` for *every* component's vertex `w` — i.e. **the remnant contains the
entire `Aout.starVertices` (all outer stars).**

**Necessary condition for `parent_remnant_eq`.**  Therefore `resolvedParentRemnant … = δ`
forces `Aout.starVertices starOf ⊆ δ.vertices`: the target component `δ` must contain **all**
outer stars.

**But genuine forest images need not.**  The discriminator `resolvedIsForestByStar` (and its
flat original) only asserts *some* component meets *some* star:
`∃ δ ∈ img.elements, ¬ Disjoint δ.vertices (Aout.starVertices)`.  And
`forest_case_of_preimageData` lifts **each component `δ ∈ z.elements` separately** via
`parentOf`, proving `remnantDisjoint` from `z.pairwiseDisjoint` *after* `parent_remnant_eq`
rewrites each remnant to its `δ`.  So if a forest-by-star image `z` has ≥2 components, each
`δ` is a *small* (often single-star) piece — **not containing all stars** — and the
all-star-containing `parentOfQuotient δ` remnant cannot equal it.  (Equivalently: two parents
`⊇ Aout` both yield remnants containing all stars, so their remnants are never disjoint —
incompatible with `remnantDisjoint` for a genuine multi-component forest.)

**Verdict — the framing knife-edge (the user's earlier prediction).**  `resolvedForestImage`
quotients by the **whole** `Aout`, collapsing every component to its star, so any parent
`⊇ Aout` exposes all stars.  This is consistent **only** when the forest-branch image is the
*single* quotient of *one* parent (`choiceParents` a singleton, `z` = that one quotient, which
genuinely contains all stars).  For a multi-component inner forest, the per-component
`parentOf δ` of the de-contraction is **over-strong** — `containsAoutEdges` (parent ⊇ whole
`Aout`) does not match a small inner component `δ`.

**Decision needed (architectural, before proving the vertex half).**  Either:
- **(i) single-parent forest images** — accept that each `ResolvedForestImageData` has a
  singleton `choiceParents` (`z` = one full quotient `γ/Aout`, which contains all stars); then
  `parentOfQuotient` works and `parent_remnant_eq` needs only `Aout.starVertices ⊆ δ.vertices`
  with `δ = z` the full quotient.  Matches the CK *insertion* picture (one divergent `γ ⊇ Aout`,
  one cograph `γ/Aout`); the multi-component RHS is recovered by summing over *outer forests*
  (the existing `ResolvedH58OuterSkeleton` outer sum), not by multi-component inner images.
- **(ii) per-component `Aout`** — make the σ-cover's `Aout` a *single* outer component (so
  `resolvedParentRemnant` quotients by just that component); each inner `δ` then touches only
  that one star.  This changes `ResolvedSigmaCoverData` to per-component, a larger refactor.
- **(iii) restrict the forest-case datum** — keep `Aout` the whole forest but supply
  `parentOf` only for images that genuinely contain all stars, documenting the rest as handled
  by the mixed branch / outer sum.

Recommendation: **(i)** — it requires no refactor (the outer sum already supplies the
multi-forest RHS), and the vertex half then reduces to the clean
`Aout.starVertices ⊆ δ.vertices` (a single hypothesis, true for full quotients).  The next
landing would be `parent_remnant_eq` for `δ` = a full quotient image, with `hStars :
Aout.starVertices starOf ⊆ δ.vertices` as the explicit hypothesis. -/

/-! ### DeContraction-3 — single-parent forest image (the correct granularity)

Per the all-star scout (decision (i)): a forest-branch image is the quotient remnant of a
**single** parent, so `choiceParents` is a singleton, `remnantDisjoint` is trivial, and the
image's one component genuinely contains all outer stars.  (The multi-forest RHS is recovered
by the outer-forest sum, not by multi-component inner images.) -/

/-- A forest-branch image from a **single** parent (`choiceParents := {parent}`).  The
consistent granularity: `remnantDisjoint` is trivial, and the image is the one quotient
remnant of `parent`. -/
noncomputable def singletonForestImageDataOfParent (D : ResolvedSigmaCoverData G)
    (parent : ResolvedForestIdx D)
    (hCD : (resolvedForestImage D parent).forget.IsConnectedDivergent)
    (hStar : ¬ Disjoint (resolvedForestImage D parent).vertices (D.Aout.starVertices D.starOf)) :
    ResolvedForestImageData D where
  choiceParents := {parent}
  remnantCD := by intro γ hγ; rw [Finset.mem_singleton] at hγ; subst hγ; exact hCD
  remnantDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    rw [Finset.mem_singleton] at h₁ h₂; subst h₁; subst h₂; exact absurd rfl hne
  starWitness := ⟨parent, Finset.mem_singleton_self parent, hStar⟩

/-- The singleton forest image is the single quotient remnant of its parent. -/
@[simp] theorem singletonForestImageDataOfParent_toImage_elements (D : ResolvedSigmaCoverData G)
    (parent : ResolvedForestIdx D)
    (hCD : (resolvedForestImage D parent).forget.IsConnectedDivergent)
    (hStar : ¬ Disjoint (resolvedForestImage D parent).vertices (D.Aout.starVertices D.starOf)) :
    (singletonForestImageDataOfParent D parent hCD hStar).toImage.elements
      = {resolvedForestImage D parent} := by
  show ({parent} : Finset (ResolvedForestIdx D)).image (resolvedForestImage D)
    = {resolvedForestImage D parent}
  exact Finset.image_singleton (resolvedForestImage D) parent

/-- The singleton forest image satisfies the forest discriminator (inherited from
`forest_sat`). -/
theorem singletonForestImageDataOfParent_forest_sat (D : ResolvedSigmaCoverData G)
    (parent : ResolvedForestIdx D)
    (hCD : (resolvedForestImage D parent).forget.IsConnectedDivergent)
    (hStar : ¬ Disjoint (resolvedForestImage D parent).vertices (D.Aout.starVertices D.starOf)) :
    resolvedIsForestByStar D (singletonForestImageDataOfParent D parent hCD hStar).toImage :=
  (singletonForestImageDataOfParent D parent hCD hStar).forest_sat

/-- Singleton forest images are injective in their parent: equal chosen-parent singletons
force equal parents. -/
theorem singletonForestImageDataOfParent_inj (D : ResolvedSigmaCoverData G)
    {p₁ p₂ : ResolvedForestIdx D}
    {hCD₁ hStar₁} {hCD₂ hStar₂}
    (h : (singletonForestImageDataOfParent D p₁ hCD₁ hStar₁).choiceParents
       = (singletonForestImageDataOfParent D p₂ hCD₂ hStar₂).choiceParents) :
    p₁ = p₂ :=
  Finset.singleton_inj.mp h

/-! ### DeContraction-3 — `parent_remnant_eq` vertex half, ⊆ direction

The forward inclusion `(parent).vertices.image retargetVertex ⊆ δ.vertices`: each vertex of
the parent retargets into `δ` — `Aout` vertices to stars (`hStars`), preimage-edge/leg
endpoints to `δ`'s supported endpoints. -/

open Classical in
/-- **⊆ direction of the vertex half.**  The parent's remnant vertices are contained in `δ`
(given `hStars : Aout.starVertices ⊆ δ.vertices`). -/
theorem parentOfQuotient_remnant_vertices_subset
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hStars : Aout.starVertices starOf ⊆ δ.vertices) :
    (parentOfQuotient Aout starOf δ hE hL).vertices.image (Aout.retargetVertex starOf)
      ⊆ δ.vertices := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  rw [parentOfQuotient_vertices, Finset.mem_filter] at hu
  obtain ⟨_, hcase⟩ := hu
  rcases hcase with hAout | ⟨e, he, hsrc⟩ | ⟨ℓ, hℓ, hatt⟩
  · rw [retargetVertex_eq_star_of_mem Aout starOf hAout]
    exact hStars (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
      ⟨Aout.componentAt hAout, Aout.componentAt_mem hAout, rfl⟩)
  · have hmem : Aout.retargetEdge starOf e ∈ δ.internalEdges := by
      have h := Multiset.mem_map_of_mem (Aout.retargetEdge starOf) he
      rwa [quotientEdgePreimage_map] at h
    obtain ⟨hs, ht⟩ := δ.edges_supported _ hmem
    rcases hsrc with rfl | rfl
    · exact hs
    · exact ht
  · have hmem : Aout.retargetExternalLeg starOf ℓ ∈ δ.externalLegs := by
      have h := Multiset.mem_map_of_mem (Aout.retargetExternalLeg starOf) hℓ
      rwa [quotientLegPreimage_map] at h
    have hs := δ.legs_supported _ hmem
    rw [← hatt]
    exact hs

/-! ### DeContraction-3 — `parent_remnant_eq` vertex half, ⊇ direction

The reverse inclusion needs that every vertex of `δ` is *covered* — a star, or an endpoint of
one of `δ`'s edges/legs (so it has a preimage that retargets onto it).  Packaged as
`QuotientVertexCovered` (the saturation datum, true for genuine σ-cover images: no isolated
vertices). -/

/-- A carrier vertex retargets to its element's star (the `componentAt` is that element, by
pairwise-disjointness). -/
theorem retargetVertex_eq_star_of_mem_element
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    {η : ResolvedFeynmanSubgraph G} (hη : η ∈ Aout.elements)
    {u : VertexId} (hu : u ∈ η.vertices) :
    Aout.retargetVertex starOf u = starOf η := by
  have huA : u ∈ Aout.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨η, hη, hu⟩
  rw [retargetVertex_eq_star_of_mem Aout starOf huA]
  congr 1
  by_contra hne
  exact Finset.disjoint_left.mp (Aout.pairwiseDisjoint (Aout.componentAt_mem huA) hη hne)
    (Aout.componentAt_vertex_mem huA) hu

/-- **Saturation datum.**  Every vertex of the contracted-graph subgraph `δ` is an outer star
or an endpoint of one of `δ`'s edges/legs (no isolated vertices) — true for genuine σ-cover
forest images. -/
def QuotientVertexCovered (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)) : Prop :=
  ∀ w ∈ δ.vertices,
    w ∈ Aout.starVertices starOf ∨
      (∃ e ∈ δ.internalEdges, e.source = w ∨ e.target = w) ∨
      (∃ l ∈ δ.externalLegs, l.attachedTo = w)

open Classical in
/-- **⊇ direction of the vertex half.**  Every vertex of `δ` is the retarget of a parent
vertex — stars via a component vertex (`hCompNonempty`), edge/leg endpoints via their
preimage in the parent. -/
theorem parentOfQuotient_vertices_subset_remnant
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hCompNonempty : ∀ η ∈ Aout.elements, η.vertices.Nonempty)
    (hCovered : QuotientVertexCovered Aout starOf δ) :
    δ.vertices ⊆ (parentOfQuotient Aout starOf δ hE hL).vertices.image
      (Aout.retargetVertex starOf) := by
  intro w hw
  rcases hCovered w hw with hStar | ⟨e, heδ, hw'⟩ | ⟨ℓ, hℓδ, hw'⟩
  · obtain ⟨η, hη, rfl⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hStar
    obtain ⟨u, hu⟩ := hCompNonempty η hη
    refine Finset.mem_image.mpr ⟨u, ?_, retargetVertex_eq_star_of_mem_element Aout starOf hη hu⟩
    rw [parentOfQuotient_vertices, Finset.mem_filter]
    exact ⟨η.vertices_subset hu, Or.inl (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨η, hη, hu⟩)⟩
  · rw [← quotientEdgePreimage_map] at heδ
    obtain ⟨e0, he0, rfl⟩ := Multiset.mem_map.mp heδ
    have he0G : e0 ∈ G.internalEdges := Multiset.mem_of_le
      (le_trans (quotientEdgePreimage_le Aout starOf δ)
        (by rw [ResolvedAdmissibleSubgraph.complementEdges]; exact tsub_le_self)) he0
    rcases hw' with hw' | hw'
    · refine Finset.mem_image.mpr ⟨e0.source, ?_, hw'⟩
      rw [parentOfQuotient_vertices, Finset.mem_filter]
      exact ⟨(hE e0 he0G).1, Or.inr (Or.inl ⟨e0, he0, Or.inl rfl⟩)⟩
    · refine Finset.mem_image.mpr ⟨e0.target, ?_, hw'⟩
      rw [parentOfQuotient_vertices, Finset.mem_filter]
      exact ⟨(hE e0 he0G).2, Or.inr (Or.inl ⟨e0, he0, Or.inr rfl⟩)⟩
  · rw [← quotientLegPreimage_map] at hℓδ
    obtain ⟨ℓ0, hℓ0, rfl⟩ := Multiset.mem_map.mp hℓδ
    refine Finset.mem_image.mpr ⟨ℓ0.attachedTo, ?_, hw'⟩
    rw [parentOfQuotient_vertices, Finset.mem_filter]
    exact ⟨hL ℓ0 (Multiset.mem_of_le (quotientLegPreimage_le Aout starOf δ) hℓ0),
      Or.inr (Or.inr ⟨ℓ0, hℓ0, rfl⟩)⟩

/-- **DeContraction-3: `parent_remnant_eq`.**  The remnant of `parentOfQuotient` is exactly
`δ` — the de-contraction section is a genuine section of `resolvedParentRemnant`.  Assembled
from the edge/leg halves (constructive) and the vertex half (`hStars` + saturation
`hCovered`/`hCompNonempty`). -/
theorem parentOfQuotient_remnant_eq
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (Aout.contractWithStars starOf))
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices)
    (hCompNonempty : ∀ η ∈ Aout.elements, η.vertices.Nonempty)
    (hStars : Aout.starVertices starOf ⊆ δ.vertices)
    (hCovered : QuotientVertexCovered Aout starOf δ) :
    resolvedParentRemnant Aout starOf (parentOfQuotient Aout starOf δ hE hL) = δ := by
  apply ResolvedFeynmanSubgraph.ext
  · exact Finset.Subset.antisymm
      (parentOfQuotient_remnant_vertices_subset Aout starOf δ hE hL hStars)
      (parentOfQuotient_vertices_subset_remnant Aout starOf δ hE hL hCompNonempty hCovered)
  · exact parentOfQuotient_remnant_internalEdges Aout starOf δ hE hL
  · exact parentOfQuotient_remnant_externalLegs Aout starOf δ hE hL

/-! ### DeContraction-4 — payload well-formedness + parents-from-quotient-carrier

The de-contraction needs the ambient graph edge/leg-supported (`hE`/`hL`).  For the canonical
payload graph this is `repG_wellFormed` transported through `ofFlatGraphWithUniqueIds`
(`forget` keeps endpoints; the id-tag does not move them).  Then a finite quotient-image
carrier yields a `CanonicalOuterParentsData` by imaging `parentOfQuotient` — non-circular
(the carrier is supplied externally, not derived from `D.parents`). -/

/-- The unique-id lift of a well-formed flat graph is edge-supported. -/
theorem ofFlatGraphWithUniqueIds_edges_supported {Gf : FeynmanGraph} (hGf : Gf.WellFormed) :
    ∀ e ∈ (ofFlatGraphWithUniqueIds Gf).internalEdges,
      e.source ∈ (ofFlatGraphWithUniqueIds Gf).vertices ∧
        e.target ∈ (ofFlatGraphWithUniqueIds Gf).vertices := by
  intro e he
  have hfe : e.forget ∈ Gf.internalEdges := by
    rw [← map_forget_uniqueIdEdges Gf.internalEdges]
    exact Multiset.mem_map_of_mem ResolvedFeynmanEdge.forget he
  have hsupp := hGf.1 e.forget hfe
  rw [FeynmanEdge.supportedOn_def] at hsupp
  exact hsupp

/-- The unique-id lift of a well-formed flat graph is leg-supported. -/
theorem ofFlatGraphWithUniqueIds_legs_supported {Gf : FeynmanGraph} (hGf : Gf.WellFormed) :
    ∀ ℓ ∈ (ofFlatGraphWithUniqueIds Gf).externalLegs,
      ℓ.attachedTo ∈ (ofFlatGraphWithUniqueIds Gf).vertices := by
  intro ℓ hℓ
  have hfℓ : ℓ.forget ∈ Gf.externalLegs := by
    rw [← map_forget_uniqueIdLegs Gf.externalLegs]
    exact Multiset.mem_map_of_mem ResolvedExternalLeg.forget hℓ
  have hsupp := hGf.2 ℓ.forget hfℓ
  rw [ExternalLeg.supportedOn_def] at hsupp
  exact hsupp

/-- The canonical payload graph is edge-supported (`hE` for `parentOfQuotient`). -/
theorem canonicalPayload_edges_supported (g : HopfGen) :
    ∀ e ∈ (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.internalEdges,
      e.source ∈ (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.vertices ∧
        e.target ∈ (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.vertices :=
  ofFlatGraphWithUniqueIds_edges_supported (repG_wellFormed g)

/-- The canonical payload graph is leg-supported (`hL` for `parentOfQuotient`). -/
theorem canonicalPayload_legs_supported (g : HopfGen) :
    ∀ ℓ ∈ (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.externalLegs,
      ℓ.attachedTo ∈ (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.vertices :=
  ofFlatGraphWithUniqueIds_legs_supported (repG_wellFormed g)

/-- **DeContraction-4: parents from a quotient-image carrier.**  An externally-supplied finite
carrier of contracted-graph subgraphs yields a `CanonicalOuterParentsData` by imaging
`parentOfQuotient` — non-circular (the carrier is *not* derived from `D.parents`).  This is
the genuine `parents` source the σ-cover needs. -/
noncomputable def canonicalOuterParentsDataOfQuotientCarrier (g : HopfGen)
    (A : h58BridgeOuterIndex g)
    (quotientCarrier : Finset (ResolvedFeynmanSubgraph
      ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)))) :
    CanonicalOuterParentsData g A where
  parents := quotientCarrier.image (fun δ =>
    parentOfQuotient (canonicalOuterAoutOfFlatOuter g A) (canonicalOuterStarOf g A) δ
      (canonicalPayload_edges_supported g) (canonicalPayload_legs_supported g))
  containsAoutEdges := by
    intro γ hγ
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp hγ
    exact parentOfQuotient_containsAoutEdges (canonicalOuterAoutOfFlatOuter g A)
      (canonicalOuterStarOf g A) δ (canonicalPayload_edges_supported g)
      (canonicalPayload_legs_supported g)

/-- The de-contracted parent of a quotient carrier element lies in the canonical parents. -/
theorem parentOfQuotient_mem_canonicalParents (g : HopfGen) (A : h58BridgeOuterIndex g)
    (quotientCarrier : Finset (ResolvedFeynmanSubgraph
      ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A))))
    {δ : ResolvedFeynmanSubgraph
      ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A))}
    (hδ : δ ∈ quotientCarrier) :
    parentOfQuotient (canonicalOuterAoutOfFlatOuter g A) (canonicalOuterStarOf g A) δ
        (canonicalPayload_edges_supported g) (canonicalPayload_legs_supported g)
      ∈ (canonicalSigmaCoverDataOfParents
          (canonicalOuterParentsDataOfQuotientCarrier g A quotientCarrier)).parents :=
  Finset.mem_image_of_mem _ hδ

/-- The canonical outer forest's components are vertex-nonempty (each has a positive-edge,
hence an endpoint). -/
theorem canonicalOuterAout_components_nonempty (g : HopfGen) (A : h58BridgeOuterIndex g) :
    ∀ η ∈ (canonicalOuterAoutOfFlatOuter g A).elements, η.vertices.Nonempty := by
  intro η hη
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero
    (Multiset.card_pos.mp (canonicalOuterComponentPositiveEdges g A η hη))
  exact ⟨e.source, (η.edges_supported e he).1⟩

/-! ### S-2d — retargetVertex alignment (forget coordinate, componentAt-choose-free)

The resolved star-contraction's `retargetVertex` agrees with the flat one — proved
membership-based (no `componentAt` choose): a carrier vertex retargets to its component's star
on both sides (`retargetVertex_eq_star_of_mem_element` resolved / `retargetVertex_of_mem_component`
flat), and the lifted component's star is the flat component's (`forget_liftUnique…`). -/

/-- The forgetful-lift forest has the same vertex carrier as the flat forest. -/
theorem ofUniqueForgetForest_vertices {Gf : FeynmanGraph}
    (A : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget) (hDisj : A.IsPairwiseDisjoint) :
    (ofUniqueForgetForest A hDisj).vertices = A.vertices := by
  apply Finset.ext
  intro v
  rw [ResolvedAdmissibleSubgraph.mem_vertices, AdmissibleSubgraph.mem_vertices,
    ofUniqueForgetForest_elements]
  constructor
  · rintro ⟨γ, hγ, hv⟩
    obtain ⟨δf, hδf, rfl⟩ := Finset.mem_image.mp hγ
    exact ⟨δf, hδf, hv⟩
  · rintro ⟨δf, hδf, hv⟩
    exact ⟨liftUniqueFromForgetSubgraph δf, Finset.mem_image_of_mem _ hδf, hv⟩

/-- **S-2d: retargetVertex alignment (forget coordinate).**  The resolved star-contraction
retarget through the lifted forest equals the flat retarget through `A` with the flat canonical
star. -/
theorem ofUniqueForgetForest_retargetVertex_eq {Gf : FeynmanGraph}
    (A : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hA : A ∈ ((ofFlatGraphWithUniqueIds Gf).forget).properDisjointAdmissibleDivergentSubgraphs)
    (v : VertexId) :
    (ofUniqueForgetForest A
        (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint
          _ hA)).retargetVertex
        (fun η => FeynmanGraph.admissibleForestCanonicalStarOf
          ((ofFlatGraphWithUniqueIds Gf).forget) A hA η.forget) v
      = A.retargetVertex
          (FeynmanGraph.admissibleForestCanonicalStarOf
            ((ofFlatGraphWithUniqueIds Gf).forget) A hA) v := by
  have hDisj := FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA
  by_cases hv : v ∈ A.vertices
  · obtain ⟨δf, hδf, hvδ⟩ := AdmissibleSubgraph.mem_vertices.mp hv
    have hlift : liftUniqueFromForgetSubgraph δf ∈ (ofUniqueForgetForest A hDisj).elements := by
      rw [ofUniqueForgetForest_elements]; exact Finset.mem_image_of_mem _ hδf
    rw [retargetVertex_eq_star_of_mem_element (ofUniqueForgetForest A hDisj) _ hlift hvδ,
      forget_liftUniqueFromForgetSubgraph,
      AdmissibleSubgraph.retargetVertex_of_mem_component hDisj _ hδf hvδ]
  · rw [A.retargetVertex_of_not_mem _ hv,
      (ofUniqueForgetForest A hDisj).retargetVertex_of_not_mem _
        (by rw [ofUniqueForgetForest_vertices]; exact hv)]

/-- (transport) Canonical-level retargetVertex alignment from the forget-coordinate one. -/
private theorem retargetVertex_canonicalOuter_transport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs)
    (v : VertexId) :
    (aoutOfTransport h A
        (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA)).retargetVertex
        (starOfTransport h A hA) v
      = A.retargetVertex (FeynmanGraph.admissibleForestCanonicalStarOf G' A hA) v := by
  subst h
  rw [aoutOfTransport_rfl]
  exact ofUniqueForgetForest_retargetVertex_eq A hA v

/-- **S-2d (canonical): retargetVertex alignment.**  The canonical resolved retarget equals the
flat retarget with the flat canonical star. -/
theorem canonicalOuter_retargetVertex_eq (g : HopfGen) (A : h58BridgeOuterIndex g) (v : VertexId) :
    (canonicalOuterAoutOfFlatOuter g A).retargetVertex (canonicalOuterStarOf g A) v
      = A.1.retargetVertex (h58BridgeOuterCanonicalStar g A) v :=
  retargetVertex_canonicalOuter_transport
    (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2 v

/-- **S-2d: edge retarget alignment.**  Forgetting the resolved retargeted edge equals the flat
retargeted edge of the forgotten edge (rides on the retargetVertex alignment). -/
theorem canonicalOuter_retargetEdge_forget (g : HopfGen) (A : h58BridgeOuterIndex g)
    (e : ResolvedFeynmanEdge) :
    ((canonicalOuterAoutOfFlatOuter g A).retargetEdge (canonicalOuterStarOf g A) e).forget
      = A.1.retargetEdge (h58BridgeOuterCanonicalStar g A) e.forget := by
  show FeynmanEdge.mk
      ((canonicalOuterAoutOfFlatOuter g A).retargetVertex (canonicalOuterStarOf g A) e.source)
      ((canonicalOuterAoutOfFlatOuter g A).retargetVertex (canonicalOuterStarOf g A) e.target)
      e.sector
    = FeynmanEdge.mk
      (A.1.retargetVertex (h58BridgeOuterCanonicalStar g A) e.source)
      (A.1.retargetVertex (h58BridgeOuterCanonicalStar g A) e.target) e.sector
  rw [canonicalOuter_retargetVertex_eq g A e.source, canonicalOuter_retargetVertex_eq g A e.target]

/-- **S-2d: leg retarget alignment.** -/
theorem canonicalOuter_retargetLeg_forget (g : HopfGen) (A : h58BridgeOuterIndex g)
    (l : ResolvedExternalLeg) :
    ((canonicalOuterAoutOfFlatOuter g A).retargetExternalLeg (canonicalOuterStarOf g A) l).forget
      = A.1.retargetExternalLeg (h58BridgeOuterCanonicalStar g A) l.forget := by
  show ExternalLeg.mk
      ((canonicalOuterAoutOfFlatOuter g A).retargetVertex (canonicalOuterStarOf g A) l.attachedTo)
      l.sector
    = ExternalLeg.mk
      (A.1.retargetVertex (h58BridgeOuterCanonicalStar g A) l.attachedTo) l.sector
  rw [canonicalOuter_retargetVertex_eq g A l.attachedTo]

/-! ### S-2e-pre — ambient legs forget + starVertices alignment -/

/-- The canonical payload graph's external legs forget to `repG g`'s (mirror of the edge case). -/
theorem canonicalPayload_externalLegs_forget (g : HopfGen) :
    (canonicalResolvedHopfPayloadFamilyWithUniqueIds.payload g).G.externalLegs.map
        ResolvedExternalLeg.forget = (repG g).toFeynmanGraph.externalLegs :=
  map_forget_uniqueIdLegs (repG g).toFeynmanGraph.externalLegs

/-- The forgetful-lift forest's star vertices equal the flat forest's (forget coordinate). -/
theorem ofUniqueForgetForest_starVertices_eq {Gf : FeynmanGraph}
    (A : AdmissibleSubgraph (ofFlatGraphWithUniqueIds Gf).forget)
    (hA : A ∈ ((ofFlatGraphWithUniqueIds Gf).forget).properDisjointAdmissibleDivergentSubgraphs) :
    (ofUniqueForgetForest A
        (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA)).starVertices
        (fun η => FeynmanGraph.admissibleForestCanonicalStarOf
          ((ofFlatGraphWithUniqueIds Gf).forget) A hA η.forget)
      = A.starVertices
          (FeynmanGraph.admissibleForestCanonicalStarOf ((ofFlatGraphWithUniqueIds Gf).forget) A hA) := by
  unfold ResolvedAdmissibleSubgraph.starVertices AdmissibleSubgraph.starVertices
  rw [ofUniqueForgetForest_elements, Finset.image_image]
  apply Finset.image_congr
  intro δf _
  show FeynmanGraph.admissibleForestCanonicalStarOf _ A hA (liftUniqueFromForgetSubgraph δf).forget
    = FeynmanGraph.admissibleForestCanonicalStarOf _ A hA δf
  rw [forget_liftUniqueFromForgetSubgraph]

/-- (transport) Canonical-level starVertices alignment. -/
private theorem starVertices_canonicalOuter_transport {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hA : A ∈ G'.properDisjointAdmissibleDivergentSubgraphs) :
    (aoutOfTransport h A
        (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint _ hA)).starVertices
        (starOfTransport h A hA)
      = A.starVertices (FeynmanGraph.admissibleForestCanonicalStarOf G' A hA) := by
  subst h
  rw [aoutOfTransport_rfl]
  exact ofUniqueForgetForest_starVertices_eq A hA

/-- **S-2e-pre: starVertices alignment.**  The canonical resolved star vertices equal the flat
forest's star vertices. -/
theorem canonicalOuter_starVertices_eq (g : HopfGen) (A : h58BridgeOuterIndex g) :
    (canonicalOuterAoutOfFlatOuter g A).starVertices (canonicalOuterStarOf g A)
      = A.1.starVertices (h58BridgeOuterCanonicalStar g A) :=
  starVertices_canonicalOuter_transport
    (forget_ofFlatGraphWithUniqueIds (repG g).toFeynmanGraph) A.1 A.2

/-! ### S-2e — the contracted-graph forget bridge (summit)

`Cres.forget = h58BridgeOuterActualQuotientGraph g A`, assembled from the field alignments
(vertices / starVertices / complement-faithful forget / retargetEdge / retargetLeg / ambient
legs).  Proved by structure-eta into the three `FeynmanGraph` fields. -/

/-- The canonical outer forest's vertex carrier equals the flat forest's. -/
private theorem aoutOfTransport_vertices_eq {Gf G' : FeynmanGraph}
    (h : (ofFlatGraphWithUniqueIds Gf).forget = G')
    (A : AdmissibleSubgraph G') (hDisj : A.IsPairwiseDisjoint) :
    (aoutOfTransport h A hDisj).vertices = A.vertices := by
  subst h; rw [aoutOfTransport_rfl]; exact ofUniqueForgetForest_vertices A hDisj

theorem canonicalOuterAout_vertices_eq (g : HopfGen) (A : h58BridgeOuterIndex g) :
    (canonicalOuterAoutOfFlatOuter g A).vertices = A.1.vertices :=
  aoutOfTransport_vertices_eq _ A.1 _

/-- **S-2e: the contracted-graph forget bridge.**  Forgetting the resolved star-contraction of
the canonical outer forest recovers the flat actual quotient graph. -/
theorem forget_canonicalOuterContractedGraph (g : HopfGen) (A : h58BridgeOuterIndex g) :
    ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)).forget
      = h58BridgeOuterActualQuotientGraph g A := by
  rw [h58BridgeOuterActualQuotientGraph_eq]
  have hv : ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
        (canonicalOuterStarOf g A)).forget.vertices
      = (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).vertices := by
    rw [ResolvedFeynmanGraph.forget_vertices,
      ResolvedAdmissibleSubgraph.contractWithStars_vertices,
      AdmissibleSubgraph.contractWithStars_vertices, canonicalOuterAout_vertices_eq,
      canonicalOuter_starVertices_eq]
    rfl
  have he : ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
        (canonicalOuterStarOf g A)).forget.internalEdges
      = (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).internalEdges := by
    rw [ResolvedFeynmanGraph.forget_internalEdges,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
      AdmissibleSubgraph.contractWithStars_internalEdges, Multiset.map_map,
      ← map_forget_complementEdges_canonicalOuterAout g A, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro e' _
    exact canonicalOuter_retargetEdge_forget g A e'
  have hl : ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
        (canonicalOuterStarOf g A)).forget.externalLegs
      = (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).externalLegs := by
    rw [ResolvedFeynmanGraph.forget_externalLegs,
      ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
      AdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map,
      ← canonicalPayload_externalLegs_forget g, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro l _
    exact canonicalOuter_retargetLeg_forget g A l
  calc ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)).forget
      = FeynmanGraph.mk
          ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
            (canonicalOuterStarOf g A)).forget.vertices
          ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
            (canonicalOuterStarOf g A)).forget.internalEdges
          ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
            (canonicalOuterStarOf g A)).forget.externalLegs := rfl
    _ = FeynmanGraph.mk (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).vertices
          (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).internalEdges
          (A.1.contractWithStars (h58BridgeOuterCanonicalStar g A)).externalLegs := by
        rw [hv, he, hl]
    _ = A.1.contractWithStars (h58BridgeOuterCanonicalStar g A) := rfl

/-! ### S-3a — generic forget-subgraph lift

A subgraph of any resolved graph's forget lifts back to a resolved subgraph (submultiset
preimage by `exists_le_map`; no id-uniqueness needed for the lift or its forget round-trip).
Applied to the contracted graph `Cres` (which is the forget-target of the bridge), this lifts
flat quotient subgraphs into the resolved contracted graph. -/

private theorem feynmanSubgraph_ext_local {G : FeynmanGraph} {γ₁ γ₂ : FeynmanSubgraph G}
    (hv : γ₁.vertices = γ₂.vertices) (hi : γ₁.internalEdges = γ₂.internalEdges)
    (he : γ₁.externalLegs = γ₂.externalLegs) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; cases hv; cases hi; cases he; rfl

private theorem resolvedSubgraphOfForget_edges_exists {G : ResolvedFeynmanGraph}
    (γf : FeynmanSubgraph G.forget) :
    ∃ t ≤ G.internalEdges, t.map ResolvedFeynmanEdge.forget = γf.internalEdges :=
  exists_le_map ResolvedFeynmanEdge.forget (s := G.internalEdges) (M := γf.internalEdges)
    γf.internalEdges_le

private theorem resolvedSubgraphOfForget_legs_exists {G : ResolvedFeynmanGraph}
    (γf : FeynmanSubgraph G.forget) :
    ∃ t ≤ G.externalLegs, t.map ResolvedExternalLeg.forget = γf.externalLegs :=
  exists_le_map ResolvedExternalLeg.forget (s := G.externalLegs) (M := γf.externalLegs)
    γf.externalLegs_le

/-- **S-3a: generic forget-subgraph lift.**  Lift a subgraph of `G.forget` back to a resolved
subgraph of `G` (occurrence-faithful submultiset preimage of the edges/legs). -/
noncomputable def resolvedSubgraphOfForget {G : ResolvedFeynmanGraph}
    (γf : FeynmanSubgraph G.forget) : ResolvedFeynmanSubgraph G where
  vertices := γf.vertices
  internalEdges := (resolvedSubgraphOfForget_edges_exists γf).choose
  externalLegs := (resolvedSubgraphOfForget_legs_exists γf).choose
  vertices_subset := γf.vertices_subset
  internalEdges_le := (resolvedSubgraphOfForget_edges_exists γf).choose_spec.1
  externalLegs_le := (resolvedSubgraphOfForget_legs_exists γf).choose_spec.1
  edges_supported := by
    intro e he
    have hfe : e.forget ∈ γf.internalEdges := by
      have hmem := Multiset.mem_map_of_mem ResolvedFeynmanEdge.forget he
      rwa [(resolvedSubgraphOfForget_edges_exists γf).choose_spec.2] at hmem
    exact γf.edges_supported e.forget hfe
  legs_supported := by
    intro ℓ hℓ
    have hfℓ : ℓ.forget ∈ γf.externalLegs := by
      have hmem := Multiset.mem_map_of_mem ResolvedExternalLeg.forget hℓ
      rwa [(resolvedSubgraphOfForget_legs_exists γf).choose_spec.2] at hmem
    exact γf.legs_supported ℓ.forget hfℓ

/-- The generic lift round-trips under forget. -/
theorem forget_resolvedSubgraphOfForget {G : ResolvedFeynmanGraph}
    (γf : FeynmanSubgraph G.forget) : (resolvedSubgraphOfForget γf).forget = γf :=
  feynmanSubgraph_ext_local rfl
    (resolvedSubgraphOfForget_edges_exists γf).choose_spec.2
    (resolvedSubgraphOfForget_legs_exists γf).choose_spec.2

/-- **BranchCarriers (2): single-δ forest image.**  A forest-by-star quotient image `δ` (from
the carrier `Q`) packaged as a single-parent `ResolvedForestImageData`, via the de-contracted
parent (`parentOfQuotient`) whose remnant is exactly `δ` (`parent_remnant_eq`).  Inputs: `δ`'s
CD (`hCD`), the star-containment `hStars` and saturation `hCovered` (for `remnant = δ`), and
the discriminator witness `hTouches` (for `forest_sat`). -/
noncomputable def canonicalForestImageDataOfQuotient
    (g : HopfGen) (A : h58BridgeOuterIndex g)
    (Q : Finset (ResolvedFeynmanSubgraph
      ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A))))
    {δ : ResolvedFeynmanSubgraph
      ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A))}
    (hδ : δ ∈ Q)
    (hCD : δ.forget.IsConnectedDivergent)
    (hStars : (canonicalOuterAoutOfFlatOuter g A).starVertices (canonicalOuterStarOf g A)
      ⊆ δ.vertices)
    (hCovered : QuotientVertexCovered (canonicalOuterAoutOfFlatOuter g A)
      (canonicalOuterStarOf g A) δ)
    (hTouches : ¬ Disjoint δ.vertices
      ((canonicalOuterAoutOfFlatOuter g A).starVertices (canonicalOuterStarOf g A))) :
    ResolvedForestImageData
      (canonicalSigmaCoverDataOfParents
        (canonicalOuterParentsDataOfQuotientCarrier g A Q)) :=
  let D := canonicalSigmaCoverDataOfParents (canonicalOuterParentsDataOfQuotientCarrier g A Q)
  let parent : ResolvedForestIdx D :=
    ⟨parentOfQuotient (canonicalOuterAoutOfFlatOuter g A) (canonicalOuterStarOf g A) δ
        (canonicalPayload_edges_supported g) (canonicalPayload_legs_supported g),
      parentOfQuotient_mem_canonicalParents g A Q hδ⟩
  have hRem : resolvedForestImage D parent = δ :=
    parentOfQuotient_remnant_eq (canonicalOuterAoutOfFlatOuter g A) (canonicalOuterStarOf g A) δ
      (canonicalPayload_edges_supported g) (canonicalPayload_legs_supported g)
      (canonicalOuterAout_components_nonempty g A) hStars hCovered
  singletonForestImageDataOfParent D parent (by rw [hRem]; exact hCD) (by rw [hRem]; exact hTouches)

/-! ### BranchCarriers (3) — forest quotient supply ⇒ forest carrier

A finite quotient-image carrier with its per-δ CD / star-containment / saturation /
discriminator facts, bundled.  It yields both the `parentsData` (hence `D`) and the finite
forest image carrier (`Q.attach.image` of the single-δ forest images). -/

/-- A finite forest-by-star quotient-image carrier `Q` with the per-element facts the
forest-branch construction needs. -/
structure CanonicalOuterForestQuotientSupply (g : HopfGen) (A : h58BridgeOuterIndex g) where
  /-- The finite forest-by-star quotient images. -/
  Q : Finset (ResolvedFeynmanSubgraph
    ((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)))
  /-- Each image is connected divergent after forget. -/
  quotientCD : ∀ δ ∈ Q, δ.forget.IsConnectedDivergent
  /-- Each image contains all outer stars (for `remnant = δ`). -/
  hStars : ∀ δ ∈ Q, (canonicalOuterAoutOfFlatOuter g A).starVertices (canonicalOuterStarOf g A)
    ⊆ δ.vertices
  /-- Each image is vertex-covered (saturation, for `remnant = δ`). -/
  hCovered : ∀ δ ∈ Q, QuotientVertexCovered (canonicalOuterAoutOfFlatOuter g A)
    (canonicalOuterStarOf g A) δ
  /-- Each image meets the outer stars (the forest discriminator). -/
  hTouches : ∀ δ ∈ Q, ¬ Disjoint δ.vertices
    ((canonicalOuterAoutOfFlatOuter g A).starVertices (canonicalOuterStarOf g A))

/-- The parents datum from the forest quotient supply. -/
noncomputable def CanonicalOuterForestQuotientSupply.parentsData {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterForestQuotientSupply g A) :
    CanonicalOuterParentsData g A :=
  canonicalOuterParentsDataOfQuotientCarrier g A S.Q

open Classical in
/-- The finite forest image carrier: each quotient image as a single-parent forest image. -/
noncomputable def CanonicalOuterForestQuotientSupply.forestCarrier {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterForestQuotientSupply g A) :
    Finset (ResolvedForestImageData (canonicalSigmaCoverDataOfParents S.parentsData)) :=
  S.Q.attach.image (fun q =>
    canonicalForestImageDataOfQuotient g A S.Q q.2
      (S.quotientCD q.1 q.2) (S.hStars q.1 q.2) (S.hCovered q.1 q.2) (S.hTouches q.1 q.2))

/-- `ResolvedForestImageData` is determined by its chosen-parent set (the other fields are
propositions — proof-irrelevant). -/
theorem ResolvedForestImageData.ext_choiceParents {D : ResolvedSigmaCoverData G}
    {F₁ F₂ : ResolvedForestImageData D} (h : F₁.choiceParents = F₂.choiceParents) : F₁ = F₂ := by
  cases F₁; cases F₂; cases h; rfl

/-- **BranchCarriers (4): forest carrier injectivity.**  Immediate from
`ext_choiceParents` — equal chosen-parent sets force equal forest image data. -/
theorem CanonicalOuterForestQuotientSupply.forest_choiceParents_inj {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterForestQuotientSupply g A) :
    ∀ x ∈ S.forestCarrier, ∀ y ∈ S.forestCarrier,
      x.choiceParents = y.choiceParents → x = y :=
  fun _ _ _ _ hcp => ResolvedForestImageData.ext_choiceParents hcp

/-! ### BranchCarriers (5) — mixed side (generic over `D`, no de-contraction)

The mixed branch needs no de-contraction: a mixed image is an admissible subgraph of the
contracted graph whose components avoid the outer stars (`ResolvedMixedImageData.ofAdmissibleSubgraph`,
`componentCD`/`componentDisjoint` free).  Bundled generically over any `D`. -/

/-- `ResolvedMixedImageData` is determined by its component set (other fields are
propositions — proof-irrelevant). -/
theorem ResolvedMixedImageData.ext_components {D : ResolvedSigmaCoverData G}
    {M N : ResolvedMixedImageData D} (h : M.components = N.components) : M = N := by
  cases M; cases N; cases h; rfl

/-- A finite mixed-image carrier: contracted-graph admissible subgraphs whose components avoid
the outer stars. -/
structure ResolvedMixedCarrierSupply (D : ResolvedSigmaCoverData G) where
  /-- The mixed-branch admissible subgraphs (already in the contracted graph). -/
  mixedQ : Finset (ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf))
  /-- Every component of every mixed subgraph avoids the outer stars. -/
  avoidsStars : ∀ M ∈ mixedQ, ∀ δ ∈ M.elements,
    Disjoint δ.vertices (D.Aout.starVertices D.starOf)

open Classical in
/-- The finite mixed image carrier. -/
noncomputable def ResolvedMixedCarrierSupply.mixedCarrier {D : ResolvedSigmaCoverData G}
    (S : ResolvedMixedCarrierSupply D) : Finset (ResolvedMixedImageData D) :=
  S.mixedQ.attach.image (fun M =>
    ResolvedMixedImageData.ofAdmissibleSubgraph M.1 (S.avoidsStars M.1 M.2))

/-- **BranchCarriers (5): mixed carrier injectivity** — immediate from `ext_components`. -/
theorem ResolvedMixedCarrierSupply.mixed_components_inj {D : ResolvedSigmaCoverData G}
    (S : ResolvedMixedCarrierSupply D) :
    ∀ x ∈ S.mixedCarrier, ∀ y ∈ S.mixedCarrier, x.components = y.components → x = y :=
  fun _ _ _ _ h => ResolvedMixedImageData.ext_components h

/-! ### BranchCarriers (6) — assemble `ResolvedBranchCarriers`

Both branch supplies (forest via de-contraction, mixed via star-avoiding subgraphs) over the
same derived `D` assemble directly into `ResolvedBranchCarriers`. -/

/-- **BranchCarriers (6): assembly.**  The forest quotient supply plus a mixed carrier supply
over the derived `D` give the full `ResolvedBranchCarriers`. -/
noncomputable def CanonicalOuterForestQuotientSupply.toBranchCarriers {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterForestQuotientSupply g A)
    (M : ResolvedMixedCarrierSupply (canonicalSigmaCoverDataOfParents S.parentsData)) :
    ResolvedBranchCarriers (canonicalSigmaCoverDataOfParents S.parentsData) where
  forestCarrier := S.forestCarrier
  mixedCarrier := M.mixedCarrier
  forest_choiceParents_inj := S.forest_choiceParents_inj
  mixed_components_inj := M.mixed_components_inj

/-! ### BranchCarriers (7) — the inner supply package for one outer forest

`CanonicalOuterInnerSupplyData g A` is the finishing package for a single outer forest `A`:
the forest quotient supply (de-contraction parents) + the mixed carrier supply + the
resolved→flat index maps + the flat split-term agreement.  It assembles directly into a
`CanonicalResolvedActualSigmaCoverSupply g` (with `D` derived from the de-contraction). -/

/-- The per-outer-forest inner supply built from genuine de-contraction data: a forest
quotient supply, a mixed carrier supply over the derived `D`, the resolved→flat index maps,
and the flat split-term agreement. -/
structure CanonicalOuterInnerSupplyData (g : HopfGen) (A : h58BridgeOuterIndex g) where
  /-- The forest quotient supply (de-contraction parents). -/
  forestSupply : CanonicalOuterForestQuotientSupply g A
  /-- The mixed carrier supply over the derived σ-cover data. -/
  mixedSupply : ResolvedMixedCarrierSupply
    (canonicalSigmaCoverDataOfParents forestSupply.parentsData)
  /-- The resolved→flat index maps for the assembled layer. -/
  concreteIndexMaps : ResolvedH58ConcreteIndexMaps g
    ((forestSupply.toBranchCarriers mixedSupply).toLayer
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.edgeIdsUnique g)
      (canonicalResolvedHopfPayloadFamilyWithUniqueIds.legIdsUnique g))
  /-- The flat split-term agreement. -/
  splitTerm_agreement : ∀ s ∈ h58BridgeSplitChoiceIndex g,
    h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)

/-- **BranchCarriers (7): assembly to the canonical supply.**  The inner supply package
reduces to a `CanonicalResolvedActualSigmaCoverSupply g` with `D` derived from the
de-contraction parents and the branch carriers assembled from the forest/mixed supplies. -/
noncomputable def CanonicalOuterInnerSupplyData.toCanonicalSupply {g : HopfGen}
    {A : h58BridgeOuterIndex g} (S : CanonicalOuterInnerSupplyData g A) :
    CanonicalResolvedActualSigmaCoverSupply g where
  D := canonicalSigmaCoverDataOfParents S.forestSupply.parentsData
  branchCarriers := S.forestSupply.toBranchCarriers S.mixedSupply
  concreteIndexMaps := S.concreteIndexMaps
  splitTerm_agreement := S.splitTerm_agreement

/-! ### BranchCarriers (8) — the full outer skeleton from genuine de-contraction data

The last wrapper: a per-outer-forest family of inner supply packages assembles into the
`ResolvedH58OuterSkeleton`, hence the full native H5.8 double-sum reindex
(`outer_sum_reindex`).  Every inner supply is built from genuine de-contraction data
(`CanonicalOuterInnerSupplyData`); the outer carrier is the fixed `h58BridgeOuterCarrier g`. -/

/-- A per-outer-forest family of inner supply packages — the full data of an
`ResolvedH58OuterSkeleton g`, with every inner supply built from genuine de-contraction. -/
structure CanonicalResolvedH58OuterSkeletonSupply (g : HopfGen) where
  /-- The inner supply package for each outer proper forest. -/
  innerData : ∀ A : h58BridgeOuterIndex g, CanonicalOuterInnerSupplyData g A

/-- The outer skeleton from the per-outer-forest inner supply family. -/
noncomputable def CanonicalResolvedH58OuterSkeletonSupply.toOuterSkeleton {g : HopfGen}
    (S : CanonicalResolvedH58OuterSkeletonSupply g) : ResolvedH58OuterSkeleton g where
  innerSupply := fun A => (S.innerData A).toCanonicalSupply

/-- **The full native H5.8 double-sum reindex** delivered by a genuine-de-contraction outer
skeleton supply: the outer sum of the inner image-weight sums equals the outer sum of the
inner forest+mixed branch-weight sums, over the outer proper-forest carrier. -/
theorem CanonicalResolvedH58OuterSkeletonSupply.outer_sum_reindex {g : HopfGen}
    (S : CanonicalResolvedH58OuterSkeletonSupply g) :
    ∑ A ∈ h58BridgeOuterCarrier g, S.toOuterSkeleton.toOuterSumSupply.innerImageSum A =
      ∑ A ∈ h58BridgeOuterCarrier g, S.toOuterSkeleton.toOuterSumSupply.innerBranchSum A :=
  S.toOuterSkeleton.outer_sum_reindex

/-! ## Track S Scout (S-1) — flat σ-cover finite-data source inventory

To construct `canonicalResolvedH58OuterSkeletonSupply g` we must supply, per outer forest `A`,
the four `CanonicalOuterInnerSupplyData` fields.  Source inventory in `Coassoc.lean`:

**Already public** (the `concreteIndexMaps` targets + the `splitTerm_agreement` statement, via
the thin `Coassoc` aliases): `h58BridgeQuotientSigma`, `h58BridgeSplitChoiceSigma`,
`h58BridgeQuotientIndex`, `h58BridgeSplitChoiceIndex`, `h58BridgeQuotientTerm`,
`h58BridgeSplitChoiceTerm`, `h58BridgeSplitPhi`, `h58BridgeOuterIndex`, `h58BridgeOuterCarrier`.

**Private flat per-`A` carriers** (would need alias-only wrappers IF imported):
`forestQuotientForestSigmaIndex` (the Σ index; per-`A` inner part =
`forestCoproductProperForestIndex (forestOuterQuotientHopfGen g A)`),
`forestQuotientForestSigmaActualQuotientSubgraph`, `forestQuotientForestSigma_isForestByStar`,
`forestQuotientForestSigmaMixedCover*` (mixed machinery), and the flat contracted graph
`forestOuterQuotientGraph`/`forestOuterActualQuotientGraph`.

**Critical findings (Track S is NOT mechanical alias+lift):**

1. **Coordinate mismatch (S-2/S-3 need a contracted-graph forget lift).**  The flat carriers
   live over the *flat* contracted graph `forestOuterQuotientGraph g A`, but the resolved `Q`
   must be `Finset (ResolvedFeynmanSubgraph ((canonicalOuterAoutOfFlatOuter g A).contractWithStars
   (canonicalOuterStarOf g A)))` — over the *resolved* contracted graph.  So lifting the flat
   quotient/mixed carriers is a **forget round-trip on the contracted graph** (analogous to
   `ofUniqueForgetForest`, but the resolved contracted graph's `forget` must be related to the
   flat contracted graph — a new lift, feasible but genuine, not an alias).

2. **`splitTerm_agreement` must NOT be imported from flat (S-5 is the genuine boundary).**
   Per Field-Filling-6 (`ResolvedH58Bridge`), the flat split-term agreement is assembled
   (`forestComponentSplitPhiBranchReindexingOfFactorization`) from
   `forestComponentForestChoiceRemnantPositiveComponentsCertificate` +
   a `forestComponentSplitPhiBranchTermFactorization` payload — which carry flat's
   **facade-discharged injectivity/cover data**.  Exposing them would hand the resolved track
   exactly the facades it is reconstructing away, defeating the point.  So `splitTerm_agreement`
   is either *proven resolved-natively* (the real remaining mathematics) or *accepted as a
   supplied σ-cover datum* (the honest "not complete" boundary).

3. **`concreteIndexMaps.forest_comm`/`mixed_comm`** are the genuine resolved→flat bridge
   (resolved branch image ↦ flat split-`φ`).  They need the index maps defined and the squares
   proven — real content, but facade-free (it is a coordinate dictionary, not a cover/injectivity
   claim).

**Verdict.**  S-2/S-3 (carrier lifts) are feasible genuine lifts (contracted-graph forget
round-trip).  S-4 (commutation dictionary) is facade-free real content.  **S-5
(`splitTerm_agreement`) is the genuine boundary** — it is exactly where importing flat would
smuggle facade-discharged data, so it stays resolved-native-or-supplied.  This is why full
native resolved H5.8 is *not yet* claimed complete: the skeleton + de-contraction are built,
but `splitTerm_agreement` (and the genuine commutation dictionary) are the remaining
non-mechanical work. -/

/-! ## Track S Scout (S-2) — the contracted-graph forget bridge (feasibility + lemma chain)

S-2/S-3 lift flat quotient/mixed subgraphs into the resolved contracted graph
`Cres := (canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)`.
The keystone is the graph-level forget bridge:

```
Cres.forget  =  the flat actual contraction of (repG g) by A.1 with the flat canonical star
```

**Target correction.**  The flat target is `forestOuterActualQuotientGraph g A`
(`= A.1.contractWithStars (admissibleForestCanonicalStarOf (repG g).toFeynmanGraph A.1 A.2)`,
the *actual* contraction), **not** `forestOuterQuotientGraph g A` (the `repG`-representative of
the quotient class — only *isomorphic*).  A Coassoc alias-only wrapper
`h58BridgeOuterActualQuotientGraph g A := forestOuterActualQuotientGraph g A` is needed (the
flat def is private); that is a `Main` touch (rebuild required), proof-change-free.

**Feasibility (the id-uniqueness payoff).**  `forget_contractWithStars` gives `Cres.forget` as
the *honest projection*: vertices `(payload.vertices \ Aout.vertices) ∪ Aout.starVertices`,
internal edges `(Aout.complementEdges.map forget)` endpoint-rewritten by `Aout.retargetVertex`.
The doc-warning that `forget` does **not** distribute over the `complementEdges` subtraction is
for a *general* resolved graph — but here `Aout = ofUniqueForgetForest A.1` over the **id-unique**
payload, so `forget` is **injective on `payload.internalEdges`** (distinct edgeIds), and an
injective map *does* distribute over multiset subtraction:
`Aout.complementEdges.map forget = payload.internalEdges.map forget - Aout.internalEdges.map forget
= (repG g).internalEdges - A.1.internalEdges = A.1.complementEdges`.  **This is exactly the
id-uniqueness payoff** — the contracted-graph bridge holds *because* the payload is id-unique
(the same reason the boundary repairs apply).

**Lemma chain to land (next sprint):**
1. Coassoc alias `h58BridgeOuterActualQuotientGraph` (+ rebuild Main).
2. star alignment: `canonicalOuterStarOf g A (liftUniqueFromForgetSubgraph δf) =
   admissibleForestCanonicalStarOf … A.1 … δf` (from `starOfTransport` + `forget_liftUnique…`),
   hence `Aout.starVertices (canonicalOuterStarOf) = A.1.starVertices (flat star)`.
3. complement faithful-forget: `Aout.complementEdges.map forget = A.1.complementEdges` (injective
   map distributes over `-`; `Multiset.map_sub` under injectivity / count argument).
4. retargetVertex/retargetEdge forget alignment (`forget` of the resolved retarget = flat
   retarget of the forgotten endpoint, mirroring `forget_quotientRemainderSubgraph_*`).
5. assemble `forget_canonicalOuterContractedGraph : Cres.forget = forestOuterActualQuotientGraph g A`.

Then `Cres` is itself **id-unique** (its edges ⊆ `payload.internalEdges` via `retargetEdge`,
which preserves edgeId), so a `liftUniqueFromForgetSubgraph`-analogue lifts flat quotient
subgraphs into `Cres` with a faithful forget round-trip — giving S-2/S-3's
`liftFlatQuotientSubgraphToResolvedContracted` + `forget_…`.  `splitTerm_agreement` stays
untouched (S-5, resolved-native-or-supplied).  **Feasible, facade-free, genuine (not alias).** -/

/-! **Report.**  `ResolvedActualSigmaCover g` consolidates the four σ-cover-data-supply
obligations.  Dependency diagram:

```
ResolvedActualSigmaCover g
  ├─ FL : ResolvedCarrierFiniteBranchMapLayer        (carries cover, forest_inj, mixed_inj,
  │       └─ layer + carriers                  componentCD/remnantCD, disjoint, avoidsStars)
  ├─ concreteIndexMaps : ResolvedH58ConcreteIndexMaps g FL   (resolved→flat maps + comm)
  └─ splitTerm_agreement                       (flat σ-cover term agreement)

  .concreteData        = concreteIndexMaps.toConcreteData splitTerm_agreement
  .concrete_sum_reindex = the flat-term H5.8 split identity
  .classifier          = FL.sep.toClassifier
```

**Embedded vs external.**  `cover`, branch injectivity, and the image-data graph-work
(CD/disjoint/avoidsStars) are *inside* `FL` — supplied when `FL` is constructed from the
forest/mixed image data (`ResolvedForestImageData`/`ResolvedMixedImageData` →
`ResolvedBranchMapInstantiation.toLayer`).  The package adds only the resolved→flat index
maps and the flat term agreement.

**Remaining R-4-superfull obstruction (single statement):** *construct one
`ResolvedActualSigmaCover g`* — i.e. build the finite branch-map layer from an actual
resolved σ-cover (its forest/mixed image data) and supply the resolved→flat index maps +
flat term agreement.  All four are σ-cover data (non-facade); no abstract structure or new
mathematics remains. -/

/-! ## Construction scout — `canonicalResolvedActualSigmaCover g` field-source table

Target: `noncomputable def canonicalResolvedActualSigmaCover (g) : ResolvedActualSigmaCover g`.
The critical discipline is that **no field may reuse a flat boundary facade** — where flat
used one, the resolved replacement must be used.

| field (path) | source | theorem? | facade status |
|---|---|---|---|
| `PFU` | `canonicalResolvedHopfPayloadFamilyWithUniqueIds` | ✅ exists | facade-free (axiom-clean) |
| `FL.sep.forest_inj` | `resolvedForestImage_injective` ← `parentRemnant_injOn` | ✅ | **resolved repair** (replaces `ForestGraphInsertionUniquenessModel`) |
| `FL.sep.mixed_inj` | `mixed_inj_of_components_inj` | ✅ | facade-free (index design) |
| `FL` componentCD/disjoint | `ResolvedMixedImageData.ofAdmissibleSubgraph` | ✅ free | facade-free |
| `FL` avoidsStars | `avoidsStars_of_vertices_offStar` | ✅ | facade-free (star freshness) |
| `FL` remnantDisjoint | pairwise vertex (defeq) | ✅ | facade-free |
| `FL` remnantCD | reflection class | needs class | not facade (power-counting reflection) |
| `concreteIndexMaps` | resolved→flat forget maps + `h58Bridge*` + commutation | to construct | facade-free (forget maps) |
| `splitTerm_agreement` | σ-cover factorization (`RemnantPositiveComponentsCertificate`) | construction data | non-facade |
| **`FL.sep.cover`** | **⚠ flat cover is facade-gated — must rebuild resolved-native** | **genuine remaining** | **flat: PromotedExternalLegs-DEPENDENT; resolved replacement: `resolved_promotedComponent_externalLegs_le_plus`** |

**Critical scout answers.**
- **(A)** ForestIdx/MixedIdx/Image are **resolved-native** (`Image = ResolvedAdmissibleSubgraph
  (Aout.contractWithStars starOf)`; branch maps are resolved parent-remnants / mixed
  components), *not* flat indices transported through `forget`.
- **(B/C)** The only fields where flat used a facade are `forest_inj` (→
  `ForestGraphInsertionUniquenessModel`) and `cover` (→ `PromotedExternalLegsLiftableModel`):
  confirmed by `CoassocStrictForestH58Ready_ofBoundaryFacades` (Coassoc), gated on exactly
  those two.  `forest_inj` already has its resolved replacement (`parentRemnant_injOn`).
- **(D) HALT.**  The flat `cover` certificate is **facade-dependent**
  (`PromotedExternalLegsLiftableModel`) — it cannot be transported.  It must be **rebuilt
  resolved-natively** using `resolved_promotedComponent_externalLegs_le_plus` (the resolved
  promoted-leg containment, built precisely for this) plus the resolved σ-cover
  surjectivity.  **This is the genuine remaining construction sprint** — the one field that
  is not a direct source lookup.

**Verdict.**  Every field except `cover` is sourced facade-free (resolved repairs + index
design + structural lemmas + reflection class).  `cover` is the single genuine remaining
piece: a resolved-native surjectivity built on the resolved promoted-leg containment — the
exact place R-4-superfull's containment lemma was designed to plug in.  So
`canonicalResolvedActualSigmaCover g` is feasible **iff** the resolved cover surjectivity
is constructed; that is the final sprint, and it does **not** reintroduce any flat facade. -/

/-! ## Cover supply — `parentOf` consolidated into the cover preimage data

The cover sprint reduced both cases (mixed: structural; forest: the `parentOf`
component-lift).  Here we consolidate them: a **forest-case supply** (a `parentOf` datum
per forest-by-star image) yields the full `ResolvedCoverPreimageData` — hence the cover —
over the identity-indexed image families.  The only genuine remaining datum is the
forest-case supply (`resolvedParentRemnant` component-level surjectivity, σ-cover data,
facade-free); the mixed half is already structural. -/

/-- The forest-case supply: a parent-lift datum for every forest-by-star image. -/
def ResolvedForestCaseSupply (D : ResolvedSigmaCoverData G) : Type _ :=
  ∀ z : ResolvedActualQuotientImage D, resolvedIsForestByStar D z →
    ResolvedForestCasePreimageData D z

/-- From a forest-case supply: the cover preimage data over the identity-indexed image
families (constructed `forest_case` + structural `mixed_case`). -/
def ResolvedForestCaseSupply.toCoverPreimageData {D : ResolvedSigmaCoverData G}
    (S : ResolvedForestCaseSupply D) :
    ResolvedCoverPreimageData
      (forestData := (fun F => F : ResolvedForestImageData D → ResolvedForestImageData D))
      (mixedData := (fun M => M : ResolvedMixedImageData D → ResolvedMixedImageData D)) where
  forest_case := fun z hz => forest_case_of_preimageData D (S z hz) hz
  mixed_case := fun _ hz => exists_mixed_preimage_of_not_forest D hz

/-- **The cover, from the forest-case supply.**  Every image is a forest or mixed branch
image — the layer's `cover` content, reduced to the single forest-case `parentOf`
supply (facade-free). -/
theorem ResolvedForestCaseSupply.cover {D : ResolvedSigmaCoverData G}
    (S : ResolvedForestCaseSupply D) :
    ∀ z : ResolvedActualQuotientImage D,
      (∃ F : ResolvedForestImageData D, F.toImage = z) ∨
        (∃ M : ResolvedMixedImageData D, M.toImage = z) :=
  S.toCoverPreimageData.cover

/-! **Construction scout (parentOf / finite-layer design — knife-edge).**

P1.  `ResolvedForestCasePreimageData.parent_remnant_eq : ∀ δ ∈ z.elements, …` requires a
parent lift for **every** component of `z`, not only the star-touching ones; `forest_case`
asserts `z` is *entirely* a forest branch image (all components are parent remnants).

P2.  `ResolvedCarrierFiniteBranchMapLayer` requires `image_mem : ∀ z, z ∈ imageCarrier` and the
layer `cover : ∀ z : Image, …` — both over the **whole** `Image` type.  With
`Image = ResolvedActualQuotientImage D = ResolvedAdmissibleSubgraph (contracted)` (an
*infinite* type) these are unsatisfiable: there are admissible subgraphs of the contracted
graph that are neither forest nor mixed branch images, and `imageCarrier : Finset` cannot
be all of an infinite type.

**Verdict / design for the construction.**  The *finite* layer must take `Image` to be the
σ-cover's **finite** RHS quotient index (a `Fintype` / `Finset`-bundled index), **not** all
admissible subgraphs.  Over the finite quotient index: `image_mem` holds (the carrier is
`univ`); `cover` is exactly the σ-cover surjectivity (every quotient index is hit by a
forest or mixed branch — the genuine content); and `forest_case`'s all-components lift is
*correct* (a genuine forest-branch image's components are all parent remnants).  The
abstract `Image = ResolvedAdmissibleSubgraph` of Step 7D is fine for the *discriminator*
and `toImage`, but the finite-layer construction must index by the finite quotient set and
map into the admissible subgraphs.  So the next construction step is **not** `parentOf` in
isolation; it is choosing `Image := the finite resolved quotient index` and building the
finite layer on it (then `parentOf` is over that index's components and is correct).
*(No flat facade is involved in this design choice.)*

**Final report.**  The entire R-4-superfull cover obstruction is now the single datum
`ResolvedForestCaseSupply D` — for each forest-by-star image, a `parentOf` lifting its
components back to parents (`resolvedParentRemnant` component-level surjectivity).  This is
σ-cover data, **not** a flat facade.  Together with the (already-isolated)
`ResolvedH58ConcreteIndexMaps`, `splitTerm_agreement` (σ-cover factorization), and
`remnantCD` (reflection-class), constructing one actual resolved σ-cover supplies every
field of `ResolvedActualSigmaCover g`.  The remaining engineering — assembling these into a
finite branch-map layer (`ResolvedCarrierFiniteBranchMapLayer`: finite carriers over the actual
σ-cover's finite branch indices, where `forestImage`/`mixedImage` are injective) — is the
actual σ-cover finiteness construction; it introduces no facade and no new mathematics
beyond the σ-cover data itself. -/

/-! ## InnerSupply-1d Scout — `parents` carrier (the genuine σ-cover insertion set)

Target fields of `ResolvedSigmaCoverData`:
```
parents          : Finset (ResolvedFeynmanSubgraph G)
containsAoutEdges : ∀ γ ∈ parents, Aout.internalEdges ≤ γ.internalEdges
```
(`remnant_vertex_recovery` is **not** a separate obligation: `ofSaturatedParents` derives it
from `starFresh`/`componentConnected`/`componentPositiveEdges`, all of which are now landed
for the canonical `Aout`.)

**Finding 1 — framing.**  `parents` is the σ-cover **insertion** set: each `γ` is a *full*
subgraph of the payload graph that *contains the whole* `Aout` (`containsAoutEdges`), and the
forest-branch image is its **remnant** `resolvedForestImage D γ = resolvedParentRemnant
D.Aout D.starOf γ` (the quotient of `γ` by `Aout`).  Confirmed by `ResolvedForestIdx D =
{γ // γ ∈ D.parents}` and `resolvedForestImage = resolvedParentRemnant`.  The forest sum is
over `choiceParents ⊆ parents`, mapped to remnants.

**Finding 2 — the flat side never forms `γ ⊇ Aout`.**  The flat carrier
`forestComponentForestChoiceForestParentsAttach g q` is a *filter of `A.1.elements`* — the
**components of the outer forest** (so `γ ∈ A.1.elements`, giving `γ.internalEdges ≤
Aout.internalEdges`, the *opposite* inclusion), and `forestQuotientForestSigma g := Σ A,
AdmissibleSubgraph (forestOuterQuotientGraph g A)` indexes by *(outer forest, quotient
subgraph)* pairs — the quotient subgraph **is** the remnant directly.  So neither the
per-component flat carrier nor the flat Σ-index produces the resolved `γ ⊇ Aout` parents by
a `liftUniqueFromForgetSubgraph` transport.  The light forget-coordinate `subst` pattern
that closed `Aout`/`starOf`/`starFresh`/`componentPositiveEdges` **does not apply** here.

**Finding 3 — `parents` needs a *section* of the remnant map (de-contraction).**  To
realize the genuine σ-cover, for each inner proper forest / quotient component `δ` we need a
parent `γ ⊇ Aout` with `resolvedParentRemnant Aout starOf γ = δ`.  That is exactly the datum
`ResolvedForestCasePreimageData.parentOf` (with `parent_remnant_eq`) already isolated as the
**cover** obstruction (`ResolvedForestCaseSupply`).  So **building genuine `parents` is the
same de-contraction construction as the remaining cover sprint** — they are one piece, not
two.  No existing machinery inverts `resolvedParentRemnant` (`uncontract`/`parentOf` search:
none).

**Finding 4 — facade check: clean.**  The flat per-component injectivity
(`forestComponentForestChoiceParentRemnant_injOn`) consumes `ForestGraphInsertionUniquenessModel`,
but the resolved side **already replaces** it with `resolvedParentRemnant_injOn` (facade-free,
landed).  The carrier *construction* (de-contraction) is a graph operation needing **no**
facade.  Facades remain only in the (separate) cover/factorization layer as documented.

**Finding 5 — wrapper need: none for the carrier shape.**  `parents`/`containsAoutEdges`
live entirely on resolved types; the obstruction is mathematical (de-contraction section),
not visibility.  A thin Coassoc wrapper would only matter if the *flat inner-forest index*
were needed to drive the section — but the section maps *into* `parents`, so the index is
not consumed as a flat private.

**Verdict / fork.**  Three landings are *not* equal in weight:
- **(A) Genuine full σ-cover parents** — construct the de-contraction section
  (`parentOf`/`ResolvedForestCaseSupply`) and take `parents` = its image.  This is the heart
  of the remaining R-4-superfull work (intertwined with `cover`), a real multi-step sprint
  with no existing machinery — *not* a one-field landing.
- **(B) Minimal genuine base carrier** — `parents := {γ_Aout}` where `γ_Aout` has
  `internalEdges = Aout.internalEdges` (the `γ = Aout` primitive coproduct term, remnant =
  empty inner forest).  `containsAoutEdges` is `le_refl`.  Genuine (no facade, non-empty),
  but covers only the primitive term, *not* the full inner-forest enumeration.  Lands the D
  field honestly as a partial carrier; the full enumeration stays the de-contraction sprint.
- **(C) Defer** — leave `parents` as the documented remaining construction (mirroring the
  `cover` obstruction it coincides with) and record that D's four predicate fields are
  landed.

The light-field run ends here: `parents` is where the genuine de-contraction sprint begins,
and it is the *same* obstruction already isolated as `cover`. -/

end GaugeGeometry.QFT.Combinatorial
