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
