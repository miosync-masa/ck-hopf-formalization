import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarAdapterDesign

/-!
# R-6c-body-332 — the de-contraction supply + forest-side core (PROVED, value-only skeleton)

Three-hundred-and-thirty-second genuine-body step — the concrete multi-star adapter skeleton (body-331 design): the
coherent de-contraction supply and the forest-side region core, with `parent` / `innerIdx` derived and `forestRecovered`
assembled from `parentCD` (M2b) + D4 pairwise-disjointness.  The image-witness selector + `forestTag` + its specs
(dependent transport) are body-333.

## The supply (coherent root)

`ResolvedMultiStarDecontractionSupply D` carries the payload well-formedness (`hE`/`hL`), the leg-lift datum
(`legLift`, δ-leg-completeness), the parent CD (`parentCD`, M2b), and the inner-forest carrier membership
(`innerRaw_mem`, the one NEW gate for `ForestIdx` landing).  `localizedParent` / `innerRaw` / M3 stay DERIVED.

## Derived accessors + forest-side core (banked here)

* `parent M z δ := localizedParentWithTouchedLegs z δ.1 (M.legLift z δ) (M.hE G) (M.hL G)` — the de-contracted parent.
* `innerIdx M z δ := ⟨innerRaw …, M.innerRaw_mem z δ⟩ : (D.supply (parent M z δ).toResolvedFeynmanGraph).ForestIdx` — the
  inner forest lifted to a carrier `ForestIdx` (via the NEW `innerRaw_mem` gate).
* `forestRecoveredMulti F M z := ofElements ((forestDomain z).attach.image (parent M z ·)) parentCD D4-disjoint` — the
  recovered forest region; CD from `M.parentCD`, pairwise from `localizedParent_pairwiseDisjoint` (D4, consuming
  `F : ResolvedCanonicalStarFacts D`) + `z.2.1.pairwiseDisjoint` (the quotient forest's components are disjoint).
* `forestRecoveredMulti_elements` — its components are the parent image (`rfl`).

Per the HALT: only the supply + parent/innerIdx + forestRecovered are built; the image-witness selector `forestSource`,
`forestTag`, `forestTag_of_parent`, and `forestTag_agrees` are body-333; `innerRaw_mem` is a genuine field (NOT extracted
free); `parentCD`/`legLift` are FIELDS (NOT derived); no right/left cross-disjointness; `innerRaw_mem` is kept distinct
from `recovered_raw_mem`; no forward-quotient/occurrence; no facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-332 — the multi-star de-contraction supply.**  `hE`/`hL` (payload well-formedness) + `legLift`
(δ-leg-completeness) + `parentCD` (M2b) + `innerRaw_mem` (the NEW `ForestIdx` carrier gate).  `localizedParent`/`innerRaw`
are derived. -/
structure ResolvedMultiStarDecontractionSupply (D : ResolvedCoproductProperForestData) where
  /-- Payload edge-support. -/
  hE : ∀ (G : ResolvedFeynmanGraph), ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices
  /-- Payload leg-support. -/
  hL : ∀ (G : ResolvedFeynmanGraph), ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices
  /-- The touched-leg-lift datum for each star-touching quotient component (δ-leg-completeness). -/
  legLift : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    ResolvedTouchedLegLiftDatum z δ.1
  /-- The de-contracted parent is connected-divergent (M2b). -/
  parentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    (localizedParentWithTouchedLegs z δ.1 (legLift z δ) (hE G) (hL G)).forget.IsConnectedDivergent
  /-- The inner forest is a carrier member of the parent's graph (the NEW `ForestIdx` gate). -/
  innerRaw_mem : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}),
    innerRaw z δ.1 (legLift z δ) (hE G) (hL G)
      ∈ D.carrier (localizedParentWithTouchedLegs z δ.1 (legLift z δ) (hE G) (hL G)).toResolvedFeynmanGraph

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-332 — the de-contracted parent** (derived). -/
noncomputable def parent (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    ResolvedFeynmanSubgraph G :=
  localizedParentWithTouchedLegs z δ.1 (M.legLift z δ) (M.hE G) (M.hL G)

/-- **R-6c-body-332 — the inner forest as a carrier `ForestIdx`** (via the `innerRaw_mem` gate). -/
noncomputable def innerIdx (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    (D.supply (M.parent z δ).toResolvedFeynmanGraph).ForestIdx :=
  ⟨innerRaw z δ.1 (M.legLift z δ) (M.hE G) (M.hL G), M.innerRaw_mem z δ⟩

/-- **R-6c-body-332 — the recovered forest region** (the `componentToForest`-image of the star-touching quotient
components; CD from `parentCD`, pairwise from D4). -/
noncomputable def forestRecoveredMulti (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements
    ((forestDomain z).attach.image (fun δ => M.parent z δ))
    (fun γ hγ => by obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ; exact M.parentCD z δ)
    (fun γ₁ hγ₁ γ₂ hγ₂ hne => by
      obtain ⟨δ₁, -, rfl⟩ := Finset.mem_image.mp hγ₁
      obtain ⟨δ₂, -, rfl⟩ := Finset.mem_image.mp hγ₂
      have hδne : δ₁.1 ≠ δ₂.1 := fun h => hne (congrArg (M.parent z) (Subtype.ext h))
      exact localizedParent_pairwiseDisjoint F z δ₁.1 δ₂.1 (M.legLift z δ₁) (M.legLift z δ₂)
        (M.hE G) (M.hL G)
        (z.2.1.pairwiseDisjoint (Finset.mem_filter.mp δ₁.2).1 (Finset.mem_filter.mp δ₂.2).1 hδne))

/-- **R-6c-body-332 — the recovered forest region's components are the parent image** (`rfl`). -/
theorem forestRecoveredMulti_elements (F : ResolvedCanonicalStarFacts D)
    (z : ForestBlockCodType D G) :
    (M.forestRecoveredMulti F z).elements = (forestDomain z).attach.image (fun δ => M.parent z δ) :=
  rfl

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
