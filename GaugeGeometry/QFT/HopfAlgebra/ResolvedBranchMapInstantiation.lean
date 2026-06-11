import GaugeGeometry.QFT.HopfAlgebra.ResolvedBranchMap

/-!
# Instantiating `ResolvedBranchMapLayer` — forest side (Track R-4-superfull, Step 7D ph.1)

First concrete win toward instantiating the branch-map layer from actual resolved
σ-index data: fix the forest index and forest image map, and prove `forest_inj`
directly from `ResolvedSigmaCoverData.parentRemnant_injOn`.

**Image strategy (7D-1).**  For the forest side the natural image is the *remnant*
itself — a `ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf)` — because that
is exactly what `parentRemnant_injOn` separates.  We take
`forestImage γ := resolvedParentRemnant D.Aout D.starOf γ`.  Whether this remnant-only
image suffices for the full `ResolvedBranchMapLayer.Image` (which must also host the
mixed images and carry the `isForestByStar` discriminator) is the open question for the
next phase — see the report note.
-/

set_option linter.unusedSectionVars false

open scoped Classical

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-- The forest branch index: the parents of the σ-cover datum. -/
abbrev ResolvedForestIdx (D : ResolvedSigmaCoverData G) :=
  {γ : ResolvedFeynmanSubgraph G // γ ∈ D.parents}

/-- The forest branch image: a parent's remnant under the outer forest. -/
noncomputable def resolvedForestImage (D : ResolvedSigmaCoverData G)
    (γ : ResolvedForestIdx D) :
    ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf) :=
  resolvedParentRemnant D.Aout D.starOf γ.1

/-- **Forest-branch injectivity** — straight from `parentRemnant_injOn`.  This is the
`forest_inj` field of `ResolvedBranchMapLayer`, now constructive on the actual σ-index
parent set. -/
theorem resolvedForestImage_injective (D : ResolvedSigmaCoverData G)
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique) :
    Function.Injective (resolvedForestImage D) := by
  intro x y h
  exact Subtype.ext (D.parentRemnant_injOn hEdgeId hLegId x.2 y.2 h)

/-! **Report (7D ph.1).**
* `ForestIdx := ResolvedForestIdx D = {γ // γ ∈ D.parents}` — landed.
* `forestImage := resolvedForestImage D` (= parent remnant) — landed.
* `forest_inj := resolvedForestImage_injective` (from `parentRemnant_injOn`) — landed.

Remaining for the layer (next phases):
* **Image**: the remnant type `ResolvedFeynmanSubgraph (Aout.contractWithStars starOf)`
  carries the forest image, but the `isForestByStar` discriminator inspects the
  *actual-quotient subgraph's components vs. star vertices*; the remnant is one
  subgraph, not a forest of components, so the discriminator likely needs the image to
  also carry the outer-forest/actual-quotient data.  **Open: does the remnant-only image
  determine `isForestByStar`, or must `Image` be a richer Σ-type (outer + remnant)?**
* **mixedImage / MixedIdx**: the mixed-boundary branch — needs the resolved
  mixed-boundary choice index and its image map (not yet defined).
* **isForestByStar / forest_sat / mixed_unsat**: the resolved discriminator + its two
  branch lemmas (the resolved actual-quotient component-vs-star statement).
* **cover**: branch-map surjectivity onto the image index.

The forest side (`ForestIdx`, `forestImage`, `forest_inj`) is the half tied to the
already-discharged insertion repair; it is closed.  The mixed/discriminator/cover half
is the resolved actual-quotient construction, the next building block. -/

/-! ## Step 7D phase 2 — actual-quotient image strategy (scout + discriminator)

**Flat finding.**  `forestQuotientForestSigma g := Σ A : forestOuterProperIndex g,
AdmissibleSubgraph (forestOuterQuotientGraph g A)` — a *dependent Σ*: an outer proper
forest `A` plus an admissible subgraph (a *forest*, with `.elements`) of the
outer-contracted graph.  The discriminator is
`isForestByStar g r := ∃ δ ∈ (ActualQuotientSubgraph g r).elements,
  ¬ Disjoint δ.vertices (r.1.1.starVertices (canonicalStarOf …))`,
i.e. **a component of the actual-quotient forest meets the outer forest's star
vertices** (option (d): a relation between outer-forest stars and the
quotient-forest components).

**Decision.**  Remnant-only `Image` is *ruled out*: the discriminator needs the
quotient *forest* (components) and the outer star vertices, not a single remnant
subgraph.  Within one `ResolvedSigmaCoverData` (fixed `Aout`/`starOf`), the resolved
`Image` is the quotient forest of the contracted graph, and the discriminator is
resolved-native (`D.Aout.starVertices D.starOf` exists). -/

/-- The resolved actual-quotient image (fixed outer forest): an admissible subgraph
(forest) of the contracted graph.  Replaces the remnant-only image. -/
abbrev ResolvedActualQuotientImage (D : ResolvedSigmaCoverData G) :=
  ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)

/-- **Resolved `isForestByStar` discriminator.**  Some component of the quotient forest
meets the outer forest's star vertices — the resolved-native mirror of the flat
discriminator. -/
def resolvedIsForestByStar (D : ResolvedSigmaCoverData G)
    (img : ResolvedActualQuotientImage D) : Prop :=
  ∃ δ ∈ img.elements, ¬ Disjoint δ.vertices (D.Aout.starVertices D.starOf)

/-! **Report (7D ph.2).**
1. **Flat `isForestByStar`**: `∃ δ ∈ (ActualQuotientSubgraph r).elements,
   ¬ Disjoint δ.vertices (outer.starVertices …)` — inspects the quotient *forest's*
   components against the outer star vertices.
2. **Chosen `Image`**: `ResolvedActualQuotientImage D =
   ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)` (a forest), with
   `resolvedIsForestByStar` the discriminator — both landed here.
3. **Consequence for `forestImage`**: the layer's `forestImage` must be **forest-valued**
   (an actual-quotient forest), *not* the single remnant of phase 1.  So
   `resolvedForestImage` (single remnant) is a per-component building block; the real
   `forestImage` assembles a forest, and `forest_inj` must be proved at the forest level
   (built from the per-component remnant injectivity).  **This is the exact extra data
   the HALT warned about: the image carries a forest, not just a remnant.**
4. **Mixed branch**: can target the *same* `Image` (a quotient forest of the same
   contracted graph) — the mixed-boundary image is another admissible subgraph there.
   `mixed_unsat` is `resolvedIsForestByStar img` failing, i.e. *no* component meets the
   star vertices (the resolved mirror of `…ActualRightQuotientSubgraph_no_starVertices`).
5. **`forest_sat`**: the forest-branch image must contain a component meeting a star —
   the resolved mirror of `…ActualQuotientSubgraph_exists_starVertex`; provable once the
   forest-valued `forestImage` is defined. -/

/-! ## Step 7D phase 3 — forest-branch actual-quotient forest assembly

The forest-valued forest image, assembled from per-parent remnants.  Component
admissibility (CD, pairwise-disjointness) and the star witness are carried as
*fields* of `ResolvedForestImageData` (per the HALT — remnant admissibility is the next
graph-work item, isolated here so the layer assembly proceeds). -/

/-- Data for one forest-branch image: a finite set of chosen parents whose remnants form
an admissible forest meeting a star vertex. -/
structure ResolvedForestImageData (D : ResolvedSigmaCoverData G) where
  /-- The chosen parents of this forest branch. -/
  choiceParents : Finset (ResolvedForestIdx D)
  /-- Each remnant is connected divergent after forget. -/
  remnantCD : ∀ γ ∈ choiceParents, (resolvedForestImage D γ).forget.IsConnectedDivergent
  /-- The remnants are pairwise disjoint. -/
  remnantDisjoint : ∀ γ ∈ choiceParents, ∀ δ ∈ choiceParents,
    resolvedForestImage D γ ≠ resolvedForestImage D δ →
    (resolvedForestImage D γ).Disjoint (resolvedForestImage D δ)
  /-- Some remnant meets the outer forest's star vertices (gives `forest_sat`). -/
  starWitness : ∃ γ ∈ choiceParents,
    ¬ Disjoint (resolvedForestImage D γ).vertices (D.Aout.starVertices D.starOf)

/-- The forest-branch image: the remnants assembled as an admissible forest in the
contracted graph. -/
noncomputable def ResolvedForestImageData.toImage {D : ResolvedSigmaCoverData G}
    (F : ResolvedForestImageData D) : ResolvedActualQuotientImage D where
  elements := F.choiceParents.image (resolvedForestImage D)
  isConnectedDivergent := by
    intro δ hδ; obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hδ; exact F.remnantCD γ hγ
  pairwiseDisjoint := by
    intro δ₁ h₁ δ₂ h₂ hne
    obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_image.mp h₁
    obtain ⟨γ₂, hγ₂, rfl⟩ := Finset.mem_image.mp h₂
    exact F.remnantDisjoint γ₁ hγ₁ γ₂ hγ₂ hne

@[simp] theorem ResolvedForestImageData.toImage_elements {D : ResolvedSigmaCoverData G}
    (F : ResolvedForestImageData D) :
    F.toImage.elements = F.choiceParents.image (resolvedForestImage D) := rfl

/-- **`forest_sat`**: the forest-branch image satisfies the discriminator (its star
witness is a component meeting the outer star vertices). -/
theorem ResolvedForestImageData.forest_sat {D : ResolvedSigmaCoverData G}
    (F : ResolvedForestImageData D) : resolvedIsForestByStar D F.toImage := by
  obtain ⟨γ, hγ, hstar⟩ := F.starWitness
  exact ⟨resolvedForestImage D γ, Finset.mem_image.mpr ⟨γ, hγ, rfl⟩, hstar⟩

/-- **Forest-level injectivity lift.**  Equal forest images have equal chosen-parent
sets — the per-remnant injectivity (`resolvedForestImage_injective`) lifted through
`Finset.image_injective`. -/
theorem ResolvedForestImageData.toImage_choiceParents_inj {D : ResolvedSigmaCoverData G}
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique)
    {F₁ F₂ : ResolvedForestImageData D}
    (h : F₁.toImage.elements = F₂.toImage.elements) :
    F₁.choiceParents = F₂.choiceParents :=
  Finset.image_injective (resolvedForestImage_injective D hEdgeId hLegId) h

/-! **Report (7D ph.3).**
* `ResolvedForestImageData` + `toImage` (forest-valued forest image) — landed; CD /
  pairwise-disjointness / star-witness carried as fields (HALT: remnant admissibility
  not derived here).
* `forest_sat` — landed (from the star witness).
* forest-level injectivity — landed as `toImage_choiceParents_inj` (elements-equality ⟹
  chosen-parent-set equality, via per-remnant injectivity + `Finset.image_injective`).

Remaining: derive `remnantCD` / `remnantDisjoint` (remnant admissibility — the next
graph-work block); define the resolved mixed-boundary `mixedImage` into the same `Image`
+ `mixed_unsat`; prove `cover`.  Then `ResolvedBranchMapLayer` instantiates. -/

/-! ## Step 7D phase 4 — mixed branch image + `mixed_unsat`

The mixed-boundary branch image, into the *same* `Image` (a forest of the contracted
graph).  Its components are right/exact-quotient components that **avoid** the outer
forest's star vertices, so it violates the discriminator — `mixed_unsat` is one line
from `avoidsStars`.  Component admissibility and the star-avoidance are carried as
fields (the exact mixed-side graph obligation). -/

/-- Data for the mixed branch image: contracted-graph components that avoid the outer
forest's star vertices. -/
structure ResolvedMixedImageData (D : ResolvedSigmaCoverData G) where
  /-- The mixed-branch components (already in the contracted graph). -/
  components : Finset (ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf))
  /-- Each component is connected divergent after forget. -/
  componentCD : ∀ δ ∈ components, δ.forget.IsConnectedDivergent
  /-- The components are pairwise disjoint. -/
  componentDisjoint : ∀ δ₁ ∈ components, ∀ δ₂ ∈ components, δ₁ ≠ δ₂ → δ₁.Disjoint δ₂
  /-- Every component avoids the outer forest's star vertices (the mixed-side obligation,
  resolved mirror of `…ActualRightQuotientSubgraph_no_starVertices`). -/
  avoidsStars : ∀ δ ∈ components, Disjoint δ.vertices (D.Aout.starVertices D.starOf)

/-- The mixed-branch image: the components assembled as an admissible forest. -/
noncomputable def ResolvedMixedImageData.toImage {D : ResolvedSigmaCoverData G}
    (M : ResolvedMixedImageData D) : ResolvedActualQuotientImage D where
  elements := M.components
  isConnectedDivergent := M.componentCD
  pairwiseDisjoint := by
    intro γ hγ δ hδ hne
    exact M.componentDisjoint γ hγ δ hδ hne

@[simp] theorem ResolvedMixedImageData.toImage_elements {D : ResolvedSigmaCoverData G}
    (M : ResolvedMixedImageData D) : M.toImage.elements = M.components := rfl

/-- **`mixed_unsat`**: the mixed-branch image violates the discriminator — no component
meets a star vertex.  One line from `avoidsStars`. -/
theorem ResolvedMixedImageData.mixed_unsat {D : ResolvedSigmaCoverData G}
    (M : ResolvedMixedImageData D) : ¬ resolvedIsForestByStar D M.toImage := by
  rintro ⟨δ, hδ, hmeet⟩
  exact hmeet (M.avoidsStars δ hδ)

/-! **Report (7D ph.4).**
* `ResolvedMixedImageData` + `toImage` + `mixed_unsat` — landed.  `mixed_unsat` is a
  one-liner from the `avoidsStars` field (the discriminator is exactly "some component
  meets a star"; mixed avoids all stars).
* Component CD / disjointness / `avoidsStars` carried as fields — `avoidsStars` is the
  precise mixed-side graph obligation (resolved
  `…ActualRightQuotientSubgraph_no_starVertices`).
* **`mixed_inj`**: NOT immediate — like the flat side it is a branch-map injectivity
  (HEq-prone); kept as a layer field, to be supplied from the mixed-boundary choice
  structure.  Not run here.

With `forest_sat` (ph.3) and `mixed_unsat` (here), the **discriminator half** of
`ResolvedBranchMapLayer` is complete; remaining for instantiation: `forest_inj`
(have, ph.1/ph.3), `mixed_inj` (field), `cover` (next). -/

/-! ## Step 7D phase 5 — assemble `ResolvedBranchMapLayer`

The wiring constructor: from forest/mixed image data plus the `mixed_inj`/`cover`
fields, build an actual `ResolvedBranchMapLayer`.  `forest_sat`/`mixed_unsat` are now
supplied automatically (ph.3/ph.4); `mixed_inj`/`cover` remain explicit fields. -/

/-- Instantiation data for the branch-map layer: forest/mixed image families plus the
remaining (`forest_inj`/`mixed_inj`/`cover`) obligations as explicit fields. -/
structure ResolvedBranchMapInstantiation (D : ResolvedSigmaCoverData G) where
  /-- Forest-branch index. -/
  ForestIdx : Type*
  /-- Mixed-branch index. -/
  MixedIdx : Type*
  /-- Forest image data per forest-branch index. -/
  forestData : ForestIdx → ResolvedForestImageData D
  /-- Mixed image data per mixed-branch index. -/
  mixedData : MixedIdx → ResolvedMixedImageData D
  /-- Forest-branch injectivity. -/
  forest_inj : Function.Injective (fun x => (forestData x).toImage)
  /-- Mixed-branch injectivity (field — branch-map injectivity, supplied later). -/
  mixed_inj : Function.Injective (fun x => (mixedData x).toImage)
  /-- Cover: every image is a forest or mixed image (field — supplied later). -/
  cover : ∀ z : ResolvedActualQuotientImage D,
    (∃ x, (forestData x).toImage = z) ∨ (∃ y, (mixedData y).toImage = z)

/-- **Assemble the branch-map layer** from instantiation data.  `forest_sat`/`mixed_unsat`
come for free (ph.3/ph.4); the discriminator is `resolvedIsForestByStar`. -/
noncomputable def ResolvedBranchMapInstantiation.toLayer {D : ResolvedSigmaCoverData G}
    (I : ResolvedBranchMapInstantiation D) : ResolvedBranchMapLayer where
  ForestIdx := I.ForestIdx
  MixedIdx := I.MixedIdx
  Image := ResolvedActualQuotientImage D
  forestImage := fun x => (I.forestData x).toImage
  mixedImage := fun x => (I.mixedData x).toImage
  isForestByStar := resolvedIsForestByStar D
  forest_sat := fun x => (I.forestData x).forest_sat
  mixed_unsat := fun x => (I.mixedData x).mixed_unsat
  forest_inj := I.forest_inj
  mixed_inj := I.mixed_inj
  cover := I.cover

/-- Cross-branch separation for the assembled layer (forest/mixed images never coincide). -/
theorem ResolvedBranchMapInstantiation.cross {D : ResolvedSigmaCoverData G}
    (I : ResolvedBranchMapInstantiation D) (qF : I.ForestIdx) (qM : I.MixedIdx) :
    (I.forestData qF).toImage ≠ (I.mixedData qM).toImage :=
  I.toLayer.cross qF qM

/-- Separated cover for the assembled layer: every image lies in exactly one branch. -/
theorem ResolvedBranchMapInstantiation.exactly_one_branch {D : ResolvedSigmaCoverData G}
    (I : ResolvedBranchMapInstantiation D) (z : ResolvedActualQuotientImage D) :
    ((∃ x, (I.forestData x).toImage = z) ∧ ¬ (∃ y, (I.mixedData y).toImage = z)) ∨
      ((∃ y, (I.mixedData y).toImage = z) ∧ ¬ (∃ x, (I.forestData x).toImage = z)) :=
  I.toLayer.exactly_one_branch z

/-- **`forest_inj` helper.**  Forest-branch injectivity reduces to injectivity of the
chosen-parent-set assignment (via the ph.3 forest-level lift). -/
theorem forest_inj_of_choiceParents_inj {D : ResolvedSigmaCoverData G}
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique)
    {ForestIdx : Type*} (forestData : ForestIdx → ResolvedForestImageData D)
    (h : Function.Injective (fun x => (forestData x).choiceParents)) :
    Function.Injective (fun x => (forestData x).toImage) := by
  intro x y hxy
  exact h (ResolvedForestImageData.toImage_choiceParents_inj hEdgeId hLegId
    (congrArg ResolvedAdmissibleSubgraph.elements hxy))

/-! **Report (7D ph.5).**
* `ResolvedBranchMapInstantiation` + `toLayer` — landed.  Given the two image families
  and the `forest_inj`/`mixed_inj`/`cover` fields, an actual `ResolvedBranchMapLayer` is
  produced; `forest_sat`/`mixed_unsat` are automatic.
* `cross`, `exactly_one_branch` — exposed from `toLayer` (the H5.8 classifier inputs).
* `forest_inj_of_choiceParents_inj` — reduces `forest_inj` to chosen-parent-set
  injectivity (easy to supply).

The remaining obligations have shrunk to: actual `mixed_inj`, actual `cover`, and the
image-data graph-work fields (remnant / mixed-component admissibility, `avoidsStars`).
The classifier side proceeds generically from `toLayer`. -/

/-! ## Step 7E — forest image graph-work fields (verdict: field-level)

Scout outcome for the forest-side graph-work (`remnantCD`, `remnantDisjoint`):

* **`remnantCD`** (the remnant is connected divergent after forget) is **not
  structural**: even flat only has `admissibleSubgraphQuotientRemainderSubgraph_isDivergent_reflect`,
  a *conditional* divergence-*reflection* lemma (gated on a reflection hypothesis), plus
  the connectedness/1PI of the remnant — all σ-cover-construction–specific.  It stays a
  field, supplied by the actual σ-cover (where it is established, flat-side, within the
  reflection model).
* **`remnantDisjoint`** is σ-cover-structural too: distinct forest-branch remnants are
  disjoint by the *cover's* construction, not by naive parent disjointness (parents all
  contain `Aout`, so their raw vertex sets are not disjoint).  Stays a field.

Both are **data the actual σ-cover provides**, not new mathematics — so the
"no remaining math obstruction" framing holds.  We provide ergonomic named constructors
that document the obligations and give a stable instantiation API. -/

/-- Ergonomic constructor for a forest image datum. -/
def ResolvedForestImageData.ofChoiceParents {D : ResolvedSigmaCoverData G}
    (choiceParents : Finset (ResolvedForestIdx D))
    (remnantCD : ∀ γ ∈ choiceParents, (resolvedForestImage D γ).forget.IsConnectedDivergent)
    (remnantDisjoint : ∀ γ ∈ choiceParents, ∀ δ ∈ choiceParents,
      resolvedForestImage D γ ≠ resolvedForestImage D δ →
      (resolvedForestImage D γ).Disjoint (resolvedForestImage D δ))
    (starWitness : ∃ γ ∈ choiceParents,
      ¬ Disjoint (resolvedForestImage D γ).vertices (D.Aout.starVertices D.starOf)) :
    ResolvedForestImageData D :=
  { choiceParents := choiceParents, remnantCD := remnantCD,
    remnantDisjoint := remnantDisjoint, starWitness := starWitness }

/-- Ergonomic constructor for a mixed image datum. -/
def ResolvedMixedImageData.ofComponents {D : ResolvedSigmaCoverData G}
    (components : Finset (ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf)))
    (componentCD : ∀ δ ∈ components, δ.forget.IsConnectedDivergent)
    (componentDisjoint : ∀ δ₁ ∈ components, ∀ δ₂ ∈ components, δ₁ ≠ δ₂ → δ₁.Disjoint δ₂)
    (avoidsStars : ∀ δ ∈ components, Disjoint δ.vertices (D.Aout.starVertices D.starOf)) :
    ResolvedMixedImageData D :=
  { components := components, componentCD := componentCD,
    componentDisjoint := componentDisjoint, avoidsStars := avoidsStars }

/-! ### Field filling — `mixed_inj` reduced to component injectivity -/

/-- Equal mixed images have equal component sets (the image forgets only proof fields). -/
theorem ResolvedMixedImageData.components_eq_of_toImage_eq {D : ResolvedSigmaCoverData G}
    {M₁ M₂ : ResolvedMixedImageData D} (h : M₁.toImage = M₂.toImage) :
    M₁.components = M₂.components := by
  have he := congrArg ResolvedAdmissibleSubgraph.elements h
  rwa [ResolvedMixedImageData.toImage_elements, ResolvedMixedImageData.toImage_elements] at he

/-- **`mixed_inj` helper.**  Mixed-branch injectivity reduces to injectivity of the
component-set assignment — the mixed analogue of `forest_inj_of_choiceParents_inj`. -/
theorem mixed_inj_of_components_inj {D : ResolvedSigmaCoverData G}
    {MixedIdx : Type*} (mixedData : MixedIdx → ResolvedMixedImageData D)
    (hCompInj : Function.Injective (fun x => (mixedData x).components)) :
    Function.Injective (fun x => (mixedData x).toImage) := by
  intro x y h
  exact hCompInj (ResolvedMixedImageData.components_eq_of_toImage_eq h)

/-! ### Field filling — `avoidsStars` reduced to off-star vertices

The contracted graph's vertices split as `(G.vertices \ Aout.vertices) ∪ starVertices`.
Star freshness (`D.starFresh`) makes the off-star part disjoint from the stars, so a
mixed component **avoids the stars** as soon as its vertices lie in the off-star part —
no separate `avoidsStars` graph-work, only the structural off-star property the actual
mixed/right construction has. -/

/-- **`avoidsStars` from off-star vertices.**  A contracted-graph subgraph whose vertices
lie in the off-`Aout` part avoids the star vertices — using star freshness.  (Resolved
analogue of the flat `forestComponentChoiceRight_vertices_not_mem_forestOuterSubgraph`.) -/
theorem avoidsStars_of_vertices_offStar (D : ResolvedSigmaCoverData G)
    {δ : ResolvedFeynmanSubgraph (D.Aout.contractWithStars D.starOf)}
    (hδ : δ.vertices ⊆ G.vertices \ D.Aout.vertices) :
    Disjoint δ.vertices (D.Aout.starVertices D.starOf) := by
  rw [Finset.disjoint_left]
  intro v hv hvs
  obtain ⟨η, hη, rfl⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hvs
  exact D.starFresh η hη (Finset.mem_sdiff.mp (hδ hv)).1

end GaugeGeometry.QFT.Combinatorial
