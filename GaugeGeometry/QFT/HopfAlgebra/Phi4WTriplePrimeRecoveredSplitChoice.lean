import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredRecontraction

/-!
# QFT-R1-body-614 — residual-free recovered occurrence owner + raw inverse split-choice value

All four body-609 proof frontiers are DISCHARGED (bodies 610/611/612/613).  This body BUNDLES the
unconditional local inverse decomposition into a single residual-free recovered-occurrence OWNER, then
ASSEMBLES the global THREE-region recovered outer forest and its global choice VALUE — every field
unconditional, everything a function of an arbitrary codomain `z`, never reading `s` / `componentEquiv`.

* **Step 1** — `Phi4WTriplePrime_RecoveredForestOccurrence` (occurrence owner) + builder; ALL fields
  discharged by 609–613, ZERO residual/frontier field.
* **Step 2** — the three-region classification (LEFT `A`-components untouched, RIGHT star-free `B`-components,
  FOREST star-touching `B`-components) with exclusivity; the source-independent `regionComponentOf` map.
* **Step 3** — `phi4WTriplePrime_recoveredOuter` (three-region union, CD + full pairwise disjointness proved)
  + banking (`_elements`, `_component_origin`).
* **Step 4** — `phi4WTriplePrime_recoveredChoice` (region tags) + `_mem` + the LEFT / RIGHT exact tag
  equations + the FOREST constructor tag (`Sum.inr`, via `isRight`) and owner determinacy.  The exact
  explicit-witness FOREST value equation (`recoveredChoice … = Sum.inr ⟨innerForest, mem⟩` for a FIXED
  `δ₀`) is NOT a local-owner obligation: `Exists.choose` selects the `δ` that fixes the very TYPE
  `ForestIdx parent.boundaryCompletedResolvedGraph`, so a term equality with an arbitrary `δ₀` is a
  dependent round-trip alignment, deliberately deferred as a NAMED body-615 obligation (proved there
  only after a forward-image source occurrence has fixed `δ` and its inner forest — no `HEq` / `cast` /
  motive transport is introduced here).  `choice_filtered` needs only the `Sum.inr` constructor tag.
* **Step 5** — `Phi4WTriplePrime_RecoveredSplitChoiceValue` (raw inverse split-choice value owner) + builder;
  NO `outer_mem` / `choice_filtered` / whole-Equiv (deferred to body-615).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; NO residual / frontier hypothesis on any owner or split-choice-value field; no
`δ.boundaryEdgeCount = 0`; no strict cross-presentation star equality; no `s` / `componentEquiv`; no
body-615 territory (no `outer_mem`, no `choice_filtered`, no `FilteredCoassocSplitChoice` inhabitant, no
forward/backward laws, no whole forest-block `Equiv`); AT MOST 2 new structures; no new `class` / permanent
`instance`; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst614 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the residual-free recovered-occurrence owner -/

/-- **body-614 (Step 1) — the recovered forest occurrence owner.**  For a star-touching `δ`, all the data
recovered by the inverse decontraction, with EVERY field discharged unconditionally by bodies 609–613: the
decontraction input, the parent leaf facts (CD / topology / saturation / edge-completeness), the inner
forest's UNCONDITIONAL W‴ membership, and both round-trips (promotion + recontraction).  ZERO residual /
frontier field. -/
structure Phi4WTriplePrime_RecoveredForestOccurrence
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) where
  /-- the forest-case decontraction input (body-608). -/
  input : phi4WTriplePrime_ForestDecontractionInput z δ
  /-- the recovered parent is φ⁴ connected-divergent, UNCONDITIONALLY (body-610). -/
  parentConnectedDivergent :
    (phi4WTriplePrime_inv_recoveredParent input).forget.IsConnectedDivergent
  /-- the recovered parent's forget topology (body-610). -/
  parentTopology : phi4WTriplePrime_inv_recoveredParent_ForgetTopology input
  /-- the recovered parent is external-leg saturated in `G` (body-609). -/
  parentSaturated : ResolvedExternalLegSaturated G (phi4WTriplePrime_inv_recoveredParent input)
  /-- the recovered parent is internal-edge complete in `G` (body-609). -/
  parentEdgeComplete : ResolvedInternalEdgeComplete (phi4WTriplePrime_inv_recoveredParent input)
  /-- the recovered inner forest is a LIVE W‴ forest, UNCONDITIONALLY (body-612). -/
  innerForestMem :
    phi4WTriplePrime_inv_recoveredInnerForest input (phi4WTriplePrime_inv_innerForest_CD_proof input)
      ∈ phi4WTriplePrimeIndex
          (phi4WTriplePrime_inv_recoveredParent input).boundaryCompletedResolvedGraph
  /-- the RAW promotion round-trip (body-609). -/
  promotionRecovery :
    (phi4WTriplePrime_inv_recoveredInnerForest input
        (phi4WTriplePrime_inv_innerForest_CD_proof input)).elements.image
        (rootRelativeInner (phi4WTriplePrime_inv_recoveredParent input))
      = (phi4WTriplePrime_touchedOuterForest z δ).elements
  /-- the recontraction recovery (corrected class equality, body-613). -/
  recontractionRecovery :
    phi4WTriplePrime_inv_recontraction_recovery input
      (phi4WTriplePrime_inv_innerForest_CD_proof input)

namespace Phi4WTriplePrime_RecoveredForestOccurrence

/-- the recovered parent on `G` (a convenience accessor). -/
noncomputable def parent {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) : ResolvedFeynmanSubgraph G :=
  phi4WTriplePrime_inv_recoveredParent O.input

/-- the recovered inner forest in the parent's boundary-completed ambient (a convenience accessor). -/
noncomputable def innerForest {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (phi4WTriplePrime_inv_recoveredParent O.input).boundaryCompletedResolvedGraph :=
  phi4WTriplePrime_inv_recoveredInnerForest O.input
    (phi4WTriplePrime_inv_innerForest_CD_proof O.input)

end Phi4WTriplePrime_RecoveredForestOccurrence

/-- **body-614 (Step 1, builder) — the recovered forest occurrence.**  Its essential inputs are `z`, `δ`,
and a star-touching proof `hst`; the input structure is `forestDecontractionInput_of_starTouching`, and every
field is discharged from the banked 609–613 proofs.  **Residual field count = 0.** -/
noncomputable def phi4WTriplePrime_recoveredForestOccurrence
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements})
    (hst : phi4WTriplePrime_inv_isForestImage z δ) :
    Phi4WTriplePrime_RecoveredForestOccurrence z δ :=
  let I := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst
  { input := I
    parentConnectedDivergent := phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent_uncond I
    parentTopology := phi4WTriplePrime_inv_recoveredParent_ForgetTopology_proof I
    parentSaturated := phi4WTriplePrime_inv_recoveredParent_saturated I
    parentEdgeComplete := phi4WTriplePrime_inv_recoveredParent_edgeComplete I
    innerForestMem := phi4WTriplePrime_inv_recoveredInnerForest_mem_proof I
    promotionRecovery :=
      phi4WTriplePrime_inv_promotion_recovery I (phi4WTriplePrime_inv_innerForest_CD_proof I)
    recontractionRecovery := phi4WTriplePrime_inv_recontraction_recovery_proof I }

/-! ## Step 2 — the three-region classification -/

/-- **body-614 (Step 2, LEFT) — an `A`-component is LEFT (untouched) iff its canonical star lies in no
`δ`.**  Reads only `z`. -/
def phi4WTriplePrime_inv_isLeftComponent (z : Phi4WTriplePrimeInverseCodomain G)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∀ δ : {x // x ∈ z.2.1.elements},
    phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∉ δ.1.vertices

/-- **body-614 (Step 2, RIGHT) — a `B`-component is RIGHT iff it is star-free.** -/
def phi4WTriplePrime_inv_isRightComponent (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop :=
  ¬ phi4WTriplePrime_inv_isForestImage z δ

/-- **body-614 (Step 2, FOREST) — a `B`-component is FOREST iff it is star-touching.** -/
def phi4WTriplePrime_inv_isForestComponent (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop :=
  phi4WTriplePrime_inv_isForestImage z δ

/-- **body-614 (Step 2) — RIGHT / FOREST exclusively partition `B.elements`.** -/
theorem phi4WTriplePrime_inv_rightForest_exclusive (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_inv_isForestComponent z δ ∨ phi4WTriplePrime_inv_isRightComponent z δ :=
  em _

/-- **body-614 (Step 2) — RIGHT and FOREST are mutually exclusive.** -/
theorem phi4WTriplePrime_inv_rightForest_not_both (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    ¬ (phi4WTriplePrime_inv_isForestComponent z δ ∧ phi4WTriplePrime_inv_isRightComponent z δ) :=
  fun h => h.2 h.1

/-- **body-614 (Step 2) — LEFT vs not-LEFT partitions `A.elements`; not-LEFT = touched by some `δ`.** -/
theorem phi4WTriplePrime_inv_not_isLeftComponent_iff (z : Phi4WTriplePrimeInverseCodomain G)
    (γ : ResolvedFeynmanSubgraph G) :
    ¬ phi4WTriplePrime_inv_isLeftComponent z γ ↔
      ∃ δ : {x // x ∈ z.2.1.elements},
        phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices := by
  simp only [phi4WTriplePrime_inv_isLeftComponent, not_forall, not_not]

/-- **body-614 (Step 2) — the source-independent quotient-region map.**  Each `B`-component `δ` recovers to a
`G`-subgraph: a star-touching `δ` to the recovered PARENT, a star-free `δ` to the recovered RIGHT.  Reads only
`z`. -/
noncomputable def phi4WTriplePrime_inv_regionComponentOf (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : ResolvedFeynmanSubgraph G :=
  if h : phi4WTriplePrime_inv_isForestImage z δ then
    phi4WTriplePrime_inv_recoveredParent
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z h)
  else
    phi4WTriplePrime_recoveredRight z h

theorem phi4WTriplePrime_inv_regionComponentOf_eq_parent (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hst : phi4WTriplePrime_inv_isForestImage z δ) :
    phi4WTriplePrime_inv_regionComponentOf z δ
      = phi4WTriplePrime_inv_recoveredParent
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) :=
  dif_pos hst

theorem phi4WTriplePrime_inv_regionComponentOf_eq_right (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_recoveredRight z hfree :=
  dif_neg hfree

/-- The A-forest is a proper forest (its W‴ membership). -/
theorem phi4WTriplePrime_inv_A_isProperForest (z : Phi4WTriplePrimeInverseCodomain G) :
    z.1.1.IsProperForest :=
  ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1

/-- The B-forest is a proper forest (its W‴ membership). -/
theorem phi4WTriplePrime_inv_B_isProperForest (z : Phi4WTriplePrimeInverseCodomain G) :
    z.2.1.IsProperForest :=
  ((mem_phi4WTriplePrimeIndex
    (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
      z.2.2).2.2.2.2.1

/-- A touched outer forest is empty for a star-free `δ`. -/
theorem phi4WTriplePrime_inv_touchedOuterForest_elements_empty_of_free
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_touchedOuterForest z δ).elements = ∅ := by
  rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.filter_eq_empty_iff]
  intro γ hγ hstar
  exact hfree ⟨_, hstar, ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨γ, hγ, rfl⟩⟩

/-- A star-free `δ`'s touched outer forest carries no vertices. -/
theorem phi4WTriplePrime_inv_touchedOuterForest_vertices_empty_of_free
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_touchedOuterForest z δ).vertices = ∅ := by
  simp only [ResolvedAdmissibleSubgraph.vertices,
    phi4WTriplePrime_inv_touchedOuterForest_elements_empty_of_free z hfree, Finset.biUnion_empty]

/-- **body-614 (Step 2) — the recovered quotient-region component's vertices.**  Uniformly the star-free part
of `δ` glued to the touched outer forest — the recovered parent's region for a star-touching `δ`, and just
`δ` (touched forest empty) for a star-free `δ`. -/
theorem phi4WTriplePrime_inv_regionComponentOf_vertices (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    (phi4WTriplePrime_inv_regionComponentOf z δ).vertices
      = (δ.1.vertices \ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
        ∪ (phi4WTriplePrime_touchedOuterForest z δ).vertices := by
  by_cases h : phi4WTriplePrime_inv_isForestImage z δ
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h,
      phi4WTriplePrime_inv_recoveredParent_vertices]
    rfl
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h,
      phi4WTriplePrime_recoveredRight_vertices,
      phi4WTriplePrime_inv_touchedOuterForest_vertices_empty_of_free z h, Finset.union_empty]
    have hdisj : Disjoint δ.1.vertices
        (z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) :=
      Finset.disjoint_left.mpr (fun v hv hstar => h ⟨v, hv, hstar⟩)
    exact ((Finset.sdiff_eq_self_iff_disjoint).mpr hdisj).symm

/-- **body-614 (Step 2) — every recovered quotient-region component is φ⁴ connected-divergent.** -/
theorem phi4WTriplePrime_inv_regionComponentOf_isConnectedDivergent
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    (phi4WTriplePrime_inv_regionComponentOf z δ).forget.IsConnectedDivergent := by
  by_cases h : phi4WTriplePrime_inv_isForestImage z δ
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h]
    exact phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent_uncond _
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h]
    exact phi4WTriplePrime_inv_recoveredRight_isConnectedDivergent z h

/-- **body-614 (Step 2) — every recovered quotient-region component is vertex-nonempty.** -/
theorem phi4WTriplePrime_inv_regionComponentOf_nonempty (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    (phi4WTriplePrime_inv_regionComponentOf z δ).vertices.Nonempty := by
  by_cases h : phi4WTriplePrime_inv_isForestImage z δ
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z h]
    exact Finset.card_pos.mp (phi4WTriplePrime_inv_recoveredParent_isNonempty _)
  · rw [phi4WTriplePrime_inv_regionComponentOf_eq_right z h,
      phi4WTriplePrime_recoveredRight_vertices]
    exact Finset.card_pos.mp ((phi4WTriplePrime_inv_B_isProperForest z).2.1 δ.1 δ.2)

/-- A star-free δ-vertex outside the stars is outside `A`. -/
theorem phi4WTriplePrime_inv_notStar_not_mem_A (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} {v : VertexId} (hvδ : v ∈ δ.1.vertices)
    (hvstar : v ∉ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) :
    v ∉ z.1.1.vertices := by
  have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
    δ.1.vertices_subset hvδ
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
  rcases hvQ with hd | hs
  · exact (Finset.mem_sdiff.mp hd).2
  · exact absurd hs hvstar

/-- Touched-outer-forest vertices lie in `A`. -/
theorem phi4WTriplePrime_inv_touchedOuterForest_vertices_subset_A
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}} {v : VertexId}
    (hv : v ∈ (phi4WTriplePrime_touchedOuterForest z δ).vertices) : v ∈ z.1.1.vertices := by
  obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hv
  exact ResolvedAdmissibleSubgraph.mem_vertices.mpr
    ⟨γ, phi4WTriplePrime_inv_touchedForest_subset_A hγ, hvγ⟩

/-- Two distinct `δ`s have vertex-disjoint touched outer forests. -/
theorem phi4WTriplePrime_inv_touchedOuterForest_vertices_disjoint
    (z : Phi4WTriplePrimeInverseCodomain G) {δ₁ δ₂ : {x // x ∈ z.2.1.elements}} (hne : δ₁ ≠ δ₂) :
    Disjoint (phi4WTriplePrime_touchedOuterForest z δ₁).vertices
      (phi4WTriplePrime_touchedOuterForest z δ₂).vertices := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  obtain ⟨γ₁, hγ₁, hvγ₁⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hv1
  obtain ⟨γ₂, hγ₂, hvγ₂⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hv2
  by_cases hγeq : γ₁ = γ₂
  · subst hγeq
    exact Finset.disjoint_left.mp
      (phi4WTriplePrime_touchedOuterForest_disjoint z hne) hγ₁ hγ₂
  · exact Finset.disjoint_left.mp
      (z.1.1.pairwiseDisjoint (phi4WTriplePrime_inv_touchedForest_subset_A hγ₁)
        (phi4WTriplePrime_inv_touchedForest_subset_A hγ₂) hγeq) hvγ₁ hvγ₂

/-- **body-614 (Step 2) — distinct `B`-components recover to vertex-disjoint quotient-region components.** -/
theorem phi4WTriplePrime_inv_regionComponentOf_disjoint (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₁ δ₂ : {x // x ∈ z.2.1.elements}} (hne : δ₁ ≠ δ₂) :
    Disjoint (phi4WTriplePrime_inv_regionComponentOf z δ₁).vertices
      (phi4WTriplePrime_inv_regionComponentOf z δ₂).vertices := by
  rw [phi4WTriplePrime_inv_regionComponentOf_vertices, phi4WTriplePrime_inv_regionComponentOf_vertices,
    Finset.disjoint_left]
  intro v hv1 hv2
  rw [Finset.mem_union] at hv1 hv2
  have hBdisj : Disjoint δ₁.1.vertices δ₂.1.vertices :=
    z.2.1.pairwiseDisjoint δ₁.2 δ₂.2 (fun h => hne (Subtype.ext h))
  rcases hv1 with hd1 | ht1
  · rcases hv2 with hd2 | ht2
    · exact Finset.disjoint_left.mp hBdisj (Finset.mem_sdiff.mp hd1).1 (Finset.mem_sdiff.mp hd2).1
    · exact phi4WTriplePrime_inv_notStar_not_mem_A z (Finset.mem_sdiff.mp hd1).1
        (Finset.mem_sdiff.mp hd1).2
        (phi4WTriplePrime_inv_touchedOuterForest_vertices_subset_A z ht2)
  · rcases hv2 with hd2 | ht2
    · exact phi4WTriplePrime_inv_notStar_not_mem_A z (Finset.mem_sdiff.mp hd2).1
        (Finset.mem_sdiff.mp hd2).2
        (phi4WTriplePrime_inv_touchedOuterForest_vertices_subset_A z ht1)
    · exact Finset.disjoint_left.mp
        (phi4WTriplePrime_inv_touchedOuterForest_vertices_disjoint z hne) ht1 ht2

/-- **body-614 (Step 2) — the recovered quotient-region map is injective.** -/
theorem phi4WTriplePrime_inv_regionComponentOf_injective (z : Phi4WTriplePrimeInverseCodomain G) :
    Function.Injective (phi4WTriplePrime_inv_regionComponentOf z) := by
  intro δ₁ δ₂ heq
  by_contra hne
  have hdisj := phi4WTriplePrime_inv_regionComponentOf_disjoint z hne
  rw [heq] at hdisj
  obtain ⟨v, hv⟩ := phi4WTriplePrime_inv_regionComponentOf_nonempty z δ₂
  exact Finset.disjoint_left.mp hdisj hv hv

/-- **body-614 (Step 2) — a LEFT `A`-component is vertex-disjoint from every recovered quotient-region
component.** -/
theorem phi4WTriplePrime_inv_left_regionComponent_disjoint (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (hγA : γ ∈ z.1.1.elements)
    (hL : phi4WTriplePrime_inv_isLeftComponent z γ) (δ : {x // x ∈ z.2.1.elements}) :
    Disjoint γ.vertices (phi4WTriplePrime_inv_regionComponentOf z δ).vertices := by
  rw [phi4WTriplePrime_inv_regionComponentOf_vertices, Finset.disjoint_left]
  intro v hvγ hv2
  have hvA : v ∈ z.1.1.vertices := ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγA, hvγ⟩
  rw [Finset.mem_union] at hv2
  rcases hv2 with hd | ht
  · exact phi4WTriplePrime_inv_notStar_not_mem_A z (Finset.mem_sdiff.mp hd).1
      (Finset.mem_sdiff.mp hd).2 hvA
  · obtain ⟨γ', hγ'TOF, hvγ'⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp ht
    have hne : γ' ≠ γ := by
      intro hh; subst hh
      exact hL δ (phi4WTriplePrime_inv_touched_starA_mem hγ'TOF)
    exact Finset.disjoint_left.mp
      (z.1.1.pairwiseDisjoint (phi4WTriplePrime_inv_touchedForest_subset_A hγ'TOF) hγA hne)
      hvγ' hvγ

/-! ## Step 3 — recovered outer assembly -/

/-- The LEFT sub-forest (untouched `A`-components). -/
noncomputable def phi4WTriplePrime_inv_leftForest (z : Phi4WTriplePrimeInverseCodomain G) :
    ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements (phi4WTriplePrime_inv_isLeftComponent z)

/-- The quotient region forest (RIGHT + FOREST recovered components). -/
noncomputable def phi4WTriplePrime_inv_quotientForest (z : Phi4WTriplePrimeInverseCodomain G) :
    ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements
    (z.2.1.elements.attach.image (phi4WTriplePrime_inv_regionComponentOf z))
    (by
      intro γ hγ
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hγ
      exact phi4WTriplePrime_inv_regionComponentOf_isConnectedDivergent z δ)
    (by
      intro γ hγ δ' hδ' hne
      obtain ⟨d1, -, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨d2, -, rfl⟩ := Finset.mem_image.mp hδ'
      exact phi4WTriplePrime_inv_regionComponentOf_disjoint z (fun h => hne (by rw [h])))

/-- **body-614 (Step 3, HEADLINE) — the recovered outer forest.**  The three-region union: the LEFT
`A`-components (verbatim), the RIGHT `recoveredRight` images, and the FOREST `recoveredParent` images (the
latter two packaged by `regionComponentOf`).  CD of every component and full pairwise disjointness (within +
cross of the three regions) are proved. -/
noncomputable def phi4WTriplePrime_recoveredOuter (z : Phi4WTriplePrimeInverseCodomain G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G :=
  (phi4WTriplePrime_inv_leftForest z).union (phi4WTriplePrime_inv_quotientForest z)
    (by
      intro γ hγ d hd _hne
      rw [phi4WTriplePrime_inv_leftForest, ResolvedAdmissibleSubgraph.filterElements_elements,
        Finset.mem_filter] at hγ
      obtain ⟨δ, -, rfl⟩ := Finset.mem_image.mp hd
      exact phi4WTriplePrime_inv_left_regionComponent_disjoint z hγ.1 hγ.2 δ)

/-- **body-614 (Step 3, BANK — `_elements` membership) — the exact recovered-outer component set.**  A
subgraph is a recovered-outer component iff it is a LEFT `A`-component or a recovered quotient-region
component (stated as a membership `iff`, avoiding the `DecidablePred` / `DecidableEq` instance diamonds of a
raw `Finset.filter` / `Finset.image` equality).  BANK for body-615. -/
theorem phi4WTriplePrime_mem_recoveredOuter_elements (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} :
    γ ∈ (phi4WTriplePrime_recoveredOuter z).elements ↔
      (γ ∈ z.1.1.elements ∧ phi4WTriplePrime_inv_isLeftComponent z γ)
        ∨ (∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ) := by
  unfold phi4WTriplePrime_recoveredOuter phi4WTriplePrime_inv_leftForest
    phi4WTriplePrime_inv_quotientForest
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union,
    ResolvedAdmissibleSubgraph.filterElements_elements, Finset.mem_filter,
    ResolvedAdmissibleSubgraph.ofElements_elements, Finset.mem_image, Finset.mem_attach,
    true_and]

/-- **body-614 (Step 3, BANK) — a LEFT component lands in the recovered outer forest.** -/
theorem phi4WTriplePrime_inv_left_mem_recoveredOuter (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (hγA : γ ∈ z.1.1.elements)
    (hL : phi4WTriplePrime_inv_isLeftComponent z γ) :
    γ ∈ (phi4WTriplePrime_recoveredOuter z).elements :=
  (phi4WTriplePrime_mem_recoveredOuter_elements z).mpr (Or.inl ⟨hγA, hL⟩)

/-- **body-614 (Step 3, BANK) — a recovered quotient-region component lands in the recovered outer forest.** -/
theorem phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_inv_regionComponentOf z δ ∈ (phi4WTriplePrime_recoveredOuter z).elements :=
  (phi4WTriplePrime_mem_recoveredOuter_elements z).mpr (Or.inr ⟨δ, rfl⟩)

/-- **body-614 (Step 3, BANK — `_component_origin`) — every recovered-outer component is LEFT or a recovered
quotient-region component (with its concrete witness).**  BANK for body-615. -/
theorem phi4WTriplePrime_recoveredOuter_component_origin (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_recoveredOuter z).elements) :
    (γ ∈ z.1.1.elements ∧ phi4WTriplePrime_inv_isLeftComponent z γ)
      ∨ (∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ) :=
  (phi4WTriplePrime_mem_recoveredOuter_elements z).mp hγ

/-! ## Step 4 — the global choice value -/

/-- The transported FOREST tag: the recovered inner W‴ forest, carried across the identification of the
recovered parent with the recovered-outer component. -/
noncomputable def phi4WTriplePrime_recoveredForestTag (z : Phi4WTriplePrimeInverseCodomain G)
    (γ : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
    (hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1)
    (hst : phi4WTriplePrime_inv_isForestImage z hq.choose) :
    (phi4WTriplePrimeCanonicalSupply.summandSupply γ.1.boundaryCompletedResolvedGraph).ForestIdx := by
  have heq : phi4WTriplePrime_inv_recoveredParent
      (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst) = γ.1 :=
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst).symm.trans hq.choose_spec
  exact heq ▸ (⟨phi4WTriplePrime_inv_recoveredInnerForest
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)
        (phi4WTriplePrime_inv_innerForest_CD_proof
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)),
      phi4WTriplePrime_inv_recoveredInnerForest_mem_proof
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)⟩ :
    (phi4WTriplePrimeCanonicalSupply.summandSupply
      (phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst)).boundaryCompletedResolvedGraph).ForestIdx)

/-- **body-614 (Step 4, HEADLINE) — the recovered global choice value.**  Each recovered-outer component is
assigned its region tag: LEFT → `Sum.inl true`; RIGHT → `Sum.inl false`; FOREST → `Sum.inr` of its recovered
inner W‴ forest (built from body-612's UNCONDITIONAL inner membership).  Reads only `z`. -/
noncomputable def phi4WTriplePrime_recoveredChoice (z : Phi4WTriplePrimeInverseCodomain G) :
    (γ : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements}) →
      γ ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach →
        Bool ⊕ (phi4WTriplePrimeCanonicalSupply.summandSupply
          γ.1.boundaryCompletedResolvedGraph).ForestIdx :=
  fun γ _ =>
    if hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1 then
      if hst : phi4WTriplePrime_inv_isForestImage z hq.choose then
        Sum.inr (phi4WTriplePrime_recoveredForestTag z γ hq hst)
      else
        Sum.inl false
    else
      Sum.inl true

/-- **body-614 (Step 4) — the recovered choice is a valid global component choice.** -/
theorem phi4WTriplePrime_recoveredChoice_mem (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_recoveredChoice z
      ∈ phi4EdgeCompleteGlobalChoiceCarrier (phi4WTriplePrime_recoveredOuter z) := by
  unfold phi4EdgeCompleteGlobalChoiceCarrier
  rw [Finset.mem_pi]
  intro γ hγ
  unfold phi4EdgeCompleteLocalChoiceCarrier phi4WTriplePrime_recoveredChoice
  by_cases hq : ∃ δ : {x // x ∈ z.2.1.elements}, phi4WTriplePrime_inv_regionComponentOf z δ = γ.1
  · rw [dif_pos hq]
    by_cases hst : phi4WTriplePrime_inv_isForestImage z hq.choose
    · rw [dif_pos hst]
      exact Finset.inr_mem_disjSum.mpr (Finset.mem_attach _ _)
    · rw [dif_neg hst]
      exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ false)
  · rw [dif_neg hq]
    exact Finset.inl_mem_disjSum.mpr (Finset.mem_univ true)

/-- **body-614 (Step 4, LEFT tag) — the recovered choice at a LEFT component is `Sum.inl true`.** -/
theorem phi4WTriplePrime_recoveredChoice_left (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (hγA : γ ∈ z.1.1.elements)
    (hL : phi4WTriplePrime_inv_isLeftComponent z γ)
    (h : (⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hL⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    phi4WTriplePrime_recoveredChoice z
        ⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hL⟩ h = Sum.inl true := by
  have hno : ¬ ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = γ := by
    rintro ⟨δ, hδ⟩
    have hdisj := phi4WTriplePrime_inv_left_regionComponent_disjoint z hγA hL δ
    rw [hδ] at hdisj
    obtain ⟨v, hv⟩ := Finset.card_pos.mp ((phi4WTriplePrime_inv_A_isProperForest z).2.1 γ hγA)
    exact Finset.disjoint_left.mp hdisj hv hv
  unfold phi4WTriplePrime_recoveredChoice
  rw [dif_neg hno]

/-- **body-614 (Step 4, RIGHT tag) — the recovered choice at a RIGHT component is `Sum.inl false`.** -/
theorem phi4WTriplePrime_recoveredChoice_right (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ₀)
    (h : (⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    phi4WTriplePrime_recoveredChoice z
        ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
          phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ h = Sum.inl false := by
  unfold phi4WTriplePrime_recoveredChoice
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀ :=
    ⟨δ₀, rfl⟩
  rw [dif_pos hq]
  have hchoose : hq.choose = δ₀ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z hq.choose_spec
  rw [dif_neg (show ¬ phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hfree)]

/-- **body-614 (Step 4, FOREST tag) — the recovered choice at a FOREST component is a `Sum.inr`.**  (The
FOREST occurrence's `Sum.inr` inner-W‴-forest value; here recorded via `isRight`, with owner determinacy
below fixing the occurrence.  The exact explicit-witness value equation `= Sum.inr ⟨innerForest, mem⟩`
for a fixed `δ₀` is a dependent round-trip alignment over the `Exists.choose`-selected `δ` and is a NAMED
body-615 obligation, discharged there in the forward-image context — deliberately not built here.) -/
theorem phi4WTriplePrime_recoveredChoice_forest_isRight (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ : {x // x ∈ z.2.1.elements}} (hst₀ : phi4WTriplePrime_inv_isForestImage z δ₀)
    (h : (⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ :
        {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements})
      ∈ (phi4WTriplePrime_recoveredOuter z).elements.attach) :
    (phi4WTriplePrime_recoveredChoice z
        ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
          phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ h).isRight = true := by
  unfold phi4WTriplePrime_recoveredChoice
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀ :=
    ⟨δ₀, rfl⟩
  rw [dif_pos hq]
  have hchoose : hq.choose = δ₀ :=
    phi4WTriplePrime_inv_regionComponentOf_injective z hq.choose_spec
  rw [dif_pos (show phi4WTriplePrime_inv_isForestImage z hq.choose by rw [hchoose]; exact hst₀)]
  rfl

/-- **body-614 (Step 4, owner determinacy) — the FOREST occurrence is determined by its recovered-outer
component.**  A recovered-outer component recovered from `δ` fixes `δ` (injectivity of `regionComponentOf`). -/
theorem phi4WTriplePrime_recoveredOuter_forest_owner_unique (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₀ δ : {x // x ∈ z.2.1.elements}}
    (h : phi4WTriplePrime_inv_regionComponentOf z δ = phi4WTriplePrime_inv_regionComponentOf z δ₀) :
    δ = δ₀ :=
  phi4WTriplePrime_inv_regionComponentOf_injective z h

/-! ## Step 5 — the raw inverse split-choice value owner -/

/-- **body-614 (Step 5) — the raw inverse split-choice VALUE owner.**  ONLY the recovered outer forest, the
recovered global choice, and its carrier membership — ZERO residual / frontier field.  The W‴ membership of
the outer, the forest-filtering, the `Phi4EdgeCompleteFilteredCoassocSplitChoice` inhabitant, the
forward/backward laws, and the whole forest-block `Equiv` are ALL deferred to body-615. -/
structure Phi4WTriplePrime_RecoveredSplitChoiceValue (z : Phi4WTriplePrimeInverseCodomain G) where
  /-- the recovered outer forest (three-region union). -/
  outer : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
  /-- the recovered global component choice (region tags). -/
  choice : (γ : {x // x ∈ outer.elements}) → γ ∈ outer.elements.attach →
    Bool ⊕ (phi4WTriplePrimeCanonicalSupply.summandSupply
      γ.1.boundaryCompletedResolvedGraph).ForestIdx
  /-- the choice is a valid global component choice. -/
  choice_mem : choice ∈ phi4EdgeCompleteGlobalChoiceCarrier outer

/-- **body-614 (Step 5, builder) — the recovered split-choice value.**  All three fields from Steps 3–4;
`outer := recoveredOuter z`, `choice := recoveredChoice z`, `choice_mem := recoveredChoice_mem z`. -/
noncomputable def phi4WTriplePrime_recoveredSplitChoiceValue (z : Phi4WTriplePrimeInverseCodomain G) :
    Phi4WTriplePrime_RecoveredSplitChoiceValue z where
  outer := phi4WTriplePrime_recoveredOuter z
  choice := phi4WTriplePrime_recoveredChoice z
  choice_mem := phi4WTriplePrime_recoveredChoice_mem z

end GaugeGeometry.QFT.Combinatorial
