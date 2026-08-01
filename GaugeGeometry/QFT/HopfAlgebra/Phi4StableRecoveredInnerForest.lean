import GaugeGeometry.QFT.HopfAlgebra.Phi4StableFiniteSumOwnership
import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredParentTopology

/-!
# QFT-R1-body-642 — the source-independent STABLE recovered inner forest

Body-641 reduced the whole STABLE forest-block inverse to the sole open obligation
`Function.Bijective stableForestBlockForward`; weight preservation (640) is DONE.  This body rebuilds ONLY the
INNER PAYLOAD of the inverse map in STABLE normal form.  The first half of the OLD inverse (star classifier /
touched owner / `recoveredParent` / parent topology, bodies 608–610) is completion-method-INDEPENDENT and is
REUSED verbatim; the old inner-forest machinery is REBUILT over the stable completion
`stableLocalBoundaryCompletedGraph (recoveredParent I)` so NO ambient transport ever arises.

## Steps
* **Step 1** — ownership boundary (this docstring): REUSE bodies 608 (`touchedOuterComponents` /
  `touchedOuterForest` / `recoveredRight`), 609 (`inv_recoveredParent` + leaves), 610 (parent topology +
  `parentExactEdges` + `inv_delta_internalEdges_eq` + `recoveredParent_internalEdges_decomp` +
  `recoveredParent_isConnectedDivergent_uncond`), 629/630/631 (`stableLocalBoundaryCompletedGraph`,
  `StableLocalForestIdx`, `stableRootRelativeInner`, the native CD landing iffs).
* **Step 2** — `stableInvInnerComponent`: each touched outer component rebuilt as a subgraph OF the stable
  completion `stableLocalBoundaryCompletedGraph (recoveredParent I)` (legs = STABLE ambient legs filtered by
  `γ.vertices`).  Born in the stable ambient — NO later transport.
* **Step 3** — the load-bearing RAW recovery `stableInvInnerComponent_rootRelativeInner_eq` (`= γ`), fed into
  the body-631 iffs to emit `stableInvInnerComponent_isConnectedDivergent` (saturation by construction;
  divergence transports through the ROOT-coordinate degree equality, connectivity/1PI definitionally).
* **Step 4** — `stableInvRecoveredInnerForest`: the touched components' `.attach` bundled via `Finset.image`
  of `stableInvInnerComponent` (image injectivity PROVED, elements-exact, pairwise-disjoint, saturation,
  edge-completeness, component-CD).  NO dedup / orbit quotient.
* **Step 5** — the exact residual (`_complementEdges_eq` / `_card` / `_card_pos`), the live W‴ membership
  `stableInvRecoveredInnerForest_mem`, and the final payload `stableInvRecoveredInnerForestValue :
  StableLocalForestIdx (recoveredParent I)`.
* **Step 6** — the promotion image `stableInvRecoveredInnerForest_rootRelative_image` (Step-3 raw equalities
  bundled over the elements-exact set).

## Ownership boundary — MUST NOT consume (old, completion-dependent)
`phi4WTriplePrime_inv_innerComponent`, `phi4WTriplePrime_inv_recoveredInnerForest` (+ its `_mem`), the old
`recoveredChoice` / `recoveredSplitChoice`, the old forest-block round-trip / `forestBlockEquiv` (623).  ZERO
adapter to the old inner forest; the residual identity is re-derived NATIVELY on the stable ambient (whose
internal edges coincide with the parent's — the completion only differs on the external legs).

## HALT / red lines
The stable recovered SPLIT choice is NOT built (body-643); `StablePhi4ForestBlockForwardBijective` is NOT
proved.  NO round-trip / Equiv / `Finset.sum_bij` / alpha / coassoc.  ZERO `cast` / `HEq` / graph-data
transport `▸` (Prop-membership `▸` only).  ZERO adapter to the OLD inner forest / old split choice / 623
Equiv.  ZERO orbit quotient / `toFinset` / dedup.  Every `Finset.image` carries an injectivity proof.  ZERO
new `class` / `structure` / permanent `instance` (one file-local `local instance`; the payload is a `⟨…⟩`
value into the EXISTING `StableLocalForestIdx`).  ZERO forbidden divergence classes in any declaration TYPE.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily642 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 2 — the stable inner component (born in the stable completion of the recovered parent) -/

/-- **body-642 (Step 2) — a touched outer component transported into the STABLE completion of the recovered
parent.**  The induced subgraph on the component's vertices; its legs are the STABLE ambient's completed legs
saturating the component (NO re-encoding, NO later transport — it lives in the stable ambient from the START).
This replaces the OLD `phi4WTriplePrime_inv_innerComponent`, which lived over
`(recoveredParent I).boundaryCompletedResolvedGraph`; here the ambient is
`stableLocalBoundaryCompletedGraph (recoveredParent I)` (same internal edges, ZERO-re-encode legs). -/
noncomputable def stableInvInnerComponent (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)) where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs :=
    (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ γ.vertices)
  vertices_subset := by
    rw [stableLocalBoundaryCompletedGraph_vertices, phi4WTriplePrime_inv_recoveredParent_vertices I]
    exact phi4WTriplePrime_inv_touchedComponent_verts_subset (z := z) (δ := δ) hγ
  internalEdges_le := by
    rw [stableLocalBoundaryCompletedGraph_internalEdges]
    exact phi4WTriplePrime_inv_touchedComponent_internalEdges_le I hγ
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := γ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem stableInvInnerComponent_vertices (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (stableInvInnerComponent hSt I γ hγ).vertices = γ.vertices := rfl

@[simp] theorem stableInvInnerComponent_internalEdges (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (stableInvInnerComponent hSt I γ hγ).internalEdges = γ.internalEdges := rfl

/-! ## Step 3 — the load-bearing RAW recovery + the native CD landing (NO new gate) -/

/-- **body-642 (Step 3, LOAD-BEARING) — the stable inner component promotes RAW-back to the touched outer
component.**  `stableRootRelativeInner (recoveredParent I) (stableInvInnerComponent … γ) = γ` as a RAW
`ResolvedFeynmanSubgraph G` equality: vertices / internal edges are `γ`'s verbatim; the external legs match
because the root lift re-filters `G.externalLegs` by `γ.vertices`, which — `γ` being a `G`-subgraph — saturate
back to `γ.externalLegs`.  This is the STABLE mirror of body-609's `_promotion_recovery_component` (over the
NEW ambient), NOT a consume of it. -/
theorem stableInvInnerComponent_rootRelativeInner_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    stableRootRelativeInner (phi4WTriplePrime_inv_recoveredParent I)
        (stableInvInnerComponent hSt I γ hγ) = γ := by
  have hγA : γ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ
  have hsat : ResolvedExternalLegSaturated G γ :=
    ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.1 γ hγA
  apply ResolvedFeynmanSubgraph.ext
  · rfl
  · rfl
  · rw [stableRootRelativeInner_externalLegs, stableInvInnerComponent_vertices hSt I hγ,
      externalLegs_eq_filter_of_saturated γ hsat]

/-- **body-642 (Step 3, HEADLINE) — the stable inner component is connected-divergent in the STABLE ambient.**
Its `forget` is connected-divergent on `stableLocalBoundaryCompletedGraph (recoveredParent I)`: connectivity
and 1PI move DEFINITIONALLY (the body-631 topology iffs are `Iff.rfl`), and divergence moves through the
ROOT-coordinate degree equality (`stableRootRelativeInner_isDivergent_iff`) fed the RAW recovery of Step 3 —
whose right side `γ.forget` is connected-divergent as a touched-outer-forest component.  Saturation of the
recovered parent (609) and of the inner component (construction) plus parent edge-completeness (609) are the
ONLY premises; NO added gate. -/
theorem stableInvInnerComponent_isConnectedDivergent (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (stableInvInnerComponent hSt I γ hγ).forget.IsConnectedDivergent := by
  have hlift : stableRootRelativeInner (phi4WTriplePrime_inv_recoveredParent I)
      (stableInvInnerComponent hSt I γ hγ) = γ :=
    stableInvInnerComponent_rootRelativeInner_eq hSt I hγ
  have hγCD : γ.forget.IsConnectedDivergent :=
    (phi4WTriplePrime_touchedOuterForest z δ).isConnectedDivergent γ hγ
  have hγsat : ResolvedExternalLegSaturated G (phi4WTriplePrime_inv_recoveredParent I) :=
    phi4WTriplePrime_inv_recoveredParent_saturated I
  have hδsat : ResolvedExternalLegSaturated
      (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
      (stableInvInnerComponent hSt I γ hγ) := le_refl _
  have hEC : ResolvedInternalEdgeComplete (phi4WTriplePrime_inv_recoveredParent I) :=
    phi4WTriplePrime_inv_recoveredParent_edgeComplete I
  refine ⟨?_, ?_, ?_⟩
  · exact (stableRootRelativeInner_isSupportConnected_iff (phi4WTriplePrime_inv_recoveredParent I)
      (stableInvInnerComponent hSt I γ hγ)).mp (by rw [hlift]; exact hγCD.1)
  · exact (stableRootRelativeInner_isOnePI_iff (phi4WTriplePrime_inv_recoveredParent I)
      (stableInvInnerComponent hSt I γ hγ)).mp (by rw [hlift]; exact hγCD.2.1)
  · exact (stableRootRelativeInner_isDivergent_iff (phi4WTriplePrime_inv_recoveredParent I)
      (stableInvInnerComponent hSt I γ hγ) hγsat hδsat hEC).mp (by rw [hlift]; exact hγCD.2.2)

/-! ## Step 4 — the stable recovered inner forest (over the stable ambient) -/

/-- **body-642 (Step 4, HEADLINE) — the stable recovered inner forest.**  One `stableInvInnerComponent` per
touched outer component, bundled over the touched forest's `.attach` via `Finset.image`; the image is
injective (equal transported components share a vertex set, distinct touched components are pairwise
vertex-disjoint + vertex-nonempty — proved inside `_internalEdges_eq`).  Admissible via Step-3 component CD +
the outer components' pairwise disjointness (transported verbatim).  This is the STABLE mirror of body-609's
`phi4WTriplePrime_inv_recoveredInnerForest`, over the STABLE ambient — NOT a consume of it. -/
noncomputable def stableInvRecoveredInnerForest (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_touchedOuterForest z δ).elements.attach.image
      (fun γ => stableInvInnerComponent hSt I γ.1 γ.2))
    (by
      intro δ' hδ'
      obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ'
      exact stableInvInnerComponent_isConnectedDivergent hSt I γ.2)
    (by
      intro δ' hδ' δ'' hδ'' hne
      obtain ⟨γ₁, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨γ₂, -, rfl⟩ := Finset.mem_image.mp hδ''
      have hγsubne : γ₁ ≠ γ₂ :=
        fun h => hne (congrArg (fun g => stableInvInnerComponent hSt I g.1 g.2) h)
      have hγne : γ₁.1 ≠ γ₂.1 := fun h => hγsubne (Subtype.ext h)
      have hsubel : (phi4WTriplePrime_touchedOuterForest z δ).elements ⊆ z.1.1.elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements]; exact Finset.filter_subset _ _
      have hγ₁A : γ₁.1 ∈ z.1.1.elements := hsubel γ₁.2
      have hγ₂A : γ₂.1 ∈ z.1.1.elements := hsubel γ₂.2
      show _root_.Disjoint (stableInvInnerComponent hSt I γ₁.1 γ₁.2).vertices
        (stableInvInnerComponent hSt I γ₂.1 γ₂.2).vertices
      exact z.1.1.pairwiseDisjoint hγ₁A hγ₂A hγne)

@[simp] theorem stableInvRecoveredInnerForest_elements (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).elements
      = (phi4WTriplePrime_touchedOuterForest z δ).elements.attach.image
          (fun γ => stableInvInnerComponent hSt I γ.1 γ.2) := rfl

/-- **body-642 (Step 4) — every element of the stable recovered inner forest is a transported touched
component.** -/
theorem stableInvRecoveredInnerForest_element_origin (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {δ' : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))}
    (hδ' : δ' ∈ (stableInvRecoveredInnerForest hSt I).elements) :
    ∃ (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements),
      δ' = stableInvInnerComponent hSt I γ hγ := by
  rw [stableInvRecoveredInnerForest_elements] at hδ'
  obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ'
  exact ⟨γ.1, γ.2, rfl⟩

/-- **body-642 (Step 4) — the stable recovered inner forest is externally-leg saturated** (each transported
component carries the STABLE completion legs saturating it, by construction). -/
theorem stableInvRecoveredInnerForest_forestSaturated (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedForestExternalLegSaturated (stableInvRecoveredInnerForest hSt I) := by
  intro δ' hδ'
  obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
  exact le_refl _

/-- **body-642 (Step 4) — the stable recovered inner forest is internal-edge complete** (each outer
component's own edge-completeness in `G`, restricted through the STABLE ambient's internal edges = the
parent's). -/
theorem stableInvRecoveredInnerForest_forestEdgeComplete (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily
      (stableInvRecoveredInnerForest hSt I) := by
  intro δ' hδ'
  obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
  have hγA : γ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ
  have hEC : ResolvedInternalEdgeComplete γ :=
    ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.2 γ hγA
  have hHle : (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)).internalEdges
      ≤ G.internalEdges := by
    rw [stableLocalBoundaryCompletedGraph_internalEdges]
    exact (phi4WTriplePrime_inv_recoveredParent I).internalEdges_le
  show (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)).internalEdges.filter
      (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) ≤ γ.internalEdges
  exact le_trans (Multiset.filter_le_filter _ hHle) hEC

/-! ## Step 5 — the exact residual + the live W‴ membership + the payload -/

/-- **body-642 (Step 5) — the stable recovered inner forest's aggregate internal edges are the touched outer
forest's.**  Each transported component carries its outer component's internal edges; the
`stableInvInnerComponent` map is injective on the touched-forest `.attach` (equal transported components share
a vertex set; distinct touched components are pairwise vertex-disjoint + vertex-nonempty — NO forget
injectivity), so `Finset.sum_image` de-dups to the touched forest's aggregate.  STABLE mirror of body-612's
Step 1. -/
theorem stableInvRecoveredInnerForest_internalEdges_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).internalEdges
      = (phi4WTriplePrime_touchedOuterForest z δ).internalEdges := by
  classical
  have hNE : z.1.1.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1).2.1
  have hinj : Set.InjOn
      (fun γ : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements} =>
        stableInvInnerComponent hSt I γ.1 γ.2)
      ↑(phi4WTriplePrime_touchedOuterForest z δ).elements.attach := by
    intro γ₁ _ γ₂ _ heq
    apply Subtype.ext
    by_contra hne
    have hv : γ₁.1.vertices = γ₂.1.vertices := by
      have hcv := congrArg ResolvedFeynmanSubgraph.vertices heq
      simpa only [stableInvInnerComponent_vertices] using hcv
    have hγ₁A : γ₁.1 ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A γ₁.2
    have hγ₂A : γ₂.1 ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A γ₂.2
    have hdisj : _root_.Disjoint γ₁.1.vertices γ₂.1.vertices :=
      z.1.1.pairwiseDisjoint hγ₁A hγ₂A hne
    have hpos : 0 < γ₁.1.vertices.card := hNE γ₁.1 hγ₁A
    obtain ⟨v, hv1⟩ := Finset.card_pos.mp hpos
    have hv2 : v ∈ γ₂.1.vertices := hv ▸ hv1
    exact Finset.disjoint_left.mp hdisj hv1 hv2
  rw [ResolvedAdmissibleSubgraph.internalEdges,
    stableInvRecoveredInnerForest_elements, Finset.sum_image hinj]
  simp only [stableInvInnerComponent_internalEdges]
  rw [Finset.sum_attach, ResolvedAdmissibleSubgraph.internalEdges]

/-- **body-642 (Step 5, LOAD-BEARING) — the stable recovered inner forest's complement in the STABLE ambient
is RAW-equal to `parentExactEdges`.**  The STABLE ambient's internal edges are the recovered parent's
(`stableLocalBoundaryCompletedGraph_internalEdges` — the completion only re-encodes the EXTERNAL legs), which
decompose as touched-forest + Exact (body-610); the inner aggregate is exactly the touched-forest half
(Step 5), so the complement cancels to the Exact half.  Identical residual computation to body-612's Step 2 —
because both completions share the parent's internal edges — with ZERO adapter to the old inner forest. -/
theorem stableInvRecoveredInnerForest_complementEdges_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).complementEdges
      = phi4WTriplePrime_inv_parentExactEdges z δ := by
  rw [ResolvedAdmissibleSubgraph.complementEdges,
    stableLocalBoundaryCompletedGraph_internalEdges,
    phi4WTriplePrime_inv_recoveredParent_internalEdges_decomp I,
    stableInvRecoveredInnerForest_internalEdges_eq hSt I,
    add_tsub_cancel_left]

/-- **body-642 (Step 5) — the stable recovered inner forest's complement cardinality equals `δ`'s
internal-edge count.**  Step 5 identifies the complement with `parentExactEdges`; body-610's
`_delta_internalEdges_eq` presents `δ`'s internal edges as those Exact edges retargeted, so the cardinalities
agree (`Multiset.card_map`, no retarget injectivity). -/
theorem stableInvRecoveredInnerForest_complementEdges_card (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).complementEdges.card = δ.1.internalEdges.card := by
  rw [stableInvRecoveredInnerForest_complementEdges_eq hSt I,
    phi4WTriplePrime_inv_delta_internalEdges_eq I, Multiset.card_map]

/-- **body-642 (Step 5) — the stable recovered inner forest's complement is positive.**  The complement
cardinality equals `δ`'s internal-edge count, positive because `B` (`z.2.1`) is a proper forest with
componentwise positive internal edges, applied at `δ ∈ B.elements`. -/
theorem stableInvRecoveredInnerForest_complementEdges_card_pos (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    0 < (stableInvRecoveredInnerForest hSt I).complementEdges.card := by
  have hBpf : z.2.1.IsProperForest :=
    ((mem_phi4WTriplePrimeIndex
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
        z.2.2).2.2.2.2.1
  have hδpos : 0 < δ.1.internalEdges.card := hBpf.2.2.2.1 δ.1 δ.2
  rw [stableInvRecoveredInnerForest_complementEdges_card hSt I]
  exact hδpos

/-- **body-642 (Step 5) — the stable recovered inner forest is a proper forest.**  Nonemptiness / positive
edges from the touched witness + the outer components' properness; complement positivity above. -/
theorem stableInvRecoveredInnerForest_isProperForest (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).IsProperForest := by
  have hApf : z.1.1.IsProperForest := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1
  obtain ⟨γ₀, hγ₀, _, hpos₀⟩ := phi4WTriplePrime_inv_touched_witness I
  have hc0mem : stableInvInnerComponent hSt I γ₀ hγ₀
      ∈ (stableInvRecoveredInnerForest hSt I).elements := by
    rw [stableInvRecoveredInnerForest_elements]
    exact Finset.mem_image.mpr ⟨⟨γ₀, hγ₀⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨⟨_, hc0mem⟩, ?_, ?_, ?_, stableInvRecoveredInnerForest_complementEdges_card_pos hSt I⟩
  · intro δ' hδ'
    obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
    exact hApf.2.1 γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)
  · obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos₀)
    have hle : (stableInvInnerComponent hSt I γ₀ hγ₀).internalEdges
        ≤ (stableInvRecoveredInnerForest hSt I).internalEdges :=
      Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hc0mem
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, Multiset.mem_of_le hle he⟩
  · intro δ' hδ'
    obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
    exact hApf.2.2.2.1 γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)

/-- **body-642 (Step 5, VICTORY) — the stable recovered inner forest is a LIVE W‴ forest** on the STABLE
completion of the recovered parent.  The four ambient gates: support (STABLE ambient internal edges / legs
supported inside its vertices — the inherited legs via the parent's `legs_supported`, the fresh ODD boundary
legs via `resolvedInsideEndpoint_mem`); class-CD from body-610's UNCONDITIONAL parent CD through the STABLE
completion's self-CD (body-629); edge- and leg-id uniqueness from `hSt` via
`stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph`.  Plus the Step-5 forest facts (properness /
saturation / edge-completeness).  NO frontier hypothesis — everything discharged. -/
theorem stableInvRecoveredInnerForest_mem (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    stableInvRecoveredInnerForest hSt I
      ∈ phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I)) := by
  rw [mem_phi4WTriplePrimeIndex]
  refine ⟨?_, ?_, ?_, ?_,
    stableInvRecoveredInnerForest_isProperForest hSt I,
    stableInvRecoveredInnerForest_forestSaturated hSt I,
    stableInvRecoveredInnerForest_forestEdgeComplete hSt I⟩
  · -- ambient support of the STABLE completion
    refine ⟨?_, ?_⟩
    · intro e he
      rw [stableLocalBoundaryCompletedGraph_internalEdges] at he
      rw [stableLocalBoundaryCompletedGraph_vertices]
      exact (phi4WTriplePrime_inv_recoveredParent I).edges_supported e he
    · intro ℓ hℓ
      rw [stableLocalBoundaryCompletedGraph_vertices]
      rw [stableLocalBoundaryCompletedGraph_externalLegs] at hℓ
      rcases Multiset.mem_add.mp hℓ with hA | hB
      · exact (phi4WTriplePrime_inv_recoveredParent I).legs_supported ℓ hA
      · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp hB
        exact (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint_mem e
          (resolvedBoundaryEdges_mem.mp he).2
  · -- class-CD via body-629 self-CD fed body-610's UNCONDITIONAL parent CD
    exact (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
        phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily _).mpr
      (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent
        (phi4WTriplePrime_inv_recoveredParent I)
        (phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent_uncond I))
  · -- EdgeIdsUnique of the STABLE completion via `hSt`
    exact (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph
      (phi4WTriplePrime_inv_recoveredParent I) hSt).edgeIdsUnique
  · -- LegIdsUnique of the STABLE completion via `hSt`
    exact (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph
      (phi4WTriplePrime_inv_recoveredParent I) hSt).legIdsUnique

/-- **body-642 (Step 5, PAYLOAD) — the live `StableLocalForestIdx` recovered inner forest.**  A `⟨…⟩` value
into the EXISTING body-630 `StableLocalForestIdx (recoveredParent I)` — the FOREST (`Sum.inr`) payload that
body-643's stable recovered split choice will read.  NOT a new structure. -/
noncomputable def stableInvRecoveredInnerForestValue (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    StableLocalForestIdx (phi4WTriplePrime_inv_recoveredParent I) :=
  ⟨stableInvRecoveredInnerForest hSt I, stableInvRecoveredInnerForest_mem hSt I⟩

/-! ## Step 6 — promotion recovery (bundle Step-3 raw equalities over the elements-exact set) -/

/-- **body-642 (Step 6) — the whole stable recovered inner forest promotes to the touched outer forest.**
Each component promoted by `stableRootRelativeInner (recoveredParent I)` recovers its touched outer component
EXACTLY (Step 3), so the images assemble — RAW component-wise — to the touched outer forest's element set.
STABLE mirror of body-609's `_promotion_recovery`, over the STABLE root lift, NOT a consume of it. -/
theorem stableInvRecoveredInnerForest_rootRelative_image (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).elements.image
        (stableRootRelativeInner (phi4WTriplePrime_inv_recoveredParent I))
      = (phi4WTriplePrime_touchedOuterForest z δ).elements := by
  rw [stableInvRecoveredInnerForest_elements, Finset.image_image]
  rw [show (stableRootRelativeInner (phi4WTriplePrime_inv_recoveredParent I)
        ∘ fun γ : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements} =>
            stableInvInnerComponent hSt I γ.1 γ.2)
      = Subtype.val from
    funext (fun γ => stableInvInnerComponent_rootRelativeInner_eq hSt I γ.2)]
  exact Finset.attach_image_val

end GaugeGeometry.QFT.Combinatorial
