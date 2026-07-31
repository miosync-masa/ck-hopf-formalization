import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockLeftInverse

/-!
# QFT-R1-body-622b-2 — the DEF-LEVEL aligned recovered inner forest + FOREST exact payload

body-622a proved the forward-native FOREST **parent** identification `recoveredParent I = o.γ.1` (a RAW
`ResolvedFeynmanSubgraph G` equality) but STOPPED at the FOREST **choice** coordinate: the value equation
demands the DEPENDENT inner-forest identity across the ambients `(recoveredParent I).bcrg` vs `o.γ.1.bcrg`,
and — as body-622a recorded — no `subst` aligns them judgmentally (the generic-parent `subst` is blocked by
an occurs-check, and a generic-`P` conclusion would need a graph-data `▸` in a public type = RED LINE).

body-622b-1 delivered the ambient-FREE combinatorial core (the touched outer forest of the forward remnant
IS the promoted inner forest, component for component with multiplicity).  This body carries the sanctioned
DEF-LEVEL alignment: build the recovered inner forest over `o.γ.1.boundaryCompletedResolvedGraph` FROM THE
START (a genuine DE-PROMOTION reconstruction of the touched geometry, NOT an `o.B.1` alias), so the target
round-trip is HOMOGENEOUS, and then bridge to the ACTUAL inverse tag inside a single proof (mirroring
body-614/620's own `recoveredForestTag` transport to identity-collapse — NO new public transport).

* **Step 1 (Aligned Component)** — `phi4WTriplePrime_forwardAlignedInnerComponent`: each recovered inner
  component built directly as a `ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph` (vertices /
  internal edges = the touched component's, legs = the boundary-completed ambient legs saturating it).
* **Step 2 (Aligned Forest)** — `phi4WTriplePrime_forwardAlignedRecoveredInnerForest o :
  ResolvedAdmissibleSubgraph o.γ.1.boundaryCompletedResolvedGraph` via `ofElements` over the touched forest's
  de-promotions.  Its CD / disjointness come by the body-622b-1 round-trip (each de-promotion re-identifies
  with an `o.B.1` component).  It is NEVER set to `o.B.1`.
* **Step 3 (Raw Round-Trip)** — `phi4WTriplePrime_forwardAlignedRecoveredInnerForest o = o.B.1`, a fully
  HOMOGENEOUS raw `ResolvedAdmissibleSubgraph o.γ.1.bcrg` equality (from body-622b-1 + `rootRelativeInner_injOn`).
* **Step 4 (Existing Tag Bridge)** — `phi4WTriplePrime_forwardAligned_recoveredForestTag_eq`: the ACTUAL
  inverse's body-614 `recoveredForestTag` equals `⟨forwardAlignedRecoveredInnerForest o, _⟩` INSIDE the
  `o.γ.1.bcrg` fiber.  The `recoveredForestTag`'s OWN transport is identity-collapsed via `eqRec`-HEq
  (`rec_heq_of_heq`) + body-620's `recoveredForestTag_transport`; NO `HEq` / `cast` / `▸` in the PUBLIC type.
* **Step 5 (Exact Payload)** — `phi4WTriplePrime_forwardAligned_recoveredChoice_eq`:
  `recoveredChoice (forestBlockForward s) ⟨o.γ.1, _⟩ _ = Sum.inr o.B` — body-614's FOREST exact payload in the
  GENERAL forward-image context.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration TYPE.  NO public graph-data `▸` / `cast` / `Eq.ndrec` / `HEq` in any declaration TYPE (the generic
`transportSub` / `transportRAS` / `transportFI` utilities keep the `▸` in their BODIES; every `▸` in a proof
is tactic-internal).  `forwardAlignedRecoveredInnerForest` is a genuine de-promotion `def` — NOT an `o.B.1`
alias.  NO `forestBlockForwardCorrected` / global `τ` / orbit quotient / dedup; NO polluted machinery.  HALT
(not entered): `recoveredOuter = s.outer`, the choice `funext`, the whole `Equiv`, the headline left inverse
(all body-622b-3).  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst622b2 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Generic dependent-transport utilities (the `▸` confined to their BODIES; clean TYPES) -/

/-- Transport a `ResolvedFeynmanSubgraph` along a graph equality (`▸` confined to the body). -/
private def phi4WTriplePrime_transportSub {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) : ResolvedFeynmanSubgraph H₂ := h ▸ δ

@[simp] private theorem phi4WTriplePrime_transportSub_vertices {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (phi4WTriplePrime_transportSub h δ).vertices = δ.vertices := by
  cases h; rfl

@[simp] private theorem phi4WTriplePrime_transportSub_internalEdges {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (phi4WTriplePrime_transportSub h δ).internalEdges = δ.internalEdges := by
  cases h; rfl

@[simp] private theorem phi4WTriplePrime_transportSub_externalLegs {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (phi4WTriplePrime_transportSub h δ).externalLegs = δ.externalLegs := by
  cases h; rfl

/-- Transport a `ResolvedAdmissibleSubgraph` along a graph equality (`▸` confined to the body). -/
private def phi4WTriplePrime_transportRAS {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (X : ResolvedAdmissibleSubgraph H₁) : ResolvedAdmissibleSubgraph H₂ := h ▸ X

private theorem phi4WTriplePrime_transportRAS_elements {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (X : ResolvedAdmissibleSubgraph H₁) :
    (phi4WTriplePrime_transportRAS h X).elements
      = X.elements.image (phi4WTriplePrime_transportSub h) := by
  cases h; exact (Finset.image_id).symm

/-- Transport a `ForestIdx` along a graph equality (`▸` confined to the body). -/
private noncomputable def phi4WTriplePrime_transportFI {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (B : (phi4WTriplePrimeCanonicalSupply.summandSupply H₁).ForestIdx) :
    (phi4WTriplePrimeCanonicalSupply.summandSupply H₂).ForestIdx := h ▸ B

private theorem phi4WTriplePrime_transportFI_val {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (B : (phi4WTriplePrimeCanonicalSupply.summandSupply H₁).ForestIdx) :
    (phi4WTriplePrime_transportFI h B).1 = phi4WTriplePrime_transportRAS h B.1 := by
  cases h; rfl

variable {s : Phi4EdgeCompleteFilteredCoassocSplitChoice G}

/-! ## Step 1 — the aligned inner component (de-promotion into the `o.γ.1.bcrg` fiber) -/

/-- A touched component's vertices lie in the boundary-completed inner ambient (via body-622b-1). -/
theorem phi4WTriplePrime_forwardAligned_verts_subset (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements) :
    γ.vertices ⊆ o.γ.1.boundaryCompletedResolvedGraph.vertices := by
  rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hγ
  obtain ⟨δᵢ, hδᵢ, rfl⟩ := Finset.mem_image.mp hγ
  rw [rootRelativeInner_vertices]
  exact δᵢ.vertices_subset

/-- A touched component's internal edges embed into the boundary-completed inner ambient (via body-622b-1). -/
theorem phi4WTriplePrime_forwardAligned_internalEdges_le (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements) :
    γ.internalEdges ≤ o.γ.1.boundaryCompletedResolvedGraph.internalEdges := by
  rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hγ
  obtain ⟨δᵢ, hδᵢ, rfl⟩ := Finset.mem_image.mp hγ
  rw [rootRelativeInner_internalEdges]
  exact δᵢ.internalEdges_le

/-- **body-622b-2 (Step 1) — the aligned inner component.**  For a touched outer component `γ` of the forward
remnant, the de-promoted subgraph over `o.γ.1.boundaryCompletedResolvedGraph`: `γ`'s vertices / internal edges
verbatim, and the boundary-completed ambient legs saturating it.  Built DIRECTLY in the `o.γ.1.bcrg` fiber
(no transport). -/
noncomputable def phi4WTriplePrime_forwardAlignedInnerComponent
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) (γ : ResolvedFeynmanSubgraph G)
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements) :
    ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := o.γ.1.boundaryCompletedResolvedGraph.externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈ γ.vertices)
  vertices_subset := phi4WTriplePrime_forwardAligned_verts_subset o hγ
  internalEdges_le := phi4WTriplePrime_forwardAligned_internalEdges_le o hγ
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := γ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

/-- **body-622b-2 (Step 1, round-trip) — the aligned de-promotion of a promoted inner component is that
component.**  For `δᵢ ∈ o.B.1.elements`, de-promoting `rootRelativeInner o.γ.1 δᵢ` recovers `δᵢ` exactly (its
saturated legs are reconstructed as the ambient filter). -/
theorem phi4WTriplePrime_forwardAligned_component_roundtrip
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    {δᵢ : ResolvedFeynmanSubgraph o.γ.1.boundaryCompletedResolvedGraph}
    (hδᵢ : δᵢ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            o.γ.1.boundaryCompletedResolvedGraph o.B.1)
    (hγ : rootRelativeInner o.γ.1 δᵢ ∈ (phi4WTriplePrime_touchedOuterForest
        (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements) :
    phi4WTriplePrime_forwardAlignedInnerComponent o (rootRelativeInner o.γ.1 δᵢ) hγ = δᵢ := by
  apply ResolvedFeynmanSubgraph.ext
  · exact rootRelativeInner_vertices o.γ.1 δᵢ
  · exact rootRelativeInner_internalEdges o.γ.1 δᵢ
  · show o.γ.1.boundaryCompletedResolvedGraph.externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈ (rootRelativeInner o.γ.1 δᵢ).vertices) = δᵢ.externalLegs
    rw [rootRelativeInner_vertices]
    exact (externalLegs_eq_filter_of_saturated δᵢ (phi4WTriplePrime_occ_B_saturated o hδᵢ)).symm

/-! ## Step 2 — the aligned recovered inner forest -/

/-- **body-622b-2 (Step 2, HEADLINE) — the aligned recovered inner forest.**  A genuine RECONSTRUCTION over
`o.γ.1.boundaryCompletedResolvedGraph`: one aligned de-promotion per touched outer component of the forward
remnant (reading body-622b-1's correspondence IN REVERSE).  CD + pairwise disjointness come from the
body-622b-1 round-trip that re-identifies each de-promotion with an `o.B.1` component.  It is NOT `o.B.1`. -/
noncomputable def phi4WTriplePrime_forwardAlignedRecoveredInnerForest
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily o.γ.1.boundaryCompletedResolvedGraph :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements.attach.image
      (fun γ => phi4WTriplePrime_forwardAlignedInnerComponent o γ.1 γ.2))
    (by
      intro δ' hδ'
      obtain ⟨γt, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨d, hd⟩ := γt
      have hdt := hd
      rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hdt
      obtain ⟨δᵢ, hδᵢ, hdeq⟩ := Finset.mem_image.mp hdt
      subst hdeq
      rw [phi4WTriplePrime_forwardAligned_component_roundtrip o hδᵢ hd]
      exact o.B.1.isConnectedDivergent δᵢ hδᵢ)
    (by
      intro δ' hδ' δ'' hδ'' hne
      obtain ⟨γa, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨γb, -, rfl⟩ := Finset.mem_image.mp hδ''
      obtain ⟨da, hda⟩ := γa
      obtain ⟨db, hdb⟩ := γb
      have hdat := hda
      rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hdat
      obtain ⟨δa, hδa, hdaeq⟩ := Finset.mem_image.mp hdat
      have hdbt := hdb
      rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hdbt
      obtain ⟨δb, hδb, hdbeq⟩ := Finset.mem_image.mp hdbt
      subst hdaeq
      subst hdbeq
      have hne' : δa ≠ δb := by
        intro h
        apply hne
        rw [phi4WTriplePrime_forwardAligned_component_roundtrip o hδa hda,
            phi4WTriplePrime_forwardAligned_component_roundtrip o hδb hdb, h]
      rw [phi4WTriplePrime_forwardAligned_component_roundtrip o hδa hda,
          phi4WTriplePrime_forwardAligned_component_roundtrip o hδb hdb]
      exact o.B.1.pairwiseDisjoint hδa hδb hne')

@[simp] theorem phi4WTriplePrime_forwardAlignedRecoveredInnerForest_elements
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    (phi4WTriplePrime_forwardAlignedRecoveredInnerForest o).elements
      = (phi4WTriplePrime_touchedOuterForest (phi4WTriplePrime_forestBlockForward s)
          ⟨phi4WTriplePrime_remnantComponent o,
            phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements.attach.image
        (fun γ => phi4WTriplePrime_forwardAlignedInnerComponent o γ.1 γ.2) := rfl

/-! ## Step 3 — the homogeneous raw round-trip `forwardAlignedRecoveredInnerForest o = o.B.1` -/

/-- **body-622b-2 (Step 3, HEADLINE) — the aligned recovered inner forest IS `o.B.1`.**  A fully HOMOGENEOUS
raw `ResolvedAdmissibleSubgraph o.γ.1.boundaryCompletedResolvedGraph` equality (both sides in the same fiber):
by body-622b-1 the touched forest is `o.B.1`'s promotion image, and each de-promotion round-trips
(`rootRelativeInner_injOn` mediating), so the component sets coincide. -/
theorem phi4WTriplePrime_forwardAlignedRecoveredInnerForest_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_forwardAlignedRecoveredInnerForest o = o.B.1 := by
  apply phi4WTriplePrime_admissible_ext_elements
  rw [phi4WTriplePrime_forwardAlignedRecoveredInnerForest_elements]
  apply Finset.ext
  intro η
  constructor
  · intro hη
    obtain ⟨γt, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨d, hd⟩ := γt
    have hdt := hd
    rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o] at hdt
    obtain ⟨δᵢ, hδᵢ, hdeq⟩ := Finset.mem_image.mp hdt
    subst hdeq
    rw [phi4WTriplePrime_forwardAligned_component_roundtrip o hδᵢ hd]
    exact hδᵢ
  · intro hη
    apply Finset.mem_image.mpr
    have hγt : rootRelativeInner o.γ.1 η ∈ (phi4WTriplePrime_touchedOuterForest
        (phi4WTriplePrime_forestBlockForward s)
        ⟨phi4WTriplePrime_remnantComponent o,
          phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩).elements := by
      rw [phi4WTriplePrime_forwardForest_touchedOuterForest_eq o]
      exact Finset.mem_image.mpr ⟨η, hη, rfl⟩
    exact ⟨⟨rootRelativeInner o.γ.1 η, hγt⟩, Finset.mem_attach _ _,
      phi4WTriplePrime_forwardAligned_component_roundtrip o hη hγt⟩

/-- **body-622b-2 (Step 3, BANK) — the aligned recovered inner forest is a live W‴ forest.**  (From Step 3
+ `o.B.2`.) -/
theorem phi4WTriplePrime_forwardAligned_mem (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_forwardAlignedRecoveredInnerForest o
      ∈ phi4WTriplePrimeIndex o.γ.1.boundaryCompletedResolvedGraph :=
  (phi4WTriplePrime_forwardAlignedRecoveredInnerForest_eq o).symm ▸ o.B.2

/-! ## Step 4 — the existing-tag bridge (the tag's own transport, identity-collapsed) -/

/-- The forward-native forest decontraction input (the `o`-native inverse data), abbreviated. -/
private noncomputable def phi4WTriplePrime_forwardInput
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_ForestDecontractionInput (phi4WTriplePrime_forestBlockForward s)
      ⟨phi4WTriplePrime_remnantComponent o, phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ :=
  phi4WTriplePrime_forestDecontractionInput_of_starTouching (phi4WTriplePrime_forestBlockForward s)
    (δ := ⟨phi4WTriplePrime_remnantComponent o,
      phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩)
    (phi4WTriplePrime_remnant_star_touching o)

/-- **body-622b-2 (Step 4, core) — the transported native recovered inner forest IS the aligned forest.**  A
HOMOGENEOUS equality over `o.γ.1.bcrg`: transporting the native `recoveredInnerForest` along the body-622a
parent identification, then computing its de-promotion component-by-component (`transportSub` on each
`inv_innerComponent` reproduces the aligned de-promotion), lands exactly on the aligned forest. -/
private theorem phi4WTriplePrime_transportRAS_recoveredInnerForest_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s) :
    phi4WTriplePrime_transportRAS
        (congrArg ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph
          (phi4WTriplePrime_forwardForest_recoveredParent_eq s o))
        (phi4WTriplePrime_inv_recoveredInnerForest (phi4WTriplePrime_forwardInput o)
          (phi4WTriplePrime_inv_innerForest_CD_proof (phi4WTriplePrime_forwardInput o)))
      = phi4WTriplePrime_forwardAlignedRecoveredInnerForest o := by
  apply phi4WTriplePrime_admissible_ext_elements
  rw [phi4WTriplePrime_transportRAS_elements, phi4WTriplePrime_inv_recoveredInnerForest_elements,
    Finset.image_image, phi4WTriplePrime_forwardAlignedRecoveredInnerForest_elements]
  apply Finset.image_congr
  intro γt _
  simp only [Function.comp_apply]
  -- per-component: `transportSub _ (inv_innerComponent I_o γ) = alignedInnerComponent o γ`
  apply ResolvedFeynmanSubgraph.ext
  · rw [phi4WTriplePrime_transportSub_vertices, phi4WTriplePrime_inv_innerComponent_vertices]; rfl
  · rw [phi4WTriplePrime_transportSub_internalEdges, phi4WTriplePrime_inv_innerComponent_internalEdges]; rfl
  · rw [phi4WTriplePrime_transportSub_externalLegs]
    exact congrArg (fun H => H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γt.1.vertices))
      (congrArg ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph
        (phi4WTriplePrime_forwardForest_recoveredParent_eq s o))

/-- **body-622b-2 (Step 4, HEADLINE) — the existing recovered-forest tag equals the aligned forest.**  Inside
the `o.γ.1.bcrg` fiber: the body-614 `recoveredForestTag` (whose OWN `▸` transport carries the native inner
forest onto the `o.γ.1` owner) equals `⟨forwardAlignedRecoveredInnerForest o, _⟩`.  The transport is
identity-collapsed via `eqRec`-HEq + body-620's `recoveredForestTag_transport` (native-fiber choose alignment)
+ Step-4-core; NO `HEq` / `cast` / `▸` in the PUBLIC type.  Private, motive-controlled transport
eliminators are used internally; no transport API or heterogeneous equality is exported. -/
theorem phi4WTriplePrime_forwardAligned_recoveredForestTag_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    (hmem : o.γ.1 ∈ (phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s)).elements)
    (hq : ∃ δ : {x // x ∈ (phi4WTriplePrime_forestBlockForward s).2.1.elements},
        phi4WTriplePrime_inv_regionComponentOf (phi4WTriplePrime_forestBlockForward s) δ = o.γ.1)
    (hst : phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s) hq.choose) :
    phi4WTriplePrime_recoveredForestTag (phi4WTriplePrime_forestBlockForward s) ⟨o.γ.1, hmem⟩ hq hst
      = ⟨phi4WTriplePrime_forwardAlignedRecoveredInnerForest o,
         phi4WTriplePrime_forwardAligned_mem o⟩ := by
  set z := phi4WTriplePrime_forestBlockForward s with hz
  -- native data at the forward remnant
  set δo : {x // x ∈ z.2.1.elements} :=
    ⟨phi4WTriplePrime_remnantComponent o, phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ with hδo
  have hsto : phi4WTriplePrime_inv_isForestImage z δo := phi4WTriplePrime_remnant_star_touching o
  set Isto := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hsto with hIsto
  set Ihst := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst with hIhst
  have hRP : phi4WTriplePrime_inv_recoveredParent Isto = o.γ.1 :=
    phi4WTriplePrime_forwardForest_recoveredParent_eq s o
  -- the `hq.choose` owner is the forward remnant
  have hchoose : hq.choose = δo :=
    phi4WTriplePrime_inv_regionComponentOf_injective z
      (hq.choose_spec.trans
        (((phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto).trans hRP).symm))
  -- bridge parent of the `hq.choose` input to the native parent
  have heq_d : phi4WTriplePrime_inv_recoveredParent Ihst
      = phi4WTriplePrime_inv_recoveredParent Isto :=
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst).symm.trans
      ((congrArg (phi4WTriplePrime_inv_regionComponentOf z) hchoose).trans
        (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto))
  -- the ambient-bcrg equality carrying the tag transport onto `o.γ.1`
  have hBeq : (phi4WTriplePrime_inv_recoveredParent Isto).boundaryCompletedResolvedGraph
      = o.γ.1.boundaryCompletedResolvedGraph :=
    congrArg ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph hRP
  -- the native and `hst` tag elements
  let tagIo : (phi4WTriplePrimeCanonicalSupply.summandSupply
        (phi4WTriplePrime_inv_recoveredParent Isto).boundaryCompletedResolvedGraph).ForestIdx :=
    ⟨phi4WTriplePrime_inv_recoveredInnerForest Isto
        (phi4WTriplePrime_inv_innerForest_CD_proof Isto),
      phi4WTriplePrime_inv_recoveredInnerForest_mem_proof Isto⟩
  let tagHst : (phi4WTriplePrimeCanonicalSupply.summandSupply
        (phi4WTriplePrime_inv_recoveredParent Ihst).boundaryCompletedResolvedGraph).ForestIdx :=
    ⟨phi4WTriplePrime_inv_recoveredInnerForest Ihst
        (phi4WTriplePrime_inv_innerForest_CD_proof Ihst),
      phi4WTriplePrime_inv_recoveredInnerForest_mem_proof Ihst⟩
  have heqInternal : phi4WTriplePrime_inv_recoveredParent Ihst = o.γ.1 :=
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst).symm.trans hq.choose_spec
  -- (B) HEq tagIo ⟨aligned, _⟩ : identity-collapse the fiber transport of the ForestIdx
  have hBval : (phi4WTriplePrime_transportFI hBeq tagIo).1
      = phi4WTriplePrime_forwardAlignedRecoveredInnerForest o := by
    rw [phi4WTriplePrime_transportFI_val]
    exact phi4WTriplePrime_transportRAS_recoveredInnerForest_eq o
  have hBsub : phi4WTriplePrime_transportFI hBeq tagIo
      = ⟨phi4WTriplePrime_forwardAlignedRecoveredInnerForest o,
         phi4WTriplePrime_forwardAligned_mem o⟩ := Subtype.ext hBval
  have hB : HEq tagIo (⟨phi4WTriplePrime_forwardAlignedRecoveredInnerForest o,
      phi4WTriplePrime_forwardAligned_mem o⟩ :
      (phi4WTriplePrimeCanonicalSupply.summandSupply
        o.γ.1.boundaryCompletedResolvedGraph).ForestIdx) := by
    have h0 : HEq (phi4WTriplePrime_transportFI hBeq tagIo) tagIo :=
      rec_heq_of_heq (C := fun H => (phi4WTriplePrimeCanonicalSupply.summandSupply H).ForestIdx)
        hBeq (HEq.refl tagIo)
    rw [hBsub] at h0
    exact h0.symm
  -- (A) HEq tagHst tagIo, via `recoveredForestTag_transport`
  have htr := phi4WTriplePrime_recoveredForestTag_transport z hsto hst heq_d
  have hA : HEq tagHst tagIo := by
    have h1 : HEq (heq_d ▸ tagHst) tagHst :=
      rec_heq_of_heq
        (C := fun P => (phi4WTriplePrimeCanonicalSupply.summandSupply
          P.boundaryCompletedResolvedGraph).ForestIdx)
        heq_d (HEq.refl tagHst)
    have htr' : heq_d ▸ tagHst = tagIo := htr
    rw [htr'] at h1
    exact h1.symm
  -- assemble via the tag's own transport
  apply eq_of_heq
  show HEq (heqInternal ▸ tagHst)
    (⟨phi4WTriplePrime_forwardAlignedRecoveredInnerForest o,
      phi4WTriplePrime_forwardAligned_mem o⟩ :
      (phi4WTriplePrimeCanonicalSupply.summandSupply
        o.γ.1.boundaryCompletedResolvedGraph).ForestIdx)
  exact HEq.trans
    (rec_heq_of_heq
      (C := fun P => (phi4WTriplePrimeCanonicalSupply.summandSupply
        P.boundaryCompletedResolvedGraph).ForestIdx)
      heqInternal (HEq.refl tagHst)) (hA.trans hB)

/-! ## Step 5 — the FOREST exact payload in the general forward-image context -/

/-- **body-622b-2 (Step 5, HEADLINE) — the FOREST exact payload.**  For the canonical forward occurrence
owner `o.γ.1` (in the recovered outer forest of `forestBlockForward s`), the body-614 recovered global choice
is EXACTLY `Sum.inr o.B`.  Settles body-614's deferred FOREST exact `Sum.inr` obligation in the GENERAL
forward-image context (via Step 4 + Step 3 + proof irrelevance). -/
theorem phi4WTriplePrime_forwardAligned_recoveredChoice_eq
    (o : Phi4WTriplePrime_ForestChoiceOccurrence s)
    (hmem : o.γ.1 ∈ (phi4WTriplePrime_recoveredOuter (phi4WTriplePrime_forestBlockForward s)).elements) :
    phi4WTriplePrime_recoveredChoice (phi4WTriplePrime_forestBlockForward s)
        ⟨o.γ.1, hmem⟩ (Finset.mem_attach _ _)
      = Sum.inr o.B := by
  set z := phi4WTriplePrime_forestBlockForward s with hz
  set δo : {x // x ∈ z.2.1.elements} :=
    ⟨phi4WTriplePrime_remnantComponent o, phi4WTriplePrime_remnantComponent_mem_quotientForest o⟩ with hδo
  have hsto : phi4WTriplePrime_inv_isForestImage z δo := phi4WTriplePrime_remnant_star_touching o
  have hRP : phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hsto) = o.γ.1 :=
    phi4WTriplePrime_forwardForest_recoveredParent_eq s o
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = o.γ.1 :=
    ⟨δo, (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto).trans hRP⟩
  have hchoose : hq.choose = δo :=
    phi4WTriplePrime_inv_regionComponentOf_injective z
      (hq.choose_spec.trans
        (((phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto).trans hRP).symm))
  have hst : phi4WTriplePrime_inv_isForestImage z hq.choose := by rw [hchoose]; exact hsto
  unfold phi4WTriplePrime_recoveredChoice
  rw [dif_pos hq, dif_pos hst]
  refine congrArg Sum.inr ?_
  rw [phi4WTriplePrime_forwardAligned_recoveredForestTag_eq o hmem hq hst]
  exact Subtype.ext (phi4WTriplePrime_forwardAlignedRecoveredInnerForest_eq o)

end GaugeGeometry.QFT.Combinatorial
