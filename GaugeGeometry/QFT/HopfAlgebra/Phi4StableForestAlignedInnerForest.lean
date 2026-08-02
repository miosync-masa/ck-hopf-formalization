import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForestBlockInnerElements

/-!
# QFT-R1-body-647b-2 — the DEF-LEVEL STABLE aligned recovered inner forest + FOREST exact payload

Body-647b-1 delivered the AMBIENT-FREE combinatorial core (`stableForwardForest_touchedOuterForest_eq`: the
touched outer forest of the forward remnant IS the promoted inner forest `o.B.1`, component for component with
multiplicity, as a raw `Finset (ResolvedFeynmanSubgraph G)` equality).  This body (647b-2) does NOT re-prove
geometry: it PACKAGES TYPES in the stable fiber.  The recovered inner forest is rebuilt DIRECTLY over
`stableLocalBoundaryCompletedGraph o.γ.1` (a genuine DE-PROMOTION, NOT an `o.B.1` alias), proved `= o.B.1`
(homogeneous raw), and the general forward-image exact FOREST payload `stableRecoveredChoice … = Sum.inr o.B`
(deferred since body-643) is closed.  It is the STABLE MIRROR of old body-622b-2; old 622b-2 terms are NEVER
consumed as terms — only the proof shape is mirrored.

## Steps
* **Step 0 (PRIVATE transport utilities)** — `stableTransportSub` / `_vertices` / `_internalEdges` /
  `_externalLegs`, `stableTransportRAS` / `_elements`, and the `StableLocalForestIdx` transport
  `stableTransportLFI` / `_val` (the `▸` confined to their BODIES; the TYPES are clean).  Plus a `private`
  clean element-set ext `stableAligned_admissible_ext_elements` (bypasses the `[IsAmbientInvariantDivergence]`-
  polluted public ext).
* **Step 1 (Aligned component + round-trip)** — `stableForwardAlignedInnerComponent`: each recovered inner
  component built DIRECTLY as a `ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)` (vertices /
  internal edges = the touched component's, legs = the stable ambient legs saturating it).
  `stableForwardAligned_component_roundtrip`: de-promoting `stableRootRelativeInner o.γ.1 δᵢ` recovers `δᵢ`.
* **Step 2 (Aligned forest)** — `stableForwardAlignedRecoveredInnerForest o :
  ResolvedAdmissibleSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)` via `ofElements` over the touched
  forest's de-promotions.  CD / disjointness by the 647b-1 round-trip.  It is NEVER set to `o.B.1`.
* **Step 3 (Raw round-trip)** — `stableForwardAlignedRecoveredInnerForest_eq o = o.B.1`, a fully HOMOGENEOUS raw
  `ResolvedAdmissibleSubgraph (SLBCG o.γ.1)` equality (from 647b-1 + `stableRootRelativeInner_injOn_elements`);
  `_mem` (live W‴ membership, thin from Step 3 + `o.B.2`).
* **Step 4 (Existing tag bridge, THE HEq CRUX)** — `stableForwardAligned_recoveredForestTag_eq`: the body-643
  `stableRecoveredForestTag` equals `⟨forwardAlignedRecoveredInnerForest o, _⟩` INSIDE the `o.γ.1` fiber.  The
  tag's OWN `heq ▸` owner transport is identity-collapsed via `eqRec`-HEq (`rec_heq_of_heq`) + the private
  `stableRecoveredForestTag_transport` (native-fiber choose alignment) + Step-4-core.  ALL `HEq` lives in the
  PRIVATE proof body; the PUBLIC type is fully homogeneous `StableLocalForestIdx o.γ.1`.
* **Step 5 (Exact payload)** — `stableForwardAligned_recoveredChoice_eq`: `stableRecoveredChoice hSt
  (stableForestBlockForward s) ⟨o.γ.1, _⟩ _ = Sum.inr o.B`.  Settles body-643's deferred FOREST `Sum.inr`
  obligation in the GENERAL forward-image context (Step 4 + Step 3 + proof irrelevance).

## Ownership boundary — MUST NOT consume as terms
The OLD 622b-2 `phi4WTriplePrime_forwardAligned*` / `_transportSub` / `_transportRAS` / `_transportFI` /
`_recoveredForestTag_eq` / `_recoveredChoice_eq` are NEVER consumed (proof shape mirrored only).  Reused AS
STATED: body-647b-1 `stableForwardForest_touchedOuterForest_eq`; body-647a `stableForwardForest_recoveredParent_eq`
/ `stableRemnant_star_touching`; body-643 `stableRecoveredForestTag` / `stableRecoveredChoice`; body-642
`stableInvRecoveredInnerForest{,Value,_elements}` / `stableInvInnerComponent{,_vertices,_internalEdges}`; body-635
`StableForestChoiceOccurrence` / `stableRemnantComponent` / `stableForestOcc_B_saturated`; body-639b
`stableRemnantComponent_mem_quotientForest`; body-632/630 `stableRootRelativeInner{,_vertices,_internalEdges,
_injOn_elements}` / `StableLocalForestIdx` / `stableLocalBoundaryCompletedGraph`; the old completion-INDEPENDENT
inverse sectors (`phi4WTriplePrime_inv_regionComponentOf{,_eq_parent,_injective}` /
`_forestDecontractionInput_of_starTouching` / `_isForestImage` / `_recoveredParent` / `_recoveredOuter`);
`externalLegs_eq_filter_of_saturated`, `rec_heq_of_heq`, `eq_of_heq`.

## HALT / red lines
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence class in any
declaration TYPE.  NO public `HEq` / `cast` / graph-data `▸` in any declaration TYPE — every transport `▸` is
inside a `private` helper BODY or a proof; the aligned forest is a genuine DE-PROMOTION `def`, NOT an `o.B.1`
alias.  NO `subst` between FIXED owners; NO cross-ambient subgraph `Eq` issued.  HALT (not entered):
`recoveredOuter = s.outer`, the choice `funext`, the whole `Equiv`, the headline left inverse (all 647c).  NO
`Bijective` / bare `Equiv` / `sum_bij` / alpha / coassoc / orbit quotient / dedup.  ZERO old-622b term consume
(mirror only).  ZERO new `structure` / `class` / permanent `instance` (one file-local `local instance`; every
transport-bearing helper is `private`).  NO `sorry` / `admit` / `native_decide`.

## Split note
FULL 647b-2 (Steps 0–5) is delivered in this single file; NO honest split was needed.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily647b2 :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — generic dependent-transport utilities (`▸` confined to BODIES; clean TYPES) -/

/-- **body-647b-2 (Step 0) — a clean element-set extensionality for φ⁴ admissible subgraphs.**  Bypasses the
`[IsAmbientInvariantDivergence]`-polluted public ext; the two non-`elements` fields are `Prop`s, so equal
element sets force equality by `cases` + definitional proof irrelevance.  PRIVATE (mirror of body-644). -/
private theorem stableAligned_admissible_ext_elements {H : ResolvedFeynmanGraph}
    {A₁ A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H}
    (h : @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₁
       = @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily H A₂) : A₁ = A₂ := by
  cases A₁; cases A₂; cases h; rfl

/-- Transport a `ResolvedFeynmanSubgraph` along a graph equality (`▸` confined to the body). -/
private def stableTransportSub {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) : ResolvedFeynmanSubgraph H₂ := h ▸ δ

@[simp] private theorem stableTransportSub_vertices {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (stableTransportSub h δ).vertices = δ.vertices := by
  cases h; rfl

@[simp] private theorem stableTransportSub_internalEdges {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (stableTransportSub h δ).internalEdges = δ.internalEdges := by
  cases h; rfl

@[simp] private theorem stableTransportSub_externalLegs {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (δ : ResolvedFeynmanSubgraph H₁) :
    (stableTransportSub h δ).externalLegs = δ.externalLegs := by
  cases h; rfl

/-- Transport a `ResolvedAdmissibleSubgraph` along a graph equality (`▸` confined to the body). -/
private def stableTransportRAS {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (X : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H₁) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H₂ := h ▸ X

private theorem stableTransportRAS_elements {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (X : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily H₁) :
    (stableTransportRAS h X).elements = X.elements.image (stableTransportSub h) := by
  cases h; exact (Finset.image_id).symm

/-- Transport a `StableLocalForestIdx` along a SUBGRAPH equality (`▸` confined to the body). -/
private noncomputable def stableTransportLFI {γ₁ γ₂ : ResolvedFeynmanSubgraph G} (h : γ₁ = γ₂)
    (B : StableLocalForestIdx γ₁) : StableLocalForestIdx γ₂ := h ▸ B

private theorem stableTransportLFI_val {γ₁ γ₂ : ResolvedFeynmanSubgraph G} (h : γ₁ = γ₂)
    (B : StableLocalForestIdx γ₁) :
    (stableTransportLFI h B).1
      = stableTransportRAS (congrArg stableLocalBoundaryCompletedGraph h) B.1 := by
  cases h; rfl

variable {hSt : StableResolvedBoundaryIds G} {s : StablePhi4MixedSplitChoice G hSt}

/-! ## Step 1 — the aligned inner component (de-promotion into the `SLBCG o.γ.1` fiber) -/

/-- **body-647b-2 (Step 1) — a touched component's vertices lie in the stable inner completion** (via 647b-1). -/
theorem stableForwardAligned_verts_subset (o : StableForestChoiceOccurrence s)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements) :
    γ.vertices ⊆ (stableLocalBoundaryCompletedGraph o.γ.1).vertices := by
  rw [stableForwardForest_touchedOuterForest_eq s o] at hγ
  obtain ⟨δᵢ, hδᵢ, rfl⟩ := Finset.mem_image.mp hγ
  rw [stableRootRelativeInner_vertices]
  exact δᵢ.vertices_subset

/-- **body-647b-2 (Step 1) — a touched component's internal edges embed in the stable inner completion** (via
647b-1). -/
theorem stableForwardAligned_internalEdges_le (o : StableForestChoiceOccurrence s)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements) :
    γ.internalEdges ≤ (stableLocalBoundaryCompletedGraph o.γ.1).internalEdges := by
  rw [stableForwardForest_touchedOuterForest_eq s o] at hγ
  obtain ⟨δᵢ, hδᵢ, rfl⟩ := Finset.mem_image.mp hγ
  rw [stableRootRelativeInner_internalEdges]
  exact δᵢ.internalEdges_le

/-- **body-647b-2 (Step 1) — the aligned inner component.**  For a touched outer component `γ` of the forward
remnant, the de-promoted subgraph over `stableLocalBoundaryCompletedGraph o.γ.1`: `γ`'s vertices / internal
edges verbatim, and the stable ambient legs saturating it.  Built DIRECTLY in the `SLBCG o.γ.1` fiber (no
transport).  NOT an `o.B.1` alias. -/
noncomputable def stableForwardAlignedInnerComponent
    (o : StableForestChoiceOccurrence s) (γ : ResolvedFeynmanSubgraph G)
    (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements) :
    ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1) where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := (stableLocalBoundaryCompletedGraph o.γ.1).externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈ γ.vertices)
  vertices_subset := stableForwardAligned_verts_subset o hγ
  internalEdges_le := stableForwardAligned_internalEdges_le o hγ
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := γ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

/-- **body-647b-2 (Step 1, round-trip) — the aligned de-promotion of a promoted inner component is that
component.**  For `δᵢ ∈ o.B.1.elements`, de-promoting `stableRootRelativeInner o.γ.1 δᵢ` recovers `δᵢ` exactly
(its saturated legs are reconstructed as the stable ambient filter). -/
theorem stableForwardAligned_component_roundtrip
    (o : StableForestChoiceOccurrence s)
    {δᵢ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph o.γ.1)}
    (hδᵢ : δᵢ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            (stableLocalBoundaryCompletedGraph o.γ.1) o.B.1)
    (hγ : stableRootRelativeInner o.γ.1 δᵢ ∈ (phi4WTriplePrime_touchedOuterForest
        (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements) :
    stableForwardAlignedInnerComponent o (stableRootRelativeInner o.γ.1 δᵢ) hγ = δᵢ := by
  apply ResolvedFeynmanSubgraph.ext
  · exact stableRootRelativeInner_vertices o.γ.1 δᵢ
  · exact stableRootRelativeInner_internalEdges o.γ.1 δᵢ
  · show (stableLocalBoundaryCompletedGraph o.γ.1).externalLegs.filter
        (fun ℓ => ℓ.attachedTo ∈ (stableRootRelativeInner o.γ.1 δᵢ).vertices) = δᵢ.externalLegs
    rw [stableRootRelativeInner_vertices]
    exact (externalLegs_eq_filter_of_saturated δᵢ (stableForestOcc_B_saturated o hδᵢ)).symm

/-! ## Step 2 — the aligned recovered inner forest -/

/-- **body-647b-2 (Step 2, HEADLINE) — the aligned recovered inner forest.**  A genuine RECONSTRUCTION over
`stableLocalBoundaryCompletedGraph o.γ.1`: one aligned de-promotion per touched outer component of the forward
remnant (reading 647b-1's correspondence IN REVERSE).  CD + pairwise disjointness come from the 647b-1
round-trip that re-identifies each de-promotion with an `o.B.1` component.  It is NOT `o.B.1`. -/
noncomputable def stableForwardAlignedRecoveredInnerForest
    (o : StableForestChoiceOccurrence s) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph o.γ.1) :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements.attach.image
      (fun γ => stableForwardAlignedInnerComponent o γ.1 γ.2))
    (by
      intro δ' hδ'
      obtain ⟨γt, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨d, hd⟩ := γt
      have hdt := hd
      rw [stableForwardForest_touchedOuterForest_eq s o] at hdt
      obtain ⟨δᵢ, hδᵢ, hdeq⟩ := Finset.mem_image.mp hdt
      subst hdeq
      rw [stableForwardAligned_component_roundtrip o hδᵢ hd]
      exact o.B.1.isConnectedDivergent δᵢ hδᵢ)
    (by
      intro δ' hδ' δ'' hδ'' hne
      obtain ⟨γa, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨γb, -, rfl⟩ := Finset.mem_image.mp hδ''
      obtain ⟨da, hda⟩ := γa
      obtain ⟨db, hdb⟩ := γb
      have hdat := hda
      rw [stableForwardForest_touchedOuterForest_eq s o] at hdat
      obtain ⟨δa, hδa, hdaeq⟩ := Finset.mem_image.mp hdat
      have hdbt := hdb
      rw [stableForwardForest_touchedOuterForest_eq s o] at hdbt
      obtain ⟨δb, hδb, hdbeq⟩ := Finset.mem_image.mp hdbt
      subst hdaeq
      subst hdbeq
      have hne' : δa ≠ δb := by
        intro h
        apply hne
        rw [stableForwardAligned_component_roundtrip o hδa hda,
            stableForwardAligned_component_roundtrip o hδb hdb, h]
      rw [stableForwardAligned_component_roundtrip o hδa hda,
          stableForwardAligned_component_roundtrip o hδb hdb]
      exact o.B.1.pairwiseDisjoint hδa hδb hne')

@[simp] theorem stableForwardAlignedRecoveredInnerForest_elements
    (o : StableForestChoiceOccurrence s) :
    (stableForwardAlignedRecoveredInnerForest o).elements
      = (phi4WTriplePrime_touchedOuterForest (stableForestBlockForward s)
          ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements.attach.image
        (fun γ => stableForwardAlignedInnerComponent o γ.1 γ.2) := rfl

/-! ## Step 3 — the homogeneous raw round-trip `stableForwardAlignedRecoveredInnerForest o = o.B.1` -/

/-- **body-647b-2 (Step 3, HEADLINE) — the aligned recovered inner forest IS `o.B.1`.**  A fully HOMOGENEOUS
raw `ResolvedAdmissibleSubgraph (SLBCG o.γ.1)` equality (both sides in the same fiber): by 647b-1 the touched
forest is `o.B.1`'s promotion image, and each de-promotion round-trips (`stableRootRelativeInner_injOn`
mediating), so the component sets coincide. -/
theorem stableForwardAlignedRecoveredInnerForest_eq
    (o : StableForestChoiceOccurrence s) :
    stableForwardAlignedRecoveredInnerForest o = o.B.1 := by
  apply stableAligned_admissible_ext_elements
  rw [stableForwardAlignedRecoveredInnerForest_elements]
  apply Finset.ext
  intro η
  constructor
  · intro hη
    obtain ⟨γt, -, rfl⟩ := Finset.mem_image.mp hη
    obtain ⟨d, hd⟩ := γt
    have hdt := hd
    rw [stableForwardForest_touchedOuterForest_eq s o] at hdt
    obtain ⟨δᵢ, hδᵢ, hdeq⟩ := Finset.mem_image.mp hdt
    subst hdeq
    rw [stableForwardAligned_component_roundtrip o hδᵢ hd]
    exact hδᵢ
  · intro hη
    apply Finset.mem_image.mpr
    have hγt : stableRootRelativeInner o.γ.1 η ∈ (phi4WTriplePrime_touchedOuterForest
        (stableForestBlockForward s)
        ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩).elements := by
      rw [stableForwardForest_touchedOuterForest_eq s o]
      exact Finset.mem_image.mpr ⟨η, hη, rfl⟩
    exact ⟨⟨stableRootRelativeInner o.γ.1 η, hγt⟩, Finset.mem_attach _ _,
      stableForwardAligned_component_roundtrip o hη hγt⟩

/-- **body-647b-2 (Step 3, BANK) — the aligned recovered inner forest is a live W‴ forest.**  (From Step 3 +
`o.B.2`; a Prop-membership `▸`.) -/
theorem stableForwardAlignedRecoveredInnerForest_mem (o : StableForestChoiceOccurrence s) :
    stableForwardAlignedRecoveredInnerForest o
      ∈ phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph o.γ.1) :=
  (stableForwardAlignedRecoveredInnerForest_eq o).symm ▸ o.B.2

/-! ## Step 4 — the existing-tag bridge (the 643 tag's own transport, identity-collapsed) -/

/-- **body-647b-2 (Step 4, PRIVATE transport collapse) — the recovered-forest-tag transport collapses.**  For
two star-touching targets `d`, `δ` whose recovered parents coincide, the `Eq.rec` transport of the stable
recovered inner W‴ forest payload at `d` onto the one at `δ` is the identity.  Owner determinacy + component
injectivity pin `d = δ`; after `subst`, the two `ForestDecontractionInput`s (a `Prop`) are DEFINITIONALLY
proof-irrelevant, so the payloads are defeq and the transport reduces to `rfl`.  PRIVATE — the `▸` is in the
BODY; NO `HEq` / `cast`.  STABLE mirror of body-620's `recoveredForestTag_transport`. -/
private theorem stableRecoveredForestTag_transport (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hδ : phi4WTriplePrime_inv_isForestImage z δ)
    {d : {x // x ∈ z.2.1.elements}} (hst_d : phi4WTriplePrime_inv_isForestImage z d)
    (heq_d : phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)
            = phi4WTriplePrime_inv_recoveredParent
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ)) :
    heq_d ▸ stableInvRecoveredInnerForestValue hSt
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst_d)
      = stableInvRecoveredInnerForestValue hSt
              (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) := by
  have hdδ : d = δ := by
    apply phi4WTriplePrime_inv_regionComponentOf_injective z
    rw [phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst_d,
        phi4WTriplePrime_inv_regionComponentOf_eq_parent z hδ]
    exact heq_d
  subst hdδ
  rfl

/-- **body-647b-2 (Step 4, core) — the transported native recovered inner forest IS the aligned forest.**  A
HOMOGENEOUS equality over `SLBCG o.γ.1`: transporting the native `stableInvRecoveredInnerForest` along the
647a parent identification, then computing its de-promotion component-by-component (`stableTransportSub` on each
`stableInvInnerComponent` reproduces the aligned de-promotion), lands exactly on the aligned forest. -/
private theorem stableTransportRAS_recoveredInnerForest_eq
    (o : StableForestChoiceOccurrence s) :
    stableTransportRAS
        (congrArg stableLocalBoundaryCompletedGraph
          (stableForwardForest_recoveredParent_eq s o))
        (stableInvRecoveredInnerForest hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching (stableForestBlockForward s)
            (stableRemnant_star_touching s o)))
      = stableForwardAlignedRecoveredInnerForest o := by
  apply stableAligned_admissible_ext_elements
  rw [stableTransportRAS_elements, stableInvRecoveredInnerForest_elements,
    Finset.image_image, stableForwardAlignedRecoveredInnerForest_elements]
  apply Finset.image_congr
  intro γt _
  simp only [Function.comp_apply]
  apply ResolvedFeynmanSubgraph.ext
  · rw [stableTransportSub_vertices, stableInvInnerComponent_vertices]; rfl
  · rw [stableTransportSub_internalEdges, stableInvInnerComponent_internalEdges]; rfl
  · rw [stableTransportSub_externalLegs]
    exact congrArg (fun H => H.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ γt.1.vertices))
      (congrArg stableLocalBoundaryCompletedGraph
        (stableForwardForest_recoveredParent_eq s o))

/-- **body-647b-2 (Step 4, HEADLINE) — the existing recovered-forest tag equals the aligned forest.**  Inside
the `o.γ.1` fiber: the body-643 `stableRecoveredForestTag` (whose OWN `heq ▸` transport carries the native inner
forest onto the `o.γ.1` owner) equals `⟨stableForwardAlignedRecoveredInnerForest o, _⟩`.  The transport is
identity-collapsed via `eqRec`-HEq (`rec_heq_of_heq`) + `stableRecoveredForestTag_transport` + Step-4-core; ALL
`HEq` lives in the PRIVATE proof body, and the PUBLIC type is fully homogeneous `StableLocalForestIdx o.γ.1`. -/
theorem stableForwardAligned_recoveredForestTag_eq
    (o : StableForestChoiceOccurrence s)
    (hmem : o.γ.1 ∈ (phi4WTriplePrime_recoveredOuter (stableForestBlockForward s)).elements)
    (hq : ∃ δ : {x // x ∈ (stableForestBlockForward s).2.1.elements},
        phi4WTriplePrime_inv_regionComponentOf (stableForestBlockForward s) δ = o.γ.1)
    (hst : phi4WTriplePrime_inv_isForestImage (stableForestBlockForward s) hq.choose) :
    stableRecoveredForestTag hSt (stableForestBlockForward s) ⟨o.γ.1, hmem⟩ hq hst
      = ⟨stableForwardAlignedRecoveredInnerForest o,
         stableForwardAlignedRecoveredInnerForest_mem o⟩ := by
  set z := stableForestBlockForward s with hz
  set δo : {x // x ∈ z.2.1.elements} :=
    ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩ with hδo
  have hsto : phi4WTriplePrime_inv_isForestImage z δo := stableRemnant_star_touching s o
  set Isto := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hsto with hIsto
  set Ihst := phi4WTriplePrime_forestDecontractionInput_of_starTouching z hst with hIhst
  have hRP : phi4WTriplePrime_inv_recoveredParent Isto = o.γ.1 :=
    stableForwardForest_recoveredParent_eq s o
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
  have heqInternal : phi4WTriplePrime_inv_recoveredParent Ihst = o.γ.1 :=
    (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hst).symm.trans hq.choose_spec
  -- the native and `hst` tag payloads
  let tagIo : StableLocalForestIdx (phi4WTriplePrime_inv_recoveredParent Isto) :=
    stableInvRecoveredInnerForestValue hSt Isto
  let tagHst : StableLocalForestIdx (phi4WTriplePrime_inv_recoveredParent Ihst) :=
    stableInvRecoveredInnerForestValue hSt Ihst
  -- (B) HEq tagIo ⟨aligned, _⟩ : identity-collapse the fiber transport of the tag
  have hBval : (stableTransportLFI hRP tagIo).1
      = stableForwardAlignedRecoveredInnerForest o := by
    rw [stableTransportLFI_val]
    exact stableTransportRAS_recoveredInnerForest_eq o
  have hBsub : stableTransportLFI hRP tagIo
      = (⟨stableForwardAlignedRecoveredInnerForest o,
          stableForwardAlignedRecoveredInnerForest_mem o⟩ :
          StableLocalForestIdx o.γ.1) := Subtype.ext hBval
  have hB : HEq tagIo (⟨stableForwardAlignedRecoveredInnerForest o,
      stableForwardAlignedRecoveredInnerForest_mem o⟩ : StableLocalForestIdx o.γ.1) := by
    have h0 : HEq (stableTransportLFI hRP tagIo) tagIo :=
      rec_heq_of_heq (C := fun γ => StableLocalForestIdx γ) hRP (HEq.refl tagIo)
    rw [hBsub] at h0
    exact h0.symm
  -- (A) HEq tagHst tagIo, via `stableRecoveredForestTag_transport`
  have htr := stableRecoveredForestTag_transport hSt z hsto hst heq_d
  have hA : HEq tagHst tagIo := by
    have h1 : HEq (heq_d ▸ tagHst) tagHst :=
      rec_heq_of_heq (C := fun P => StableLocalForestIdx P) heq_d (HEq.refl tagHst)
    have htr' : heq_d ▸ tagHst = tagIo := htr
    rw [htr'] at h1
    exact h1.symm
  -- assemble via the 643 tag's own transport
  apply eq_of_heq
  show HEq (heqInternal ▸ tagHst)
    (⟨stableForwardAlignedRecoveredInnerForest o,
      stableForwardAlignedRecoveredInnerForest_mem o⟩ : StableLocalForestIdx o.γ.1)
  exact HEq.trans
    (rec_heq_of_heq (C := fun P => StableLocalForestIdx P) heqInternal (HEq.refl tagHst))
    (hA.trans hB)

/-! ## Step 5 — the FOREST exact payload in the general forward-image context -/

/-- **body-647b-2 (Step 5, HEADLINE) — the FOREST exact payload.**  For the canonical forward occurrence owner
`o.γ.1` (in the recovered outer forest of `stableForestBlockForward s`), the body-643 recovered global choice is
EXACTLY `Sum.inr o.B`.  Settles body-643's deferred FOREST exact `Sum.inr` obligation in the GENERAL
forward-image context (via Step 4 + Step 3 + proof irrelevance). -/
theorem stableForwardAligned_recoveredChoice_eq
    (o : StableForestChoiceOccurrence s)
    (hmem : o.γ.1 ∈ (phi4WTriplePrime_recoveredOuter (stableForestBlockForward s)).elements) :
    stableRecoveredChoice hSt (stableForestBlockForward s)
        ⟨o.γ.1, hmem⟩ (Finset.mem_attach _ _)
      = Sum.inr o.B := by
  set z := stableForestBlockForward s with hz
  set δo : {x // x ∈ z.2.1.elements} :=
    ⟨stableRemnantComponent o, stableRemnantComponent_mem_quotientForest s o⟩ with hδo
  have hsto : phi4WTriplePrime_inv_isForestImage z δo := stableRemnant_star_touching s o
  have hRP : phi4WTriplePrime_inv_recoveredParent
        (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hsto) = o.γ.1 :=
    stableForwardForest_recoveredParent_eq s o
  have hq : ∃ δ : {x // x ∈ z.2.1.elements},
      phi4WTriplePrime_inv_regionComponentOf z δ = o.γ.1 :=
    ⟨δo, (phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto).trans hRP⟩
  have hchoose : hq.choose = δo :=
    phi4WTriplePrime_inv_regionComponentOf_injective z
      (hq.choose_spec.trans
        (((phi4WTriplePrime_inv_regionComponentOf_eq_parent z hsto).trans hRP).symm))
  have hst : phi4WTriplePrime_inv_isForestImage z hq.choose := by rw [hchoose]; exact hsto
  unfold stableRecoveredChoice
  rw [dif_pos hq, dif_pos hst]
  refine congrArg Sum.inr ?_
  rw [stableForwardAligned_recoveredForestTag_eq o hmem hq hst]
  exact Subtype.ext (stableForwardAlignedRecoveredInnerForest_eq o)

end GaugeGeometry.QFT.Combinatorial
