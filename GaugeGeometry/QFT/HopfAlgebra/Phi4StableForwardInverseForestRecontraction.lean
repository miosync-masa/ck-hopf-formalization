import GaugeGeometry.QFT.HopfAlgebra.Phi4StableForwardInverseOuter

/-!
# QFT-R1-body-645a — stable RAW inverse recontraction (Steps 1–4 of the FOREST completion reconcile)

Body-644 proved the stable forward map's OUTER forest recovers `z.1.1` raw.  The FOREST completion
reconciliation (body-645) reconciles ONE FOREST component: the stable remnant of the recovered forward
occurrence, DECOMPLETED and RE-COMPLETED, equals the original star-touching target `δ.1` RE-COMPLETED — as
AMBIENT-FREE plain `ResolvedFeynmanGraph`s.  This is a 613-class INVERSE RECONTRACTION.

## VOLUME / SPLIT NOTE
The full headline is a 613-class inverse recontraction (τ existence engine + coordinate law + three RAW field
equalities against `stableLocalBoundaryCompletedGraph δ.1` + the Step-5 action agreement + the Step-6
`mapPerm`-congruence assembly through body-635's `stableRemnant_contractTwice`).  The OLD series spread this
across several bodies (610–613, 616, 620).  This file honestly delivers **645a = Steps 1–4** — the inverse
correcting permutation and the RAW inverse recontraction, ending at

`(stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I) = stableLocalBoundaryCompletedGraph δ.1`

— and STOPS.  The remaining **645b = Steps 5–6** (action agreement + HEADLINE assembly) is deferred to a
follow-up that will import this file.  The split is on genuine volume only: NO new hypothesis / axiom / `sorry`.

## Steps (this file)
* **Step 1** — `stableInvLocalContractGraph hSt I` (the inverse LOCAL contraction owner) + `defeq` anchor to
  body-635's `stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)` (rfl: `o.B.1` is body-642's
  stable inner forest, `o.γ.1` is the recovered parent).
* **Step 2** — `stableInvReconTau_exists` / `stableInvReconTau` / `_fix` / `_map`: the per-occurrence inverse
  correcting permutation (inner canonical stars → `z.1.1`-side final stars; survivors FIXED).  Mirrors body-635
  `stableRemnantTau_exists` and old body-613 `phi4WTriplePrime_inv_reconTau_exists` (proof SHAPE only).  NEVER
  asserts `stableInvReconTau = stableRemnantTau`.
* **Step 3** — `stableInvRecon_coord`: on the recovered-parent region, `τ ∘ (local retarget) = (global
  `z.1.1`-retarget)`.  Mirrors old body-613 `phi4WTriplePrime_inv_recon_coord`.
* **Step 4** — `stableInvRecontraction_internalEdges_eq` / `_vertices_eq` / `_externalLegs_eq` /
  `stableInvRecontraction_raw`: the RAW inverse recontraction against `stableLocalBoundaryCompletedGraph δ.1`.
  Internal edges from body-642's complement recovery; vertices from the survivor / promotion split; external
  legs in the STABLE normal form (`γ.externalLegs + γ.rbe.map γ.boundaryExternalLeg`) — EVEN via body-609's
  `_recoveredParent_externalLegs_transport`, ODD via `_inv_delta_resolvedBoundaryEdges`, both completion
  INDEPENDENT terms.  Inherited IDs / sectors VERBATIM.

## Ownership boundary — MUST NOT consume as terms
The OLD `phi4WTriplePrime_inv_reconTau` / `phi4WTriplePrime_inv_recontraction_raw` / the OLD inner forest
`phi4WTriplePrime_inv_recoveredInnerForest` / the 623 Equiv are NEVER consumed — only their proof SHAPE is
mirrored.  Body-642's stable inner forest / stable inner component / element-origin, body-635's clean star
algebra (`stableRemnant_gen_star_*` / `stableRemnant_retargetVertex_eq_star`), and the completion-INDEPENDENT
scaffolding (recovered parent geometry, touched-forest membership, `_inv_delta_*`, `_inv_star_not_mem_vertices`,
`_inv_retarget_mem_delta_iff`) are reused.

## HALT / red lines
NO cross-ambient subgraph `Eq` (`stableRemnantComponent o = δ.1` FORBIDDEN); NO global-τ equality / NO
`stableInvReconTau = stableRemnantTau`; NO round-trip / Equiv / `Sigma.ext` / `Finset.sum_bij` / alpha /
coassoc / `Bijective`.  The Step-5 action agreement and Step-6 headline are NOT entered here (645b).  ZERO new
`structure` / `class` / permanent `instance` (one file-local `local instance`; the τ-engine is a PRIVATE
Mathlib-only theorem reproduced clean, NOT a structure).  ZERO PUBLIC `HEq` / `cast` / graph-data transport
`▸` (all `▸` are Prop-membership rewrites).  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance instPhi4DivergenceMeasureFamily645 :
    (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — the correcting-permutation engine (Mathlib-only, reproduced clean) -/

/-- A finite partial vertex relabeling extends to a permutation of `VertexId`: fix `S`, send the finite
injective family `src` to the finite injective family `dst`, both disjoint from `S`.  Reproduced clean from
body-580 / body-635's `private` engine; uses only Mathlib primitives — no divergence class. -/
private theorem finite_visible_star_permutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Finset VertexId) (src dst : ι → VertexId)
    (hsrcInj : Function.Injective src)
    (hdstInj : Function.Injective dst)
    (hsrcS : ∀ i, src i ∉ S)
    (hdstS : ∀ i, dst i ∉ S) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ S → τ v = v) ∧
      ∀ i, τ (src i) = dst i := by
  classical
  let srcSet : Finset VertexId := Finset.univ.image src
  let dstSet : Finset VertexId := Finset.univ.image dst
  let support : Finset VertexId := S ∪ srcSet ∪ dstSet
  let p : {x // x ∈ support} → VertexId := fun x =>
    if h : ∃ i, src i = x.1 then dst h.choose else x.1
  let domain : Finset {x // x ∈ support} :=
    Finset.univ.filter (fun x : {x // x ∈ support} =>
      x.1 ∈ S ∨ ∃ i, src i = x.1)
  have hcard : Fintype.card {x // x ∈ support} = support.card :=
    Fintype.card_coe support
  have hp_subset : Finset.image p domain ⊆ support := by
    intro y hy
    rw [Finset.mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    dsimp [p]
    split
    · rename_i hsrc
      simp [support, dstSet]
    · exact x.2
  have hp_inj : Set.InjOn p (domain : Set {x // x ∈ support}) := by
    intro x hx y hy hxy
    have hx' : x.1 ∈ S ∨ ∃ i, src i = x.1 := by
      simpa [domain] using hx
    have hy' : y.1 ∈ S ∨ ∃ i, src i = y.1 := by
      simpa [domain] using hy
    rcases hx' with hxS | hxsrc
    · rcases hy' with hyS | hysrc
      · dsimp [p] at hxy
        have hxNotSrc : ¬ ∃ i, src i = x.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hxS)
        have hyNotSrc : ¬ ∃ i, src i = y.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hyS)
        simp [hxNotSrc, hyNotSrc] at hxy
        exact hxy
      · dsimp [p] at hxy
        have hxNotSrc : ¬ ∃ i, src i = x.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hxS)
        simp [hxNotSrc, hysrc] at hxy
        exact False.elim (hdstS hysrc.choose (hxy ▸ hxS))
    · rcases hy' with hyS | hysrc
      · dsimp [p] at hxy
        have hyNotSrc : ¬ ∃ i, src i = y.1 := by
          rintro ⟨i, hi⟩
          exact hsrcS i (hi ▸ hyS)
        simp [hxsrc, hyNotSrc] at hxy
        exact False.elim (hdstS hxsrc.choose (hxy.symm ▸ hyS))
      · dsimp [p] at hxy
        simp [hxsrc, hysrc] at hxy
        have hi : hxsrc.choose = hysrc.choose := hdstInj hxy
        have hxval : x.1 = y.1 := by
          rw [← hxsrc.choose_spec, ← hysrc.choose_spec, hi]
        exact Subtype.ext hxval
  obtain ⟨σ, hσ⟩ :=
    Finset.exists_equiv_extend_of_card_eq hcard hp_subset hp_inj
  let τ : Equiv.Perm VertexId :=
    Equiv.Perm.extendDomain σ (Finset.equivToSet support)
  refine ⟨τ, ?_, ?_⟩
  · intro v hvS
    have hvSupport : v ∈ support := by
      simp [support, hvS]
    have hvDomain : (⟨v, hvSupport⟩ : {x // x ∈ support}) ∈ domain := by
      dsimp [domain]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inl hvS⟩
    have hpv : p ⟨v, hvSupport⟩ = v := by
      dsimp [p]
      have hvNotSrc : ¬ ∃ i, src i = v := by
        rintro ⟨i, hi⟩
        exact hsrcS i (hi ▸ hvS)
      simp [hvNotSrc]
    have hσv : (σ ⟨v, hvSupport⟩ : VertexId) = v := by
      simpa [hpv] using hσ ⟨v, hvSupport⟩ hvDomain
    have hτ :
        τ ((Finset.equivToSet support) ⟨v, hvSupport⟩) =
          (Finset.equivToSet support) (σ ⟨v, hvSupport⟩) :=
      Equiv.Perm.extendDomain_apply_image σ
        (Finset.equivToSet support) ⟨v, hvSupport⟩
    change τ v = (σ ⟨v, hvSupport⟩ : VertexId) at hτ
    exact hτ.trans hσv
  · intro i
    have hsrcSupport : src i ∈ support := by
      simp [support, srcSet]
    have hsrcDomain :
        (⟨src i, hsrcSupport⟩ : {x // x ∈ support}) ∈ domain := by
      dsimp [domain]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Or.inr ⟨i, rfl⟩⟩
    have hp_src : p ⟨src i, hsrcSupport⟩ = dst i := by
      dsimp [p]
      split
      · rename_i h
        have hi : h.choose = i := hsrcInj h.choose_spec
        exact congrArg dst hi
      · rename_i h
        exact False.elim (h ⟨i, rfl⟩)
    have hσsrc : (σ ⟨src i, hsrcSupport⟩ : VertexId) = dst i := by
      simpa [hp_src] using hσ ⟨src i, hsrcSupport⟩ hsrcDomain
    have hτ :
        τ ((Finset.equivToSet support) ⟨src i, hsrcSupport⟩) =
          (Finset.equivToSet support) (σ ⟨src i, hsrcSupport⟩) :=
      Equiv.Perm.extendDomain_apply_image σ
        (Finset.equivToSet support) ⟨src i, hsrcSupport⟩
    change τ (src i) = (σ ⟨src i, hsrcSupport⟩ : VertexId) at hτ
    exact hτ.trans hσsrc

/-! ## Step 1 — the inverse LOCAL contraction owner -/

/-- **body-645a (Step 1) — the inverse LOCAL star-contraction owner.**  The star-contraction of body-642's
stable inner forest `stableInvRecoveredInnerForest hSt I` on the STABLE inner ambient
`stableLocalBoundaryCompletedGraph (recoveredParent I)`.  DEFEQ to body-635's
`stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)` (see the anchor). -/
noncomputable def stableInvLocalContractGraph (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) : ResolvedFeynmanGraph :=
  (stableInvRecoveredInnerForest hSt I).contractWithStars
    (phi4WTriplePrimeCanonicalSupply.starOf
      (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
      (stableInvRecoveredInnerForest hSt I))

/-- **body-645a (Step 1, DEFEQ ANCHOR) — the inverse LOCAL contraction owner IS body-635's LOCAL contract
graph of the stable recovered forward occurrence.**  `rfl`: `o.B = stableInvRecoveredInnerForestValue hSt I`
(body-644 Step 3) and `o.γ.1 = recoveredParent I`. -/
theorem stableInvLocalContractGraph_eq_stableLocalContractGraph (hSt : StableResolvedBoundaryIds G)
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hδ : phi4WTriplePrime_inv_isForestImage z δ) :
    stableLocalContractGraph (stableRecoveredForwardOccurrence hSt z hδ)
      = stableInvLocalContractGraph hSt
          (phi4WTriplePrime_forestDecontractionInput_of_starTouching z hδ) :=
  rfl

/-! ## Step 2 — the per-occurrence inverse correcting permutation `τ` -/

/-- A transported touched component lands in the stable inner forest's elements. -/
private theorem stableInvInnerComponent_mem (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    stableInvInnerComponent hSt I γ hγ
      ∈ (stableInvRecoveredInnerForest hSt I).elements := by
  rw [stableInvRecoveredInnerForest_elements]
  exact Finset.mem_image.mpr ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, rfl⟩

/-- `stableInvInnerComponent hSt I` is injective on the touched outer forest's components (equal transported
components share a vertex set; distinct touched components are pairwise vertex-disjoint + vertex-nonempty). -/
private theorem stableInvInnerComponent_injOn (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ₁ : ResolvedFeynmanSubgraph G} (h₁ : γ₁ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements)
    {γ₂ : ResolvedFeynmanSubgraph G} (h₂ : γ₂ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements)
    (heq : stableInvInnerComponent hSt I γ₁ h₁ = stableInvInnerComponent hSt I γ₂ h₂) : γ₁ = γ₂ := by
  by_contra hne
  have hv : γ₁.vertices = γ₂.vertices := by
    have hcv := congrArg ResolvedFeynmanSubgraph.vertices heq
    simpa only [stableInvInnerComponent_vertices] using hcv
  have hNE : z.1.1.HasNonemptyComponents :=
    (((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1).2.1
  have hγ₁A : γ₁ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A h₁
  have hγ₂A : γ₂ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A h₂
  have hdisj : _root_.Disjoint γ₁.vertices γ₂.vertices :=
    z.1.1.pairwiseDisjoint hγ₁A hγ₂A hne
  obtain ⟨v, hv1⟩ := Finset.card_pos.mp (hNE γ₁ hγ₁A)
  exact Finset.disjoint_left.mp hdisj hv1 (hv ▸ hv1)

/-- **body-645a (Step 2) — the inverse correcting-permutation existence.**  Fix the recovered-parent survivors,
send each stable inner star `starOf H (stableInvInnerComponent … γ)` to `δ`'s final quotient star `starA γ`.
Freshness / injectivity from body-635's clean star algebra + body-608's fresh-star engine.  Per-occurrence. -/
theorem stableInvReconTau_exists (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
          \ (stableInvRecoveredInnerForest hSt I).vertices → τ v = v) ∧
      (∀ i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements},
        τ (phi4WTriplePrimeCanonicalSupply.starOf
              (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
              (stableInvRecoveredInnerForest hSt I)
              (stableInvInnerComponent hSt I i.1 i.2))
          = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1) := by
  have hpfF := stableInvRecoveredInnerForest_isProperForest hSt I
  have hApf := phi4WTriplePrime_inv_recon_A_isProperForest I
  refine finite_visible_star_permutation
    (ι := {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements})
    ((phi4WTriplePrime_inv_recoveredParent I).vertices
      \ (stableInvRecoveredInnerForest hSt I).vertices)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
        (stableInvRecoveredInnerForest hSt I)
        (stableInvInnerComponent hSt I i.1 i.2))
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1)
    ?_ ?_ ?_ ?_
  · -- hsrcInj
    intro i j hij
    have hcomp := stableRemnant_gen_star_injOn (stableInvRecoveredInnerForest hSt I) hpfF
      (stableInvInnerComponent_mem hSt I i.2) (stableInvInnerComponent_mem hSt I j.2) hij
    exact Subtype.ext (stableInvInnerComponent_injOn hSt I i.2 j.2 hcomp)
  · -- hdstInj
    intro i j hij
    exact Subtype.ext (stableRemnant_gen_star_injOn z.1.1 hApf
      (phi4WTriplePrime_inv_touchedForest_subset_A i.2)
      (phi4WTriplePrime_inv_touchedForest_subset_A j.2) hij)
  · -- hsrcS
    intro i hc
    exact stableRemnant_gen_star_not_mem (stableInvRecoveredInnerForest hSt I) hpfF
      (stableInvInnerComponent_mem hSt I i.2) (Finset.mem_sdiff.mp hc).1
  · -- hdstS
    intro i hc
    exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf
      (phi4WTriplePrime_inv_touchedForest_subset_A i.2)
      ((phi4WTriplePrime_inv_recoveredParent I).vertices_subset (Finset.mem_sdiff.mp hc).1)

/-- The per-occurrence inverse correcting permutation `τ`. -/
noncomputable def stableInvReconTau (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) : Equiv.Perm VertexId :=
  (stableInvReconTau_exists hSt I).choose

theorem stableInvReconTau_fix (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {v : VertexId}
    (hv : v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
        \ (stableInvRecoveredInnerForest hSt I).vertices) :
    stableInvReconTau hSt I v = v :=
  (stableInvReconTau_exists hSt I).choose_spec.1 v hv

theorem stableInvReconTau_map (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements}) :
    stableInvReconTau hSt I
        (phi4WTriplePrimeCanonicalSupply.starOf
          (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
          (stableInvRecoveredInnerForest hSt I)
          (stableInvInnerComponent hSt I i.1 i.2))
      = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1 :=
  (stableInvReconTau_exists hSt I).choose_spec.2 i

/-! ## Step 2b — the stable inner-forest vertex set + the survivor correspondence -/

/-- The stable recovered inner forest's vertex set is the touched outer forest's. -/
private theorem stableInvRecoveredInnerForest_vertices_char (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvRecoveredInnerForest hSt I).vertices
      = (phi4WTriplePrime_touchedOuterForest z δ).vertices := by
  ext v
  rw [ResolvedAdmissibleSubgraph.mem_vertices, ResolvedAdmissibleSubgraph.mem_vertices]
  constructor
  · rintro ⟨δ', hδ', hvδ'⟩
    obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
    exact ⟨γ, hγ, by rw [stableInvInnerComponent_vertices] at hvδ'; exact hvδ'⟩
  · rintro ⟨γ, hγ, hvγ⟩
    exact ⟨stableInvInnerComponent hSt I γ hγ, stableInvInnerComponent_mem hSt I hγ,
      by rw [stableInvInnerComponent_vertices]; exact hvγ⟩

/-- **body-645a (Step 2b) — the survivor correspondence.**  A recovered-parent vertex outside the stable inner
forest is exactly a `δ`-vertex outside the `A`-star carrier.  Mirrors old body-613 `_inv_recon_survivor_iff`,
using the stable inner forest's vertex characterization. -/
private theorem stableInvRecon_survivor_iff (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (v : VertexId) :
    (v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
        ∧ v ∉ (stableInvRecoveredInnerForest hSt I).vertices)
      ↔ (v ∈ δ.1.vertices
          ∧ v ∉ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  have hFv := stableInvRecoveredInnerForest_vertices_char hSt I
  constructor
  · rintro ⟨hvP, hvF⟩
    rw [phi4WTriplePrime_inv_recoveredParent_vertices,
      phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union] at hvP
    rw [hFv] at hvF
    rcases hvP with hd | ht
    · exact ⟨(Finset.mem_sdiff.mp hd).1, (Finset.mem_sdiff.mp hd).2⟩
    · exact absurd ht hvF
  · rintro ⟨hvδ, hvstar⟩
    have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
      δ.1.vertices_subset hvδ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
    have hvnA : v ∉ z.1.1.vertices := by
      rcases hvQ with h | h
      · exact (Finset.mem_sdiff.mp h).2
      · exact absurd h hvstar
    refine ⟨?_, ?_⟩
    · rw [phi4WTriplePrime_inv_recoveredParent_vertices,
        phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
      exact Or.inl (Finset.mem_sdiff.mpr ⟨hvδ, hvstar⟩)
    · rw [hFv]
      intro hc
      exact hvnA (by
        obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hc
        exact ResolvedAdmissibleSubgraph.mem_vertices.mpr
          ⟨γ, phi4WTriplePrime_inv_touchedForest_subset_A hγ, hvγ⟩)

/-! ## Step 3 — the coordinate lemma (τ ∘ local retarget = global retarget on the parent region) -/

/-- **body-645a (Step 3) — the coordinate lemma.**  On the recovered-parent region, `τ` composed with the
LOCAL inverse-recontraction retarget equals the GLOBAL `z.1.1`-retarget.  Mirrors old body-613
`phi4WTriplePrime_inv_recon_coord`. -/
theorem stableInvRecon_coord (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {v : VertexId}
    (hvP : v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices) :
    stableInvReconTau hSt I
        ((stableInvRecoveredInnerForest hSt I).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf
            (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
            (stableInvRecoveredInnerForest hSt I)) v)
      = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v := by
  by_cases hvF : v ∈ (stableInvRecoveredInnerForest hSt I).vertices
  · obtain ⟨δ₀, hδ₀, hvδ₀⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvF
    obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ₀
    rw [stableRemnant_retargetVertex_eq_star (stableInvRecoveredInnerForest hSt I) _ hδ₀ hvδ₀,
      stableInvReconTau_map hSt I ⟨γ, hγ⟩,
      stableRemnant_retargetVertex_eq_star z.1.1 _
        (phi4WTriplePrime_inv_touchedForest_subset_A hγ) hvδ₀]
  · rw [(stableInvRecoveredInnerForest hSt I).retargetVertex_of_not_mem _ hvF,
      stableInvReconTau_fix hSt I (Finset.mem_sdiff.mpr ⟨hvP, hvF⟩)]
    obtain ⟨hvδ, hvstar⟩ := (stableInvRecon_survivor_iff hSt I v).mp ⟨hvP, hvF⟩
    have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
      δ.1.vertices_subset hvδ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
    have hvnA : v ∉ z.1.1.vertices := by
      rcases hvQ with h | h
      · exact (Finset.mem_sdiff.mp h).2
      · exact absurd h hvstar
    rw [z.1.1.retargetVertex_of_not_mem _ hvnA]

/-! ## Step 4 — the RAW inverse recontraction field equalities -/

/-- **body-645a (Step 4, internalEdges) — the inverse recontraction internal edges (under `τ`) equal `δ`'s
completed internal edges.** -/
theorem stableInvRecontraction_internalEdges_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ((stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I)).internalEdges
      = (stableLocalBoundaryCompletedGraph δ.1).internalEdges := by
  rw [stableLocalBoundaryCompletedGraph_internalEdges]
  show ((stableInvRecoveredInnerForest hSt I).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
        (stableInvRecoveredInnerForest hSt I))).internalEdges.map
        (ResolvedFeynmanEdge.map (stableInvReconTau hSt I))
    = δ.1.internalEdges
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.map_map,
    stableInvRecoveredInnerForest_complementEdges_eq hSt I,
    phi4WTriplePrime_inv_delta_internalEdges_eq I]
  apply Multiset.map_congr rfl
  intro e he
  simp only [phi4WTriplePrime_inv_parentExactEdges, Multiset.mem_filter] at he
  have hcs := stableInvRecon_coord hSt I
    (show e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices from he.2.1)
  have hct := stableInvRecon_coord hSt I
    (show e.target ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices from he.2.2)
  simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
    ResolvedFeynmanEdge.map]
  rw [hcs, hct]

/-- **body-645a (Step 4, vertices) — the inverse recontraction vertices (under `τ`) equal `δ`'s.** -/
theorem stableInvRecontraction_vertices_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ((stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I)).vertices
      = (stableLocalBoundaryCompletedGraph δ.1).vertices := by
  rw [stableLocalBoundaryCompletedGraph_vertices]
  show ((stableInvRecoveredInnerForest hSt I).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
        (stableInvRecoveredInnerForest hSt I))).vertices.image (stableInvReconTau hSt I)
    = δ.1.vertices
  ext w
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
    rcases hx with hsurv | hstar
    · rw [stableLocalBoundaryCompletedGraph_vertices, Finset.mem_sdiff] at hsurv
      rw [stableInvReconTau_fix hSt I (Finset.mem_sdiff.mpr hsurv)]
      exact ((stableInvRecon_survivor_iff hSt I x).mp hsurv).1
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨δ', hδ', rfl⟩ := hstar
      obtain ⟨γ, hγ, rfl⟩ := stableInvRecoveredInnerForest_element_origin hSt I hδ'
      rw [stableInvReconTau_map hSt I ⟨γ, hγ⟩]
      exact phi4WTriplePrime_inv_touched_starA_mem hγ
  · intro hwδ
    have hwQ : w ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
      δ.1.vertices_subset hwδ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hwQ
    rcases hwQ with hsurv | hstar
    · have hwnstar : w ∉ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) := by
        intro hc
        obtain ⟨γ, hγ, hγeq⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hc
        exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1
          (phi4WTriplePrime_inv_recon_A_isProperForest I) hγ
          (by rw [hγeq]; exact (Finset.mem_sdiff.mp hsurv).1)
      have hxP := (stableInvRecon_survivor_iff hSt I w).mpr ⟨hwδ, hwnstar⟩
      refine ⟨w, ?_, ?_⟩
      · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        exact Or.inl (Finset.mem_sdiff.mpr
          ⟨by rw [stableLocalBoundaryCompletedGraph_vertices]; exact hxP.1, hxP.2⟩)
      · exact stableInvReconTau_fix hSt I (Finset.mem_sdiff.mpr ⟨hxP.1, hxP.2⟩)
    · obtain ⟨γ, hγA, rfl⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
      have hγTOF := phi4WTriplePrime_inv_touched_of_starA_mem hγA hwδ
      refine ⟨phi4WTriplePrimeCanonicalSupply.starOf
          (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
          (stableInvRecoveredInnerForest hSt I)
          (stableInvInnerComponent hSt I γ hγTOF), ?_, ?_⟩
      · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
          ⟨stableInvInnerComponent hSt I γ hγTOF, stableInvInnerComponent_mem hSt I hγTOF, rfl⟩)
      · exact stableInvReconTau_map hSt I ⟨γ, hγTOF⟩

/-- **body-645a (Step 4, externalLegs) — the inverse recontraction external legs (under `τ`) equal `δ`'s
completed external legs, in the STABLE normal form.**  EVEN via body-609's recovered-parent leg transport;
ODD via `_inv_delta_resolvedBoundaryEdges` + the inside-endpoint agreement.  Multiplicity / id / sector
exact. -/
theorem stableInvRecontraction_externalLegs_eq (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ((stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I)).externalLegs
      = (stableLocalBoundaryCompletedGraph δ.1).externalLegs := by
  show ((stableInvRecoveredInnerForest hSt I).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
        (stableInvRecoveredInnerForest hSt I))).externalLegs.map
        (ResolvedExternalLeg.map (stableInvReconTau hSt I))
    = (stableLocalBoundaryCompletedGraph δ.1).externalLegs
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map,
    stableLocalBoundaryCompletedGraph_externalLegs,
    stableLocalBoundaryCompletedGraph_externalLegs, Multiset.map_add]
  congr 1
  · -- EVEN
    rw [phi4WTriplePrime_inv_recoveredParent_externalLegs_transport I]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hatt : ℓ.attachedTo ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices :=
      (phi4WTriplePrime_inv_recoveredParent I).legs_supported ℓ hℓ
    have hc := stableInvRecon_coord hSt I hatt
    simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetExternalLeg,
      ResolvedExternalLeg.retarget, ResolvedExternalLeg.map]
    rw [hc]
  · -- ODD
    rw [phi4WTriplePrime_inv_delta_resolvedBoundaryEdges I, Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro e he
    have he_mem := (ResolvedFeynmanSubgraph.resolvedBoundaryEdges_mem).mp he
    have hesupp := I.rootAmbientSupported.1 e he_mem.1
    have hinside : (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e
        ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices :=
      (phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint_mem e he_mem.2
    have hcoord := stableInvRecon_coord hSt I hinside
    have hend : δ.1.resolvedInsideEndpoint
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e)
        = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)
            ((phi4WTriplePrime_inv_recoveredParent I).resolvedInsideEndpoint e) := by
      show (if (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source ∈ δ.1.vertices
            then (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source
            else (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).target)
        = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)
            (if e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices then e.source else e.target)
      simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
        ResolvedFeynmanEdge.retarget_target]
      by_cases hsP : e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
      · rw [if_pos hsP, if_pos ((phi4WTriplePrime_inv_retarget_mem_delta_iff I hesupp.1).mpr hsP)]
      · rw [if_neg hsP, if_neg (fun hc => hsP ((phi4WTriplePrime_inv_retarget_mem_delta_iff I hesupp.1).mp hc))]
    show ResolvedExternalLeg.map (stableInvReconTau hSt I)
        ((stableInvRecoveredInnerForest hSt I).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf
            (stableLocalBoundaryCompletedGraph (phi4WTriplePrime_inv_recoveredParent I))
            (stableInvRecoveredInnerForest hSt I))
          ((phi4WTriplePrime_inv_recoveredParent I).boundaryExternalLeg e))
      = δ.1.boundaryExternalLeg (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e)
    unfold ResolvedFeynmanSubgraph.boundaryExternalLeg ResolvedAdmissibleSubgraph.retargetExternalLeg
      ResolvedExternalLeg.retarget ResolvedExternalLeg.map
    rw [hend, hcoord]
    simp only [ResolvedFeynmanSubgraph.boundaryLegId, ResolvedAdmissibleSubgraph.retargetEdge,
      ResolvedFeynmanEdge.retarget]

/-- **body-645a (Step 4, HEADLINE) — the RAW inverse recontraction.**  Under the inverse correcting
permutation `τ`, the inverse LOCAL contraction of the stable inner forest reconstructs `δ`'s STABLE
boundary-completion — a RAW `ResolvedFeynmanGraph` equality on all three fields (exact IDs / sectors /
multiplicities; inherited legs VERBATIM).  This is the STABLE mirror of old body-613
`phi4WTriplePrime_inv_recontraction_raw`, against the STABLE completion `stableLocalBoundaryCompletedGraph`
instead of `boundaryCompletedResolvedGraph`. -/
theorem stableInvRecontraction_raw (hSt : StableResolvedBoundaryIds G)
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (stableInvLocalContractGraph hSt I).mapPerm (stableInvReconTau hSt I)
      = stableLocalBoundaryCompletedGraph δ.1 := by
  have hgen : ∀ (a b : ResolvedFeynmanGraph), a.vertices = b.vertices → a.internalEdges = b.internalEdges →
      a.externalLegs = b.externalLegs → a = b := by
    intro a b h1 h2 h3
    cases a; cases b
    simp only [ResolvedFeynmanGraph.mk.injEq]
    exact ⟨h1, h2, h3⟩
  exact hgen _ _ (stableInvRecontraction_vertices_eq hSt I)
    (stableInvRecontraction_internalEdges_eq hSt I)
    (stableInvRecontraction_externalLegs_eq hSt I)

end GaugeGeometry.QFT.Combinatorial
