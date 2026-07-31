import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredInnerComplement

/-!
# QFT-R1-body-613 — recovered recontraction recovery (inverse contract-twice raw equality)

This body DISCHARGES the last body-609 proof frontier `phi4WTriplePrime_inv_recontraction_recovery` (with the
CORRECTED target `δ.1.boundaryCompletedResolvedGraph`, edited into body-609): recontracting the recovered inner
forest `F` inside the recovered parent's boundary-completed ambient `Pbc` returns `δ`'s boundary-completion, at
the resolved class level.  It is the exact INVERSE of body-604's forward contract-twice raw equality
`remnant.boundaryCompletion = localContraction.mapPerm τ`.

## Strategy (mirror of body-604 in reverse)

Let `A := z.1.1`, `P := recoveredParent I`, `Pbc := P.boundaryCompletedResolvedGraph`,
`F := recoveredInnerForest I (innerForest_CD_proof I)`, `L := F.contractWithStars starL` (the recontraction),
`τ := reconTau I` the correcting permutation.  We prove the RAW graph equality `L.mapPerm τ = δ.bcrg` on all
three fields (vertices / internalEdges / externalLegs EVEN+ODD, exact ids/sectors/multiplicity) and descend to
`toResolvedClass` via `toResolvedClass_mapPerm`.

* `τ` fixes the survivors `P.vertices \ F.vertices` and sends each recontraction star `starL (innerComponent γ)`
  to `δ`'s quotient star `starA γ` (body-580 `finite_visible_star_permutation`, reproduced clean; freshness /
  injectivity from body-604's public `gen_star_*`).  NO strict cross-presentation star equality.
* internalEdges: `F.complementEdges = parentExactEdges` (612), `δ.internalEdges = parentExactEdges.map (A.retargetEdge starA)` (610); connected by the coordinate law under `τ`.
* vertices: membership round-trip via the body-609 KEY IFF `retarget_mem_delta_iff`.
* EVEN/ODD legs: the body-609 leg transport + a fresh `δ.rbe = P.rbe.map (A.retargetEdge starA)`, mirroring
  body-604's `_even_eq` / `_odd_eq` (multiplicity-exact, no card shortcut).

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; no strict `starOf … = starOf …`; no `δ.boundaryEdgeCount = 0` hypothesis; no raw-`δ` target;
no parent topology/CD/complement re-proof (READ from 609–612); no `s` / `componentEquiv`; no
`RecoveredForestOccurrence` owner / global split / whole-Equiv / summand / alpha / coassoc; no new `class` /
`structure` / permanent `instance`; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst613 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 0 — the correcting-permutation engine (Mathlib-only, reproduced clean) -/

/-- A finite partial vertex relabeling extends to a permutation of `VertexId`: fix `S`, send the finite
injective family `src` to the finite injective family `dst`, both disjoint from `S`.  Reproduced clean from
body-580 / body-604's `private` engine; uses only Mathlib primitives — no divergence class. -/
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

/-! ## Step 1 — recovered-forest leaf facts. -/

/-- The recovered parent `A := z.1.1` is a proper forest (its W‴ membership). -/
theorem phi4WTriplePrime_inv_recon_A_isProperForest
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    z.1.1.IsProperForest :=
  ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1

/-- The recovered inner forest `F` is a proper forest (its unconditional W‴ membership, body-612). -/
theorem phi4WTriplePrime_inv_recon_F_isProperForest
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily
      (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
      (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)) :=
  ((mem_phi4WTriplePrimeIndex _ _).mp (phi4WTriplePrime_inv_recoveredInnerForest_mem_proof I)).2.2.2.2.1

/-- Each transported inner component is an element of the recovered inner forest. -/
theorem phi4WTriplePrime_inv_innerComponent_mem_F
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    phi4WTriplePrime_inv_innerComponent I γ hγ
      ∈ (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).elements := by
  rw [phi4WTriplePrime_inv_recoveredInnerForest_elements]
  exact Finset.mem_image.mpr ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, rfl⟩

/-- The recovered inner forest's vertex set equals the touched outer forest's (each transported component keeps
its outer component's vertices). -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_vertices_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices
      = (phi4WTriplePrime_touchedOuterForest z δ).vertices := by
  ext v
  rw [ResolvedAdmissibleSubgraph.mem_vertices, ResolvedAdmissibleSubgraph.mem_vertices]
  constructor
  · rintro ⟨δ', hδ', hv⟩
    obtain ⟨γ, hγ, rfl⟩ :=
      phi4WTriplePrime_inv_recoveredInnerForest_element_origin I
        (phi4WTriplePrime_inv_innerForest_CD_proof I) hδ'
    exact ⟨γ, hγ, hv⟩
  · rintro ⟨γ, hγ, hv⟩
    exact ⟨phi4WTriplePrime_inv_innerComponent I γ hγ,
      phi4WTriplePrime_inv_innerComponent_mem_F I γ hγ, hv⟩

/-- A touched outer component's canonical `A`-star lands in `δ` (the touched definition). -/
theorem phi4WTriplePrime_inv_touched_starA_mem
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices := by
  rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter] at hγ
  exact hγ.2

/-- Conversely, an `A`-component whose canonical star lands in `δ` is touched. -/
theorem phi4WTriplePrime_inv_touched_of_starA_mem
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    {γ : ResolvedFeynmanSubgraph G} (hγA : γ ∈ z.1.1.elements)
    (h : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices) :
    γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
  rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]
  exact ⟨hγA, h⟩

/-- **body-613 — the survivor correspondence.**  A parent-region vertex outside the recovered inner forest is
exactly a `δ`-vertex outside the `A`-star carrier (a genuine survivor). -/
theorem phi4WTriplePrime_inv_recon_survivor_iff
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (v : VertexId) :
    (v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
        ∧ v ∉ (phi4WTriplePrime_inv_recoveredInnerForest I
                (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices)
      ↔ (v ∈ δ.1.vertices
          ∧ v ∉ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  have hFv := phi4WTriplePrime_inv_recoveredInnerForest_vertices_eq I
  have hTOFsubA : (phi4WTriplePrime_touchedOuterForest z δ).vertices ⊆ z.1.1.vertices := by
    intro w hw
    obtain ⟨γ, hγ, hwγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hw
    exact ResolvedAdmissibleSubgraph.mem_vertices.mpr
      ⟨γ, phi4WTriplePrime_inv_touchedForest_subset_A hγ, hwγ⟩
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
    · rw [hFv]; intro hc; exact hvnA (hTOFsubA hc)

/-! ## Step 2 — the correcting permutation `τ`. -/

/-- The correcting-permutation existence for the recontraction: fix the parent-region survivors, send each
recontraction star `starL (innerComponent γ)` to `δ`'s quotient star `starA γ`.  Freshness / injectivity from
body-604's public `gen_star_*`; STRICT star equality FORBIDDEN — `τ` absorbs the local↔δ star shift. -/
theorem phi4WTriplePrime_inv_reconTau_exists
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ∃ τ : Equiv.Perm VertexId,
      (∀ v, v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
          \ (phi4WTriplePrime_inv_recoveredInnerForest I
              (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices → τ v = v) ∧
      (∀ i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements},
        τ (phi4WTriplePrimeCanonicalSupply.starOf
              (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
              (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
              (phi4WTriplePrime_inv_innerComponent I i.1 i.2))
          = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1) := by
  have hApf := phi4WTriplePrime_inv_recon_A_isProperForest I
  have hpfF := phi4WTriplePrime_inv_recon_F_isProperForest I
  refine finite_visible_star_permutation
    (ι := {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements})
    ((phi4WTriplePrime_inv_recoveredParent I).vertices
      \ (phi4WTriplePrime_inv_recoveredInnerForest I
          (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices)
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
        (phi4WTriplePrime_inv_innerComponent I i.1 i.2))
    (fun i => phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1)
    ?_ ?_ ?_ ?_
  · -- hsrcInj
    intro i j hij
    have h1 : phi4WTriplePrime_inv_innerComponent I i.1 i.2 = phi4WTriplePrime_inv_innerComponent I j.1 j.2 :=
      phi4WTriplePrime_gen_star_injOn
        (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
        hpfF (phi4WTriplePrime_inv_innerComponent_mem_F I i.1 i.2)
        (phi4WTriplePrime_inv_innerComponent_mem_F I j.1 j.2) hij
    apply Subtype.ext
    by_contra hne
    have hv : i.1.vertices = j.1.vertices := by
      have hcv := congrArg ResolvedFeynmanSubgraph.vertices h1
      simpa only [phi4WTriplePrime_inv_innerComponent_vertices] using hcv
    have hiA := phi4WTriplePrime_inv_touchedForest_subset_A i.2
    have hjA := phi4WTriplePrime_inv_touchedForest_subset_A j.2
    have hdisj : _root_.Disjoint i.1.vertices j.1.vertices :=
      z.1.1.pairwiseDisjoint hiA hjA hne
    have hNE : z.1.1.HasNonemptyComponents := hApf.2.1
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (hNE i.1 hiA)
    exact Finset.disjoint_left.mp hdisj hw (hv ▸ hw)
  · -- hdstInj
    intro i j hij
    exact Subtype.ext (phi4WTriplePrime_gen_star_injOn z.1.1 hApf
      (phi4WTriplePrime_inv_touchedForest_subset_A i.2)
      (phi4WTriplePrime_inv_touchedForest_subset_A j.2) hij)
  · -- hsrcS : recontraction star is fresh outside Pbc ⊇ survivors
    intro i hc
    exact phi4WTriplePrime_gen_star_not_mem
      (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
      hpfF (phi4WTriplePrime_inv_innerComponent_mem_F I i.1 i.2)
      (by rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]
          exact (Finset.mem_sdiff.mp hc).1)
  · -- hdstS : δ-star is fresh outside G ⊇ survivors
    intro i hc
    exact phi4WTriplePrime_inv_star_not_mem_vertices z.1.1 hApf
      (phi4WTriplePrime_inv_touchedForest_subset_A i.2)
      ((phi4WTriplePrime_inv_recoveredParent I).vertices_subset (Finset.mem_sdiff.mp hc).1)

/-- The correcting permutation `τ` for the recontraction. -/
noncomputable def phi4WTriplePrime_inv_reconTau
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) : Equiv.Perm VertexId :=
  (phi4WTriplePrime_inv_reconTau_exists I).choose

theorem phi4WTriplePrime_inv_reconTau_fix
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {v : VertexId}
    (hv : v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
        \ (phi4WTriplePrime_inv_recoveredInnerForest I
            (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices) :
    phi4WTriplePrime_inv_reconTau I v = v :=
  (phi4WTriplePrime_inv_reconTau_exists I).choose_spec.1 v hv

theorem phi4WTriplePrime_inv_reconTau_map
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (i : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements}) :
    phi4WTriplePrime_inv_reconTau I
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
          (phi4WTriplePrime_inv_innerComponent I i.1 i.2))
      = phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 i.1 :=
  (phi4WTriplePrime_inv_reconTau_exists I).choose_spec.2 i

/-! ## Step 3 — the coordinate lemma (τ ∘ local retarget = global retarget on the parent region). -/

/-- **body-613 — the coordinate lemma.**  On the recovered-parent region, `τ` composed with the LOCAL
recontraction retarget equals the GLOBAL `A`-retarget. -/
theorem phi4WTriplePrime_inv_recon_coord
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {v : VertexId}
    (hvP : v ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices) :
    phi4WTriplePrime_inv_reconTau I
        ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).retargetVertex
          (phi4WTriplePrimeCanonicalSupply.starOf
            (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
            (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))) v)
      = z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v := by
  by_cases hvF : v ∈ (phi4WTriplePrime_inv_recoveredInnerForest I
      (phi4WTriplePrime_inv_innerForest_CD_proof I)).vertices
  · obtain ⟨δ₀, hδ₀, hvδ₀⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvF
    obtain ⟨γ, hγ, rfl⟩ :=
      phi4WTriplePrime_inv_recoveredInnerForest_element_origin I
        (phi4WTriplePrime_inv_innerForest_CD_proof I) hδ₀
    rw [phi4WTriplePrime_retargetVertex_eq_star
        (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
        _ hδ₀ hvδ₀,
      phi4WTriplePrime_inv_reconTau_map I ⟨γ, hγ⟩,
      phi4WTriplePrime_retargetVertex_eq_star z.1.1 _
        (phi4WTriplePrime_inv_touchedForest_subset_A hγ) hvδ₀]
  · rw [(phi4WTriplePrime_inv_recoveredInnerForest I
        (phi4WTriplePrime_inv_innerForest_CD_proof I)).retargetVertex_of_not_mem _ hvF,
      phi4WTriplePrime_inv_reconTau_fix I (Finset.mem_sdiff.mpr ⟨hvP, hvF⟩)]
    obtain ⟨hvδ, hvstar⟩ := (phi4WTriplePrime_inv_recon_survivor_iff I v).mp ⟨hvP, hvF⟩
    have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
      δ.1.vertices_subset hvδ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
    have hvnA : v ∉ z.1.1.vertices := by
      rcases hvQ with h | h
      · exact (Finset.mem_sdiff.mp h).2
      · exact absurd h hvstar
    rw [z.1.1.retargetVertex_of_not_mem _ hvnA]

/-! ## Step 4 — internal-edge raw equality (under τ). -/

/-- **body-613 (Step 4, internalEdges) — the recontraction internal edges (under `τ`) equal `δ`'s.** -/
theorem phi4WTriplePrime_inv_recontraction_internalEdges_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)))).mapPerm
        (phi4WTriplePrime_inv_reconTau I)).internalEdges
      = δ.1.boundaryCompletedResolvedGraph.internalEdges := by
  rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges]
  show ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest I
          (phi4WTriplePrime_inv_innerForest_CD_proof I)))).internalEdges.map
        (ResolvedFeynmanEdge.map (phi4WTriplePrime_inv_reconTau I))
    = δ.1.internalEdges
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.map_map,
    phi4WTriplePrime_inv_recoveredInnerForest_complementEdges_eq I,
    phi4WTriplePrime_inv_delta_internalEdges_eq I]
  apply Multiset.map_congr rfl
  intro e he
  simp only [phi4WTriplePrime_inv_parentExactEdges, Multiset.mem_filter] at he
  have hcs := phi4WTriplePrime_inv_recon_coord I
    (show e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices from he.2.1)
  have hct := phi4WTriplePrime_inv_recon_coord I
    (show e.target ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices from he.2.2)
  simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
    ResolvedFeynmanEdge.map]
  rw [hcs, hct]

/-! ## Step 5 — vertex raw equality (under τ). -/

/-- **body-613 (Step 5, vertices) — the recontraction vertices (under `τ`) equal `δ`'s.** -/
theorem phi4WTriplePrime_inv_recontraction_vertices_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)))).mapPerm
        (phi4WTriplePrime_inv_reconTau I)).vertices
      = δ.1.boundaryCompletedResolvedGraph.vertices := by
  rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]
  show ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest I
          (phi4WTriplePrime_inv_innerForest_CD_proof I)))).vertices.image
        (phi4WTriplePrime_inv_reconTau I)
    = δ.1.vertices
  ext w
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hx
    rcases hx with hsurv | hstar
    · rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices, Finset.mem_sdiff] at hsurv
      rw [phi4WTriplePrime_inv_reconTau_fix I (Finset.mem_sdiff.mpr hsurv)]
      exact ((phi4WTriplePrime_inv_recon_survivor_iff I x).mp hsurv).1
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstar
      obtain ⟨δ', hδ', rfl⟩ := hstar
      obtain ⟨γ, hγ, rfl⟩ :=
        phi4WTriplePrime_inv_recoveredInnerForest_element_origin I
          (phi4WTriplePrime_inv_innerForest_CD_proof I) hδ'
      rw [phi4WTriplePrime_inv_reconTau_map I ⟨γ, hγ⟩]
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
      have hxP := (phi4WTriplePrime_inv_recon_survivor_iff I w).mpr ⟨hwδ, hwnstar⟩
      refine ⟨w, ?_, ?_⟩
      · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        exact Or.inl (Finset.mem_sdiff.mpr
          ⟨by rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]; exact hxP.1, hxP.2⟩)
      · exact phi4WTriplePrime_inv_reconTau_fix I (Finset.mem_sdiff.mpr ⟨hxP.1, hxP.2⟩)
    · obtain ⟨γ, hγA, rfl⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
      have hγTOF := phi4WTriplePrime_inv_touched_of_starA_mem hγA hwδ
      refine ⟨phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I))
          (phi4WTriplePrime_inv_innerComponent I γ hγTOF), ?_, ?_⟩
      · rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
        exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
          ⟨phi4WTriplePrime_inv_innerComponent I γ hγTOF,
            phi4WTriplePrime_inv_innerComponent_mem_F I γ hγTOF, rfl⟩)
      · exact phi4WTriplePrime_inv_reconTau_map I ⟨γ, hγTOF⟩

/-! ## Step 6 — `δ`'s resolved boundary edges as the parent's, retargeted. -/

/-- **body-613 — `δ.rbe = P.rbe.map (A.retargetEdge starA)`.**  The inverse of body-604's
`remnant_resolvedBoundaryEdges`: `δ`'s quotient boundary edges are the recovered parent's boundary edges
retargeted through `A`.  Mirrors body-609's boundary-edge bookkeeping. -/
theorem phi4WTriplePrime_inv_delta_resolvedBoundaryEdges
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    δ.1.resolvedBoundaryEdges
      = (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges.map
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  have hAmb : ResolvedAmbientSupported G := I.rootAmbientSupported
  -- A-internal edges never cross the region boundary
  have hAfail : z.1.1.internalEdges.filter (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge
      = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨γ', hγ', heγ'⟩ : ∃ γ' ∈ z.1.1.elements, e ∈ γ'.internalEdges := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he; exact he
    obtain ⟨hs, ht⟩ := γ'.edges_supported e heγ'
    have hsG : e.source ∈ G.vertices := γ'.vertices_subset hs
    have htG : e.target ∈ G.vertices := γ'.vertices_subset ht
    have hse : e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ↔ phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ' ∈ δ.1.vertices := by
      rw [← phi4WTriplePrime_inv_retarget_mem_delta_iff I hsG,
        phi4WTriplePrime_retargetVertex_eq_star z.1.1 _ hγ' hs]
    have hte : e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ↔ phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ' ∈ δ.1.vertices := by
      rw [← phi4WTriplePrime_inv_retarget_mem_delta_iff I htG,
        phi4WTriplePrime_retargetVertex_eq_star z.1.1 _ hγ' ht]
    intro hbd
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hte.mpr (hse.mp h1))
    · exact h1 (hse.mpr (hte.mp h2))
  -- boundary predicate transports across the retarget on complement edges
  have hpred : ∀ e ∈ z.1.1.complementEdges,
      δ.1.resolvedIsBoundaryEdge (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e)
        ↔ (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e := by
    intro e he
    have hsG : e.source ∈ G.vertices :=
      (hAmb.1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
    have htG : e.target ∈ G.vertices :=
      (hAmb.1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
    have hs := phi4WTriplePrime_inv_retarget_mem_delta_iff I hsG
    have ht := phi4WTriplePrime_inv_retarget_mem_delta_iff I htG
    show (((z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source ∈ δ.1.vertices
          ∧ (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).target ∉ δ.1.vertices)
        ∨ ((z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).source ∉ δ.1.vertices
          ∧ (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e).target ∈ δ.1.vertices))
      ↔ ((e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
          ∧ e.target ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices)
        ∨ (e.source ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices
          ∧ e.target ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices))
    simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source,
      ResolvedFeynmanEdge.retarget_target, phi4WTriplePrime_inv_recoveredParent_vertices]
    rw [hs, ht]
  -- descend δ.rbe = Q.internalEdges.filter δ.bdry, transport, then collapse to P.rbe
  show ((z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).internalEdges).filter
      δ.1.resolvedIsBoundaryEdge = _
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges,
    ← Multiset.map_filter_of_iff (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
        z.1.1.complementEdges
        (fun e => δ.1.resolvedIsBoundaryEdge
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e))
        δ.1.resolvedIsBoundaryEdge (fun _ => Iff.rfl)]
  congr 1
  have hcongr : z.1.1.complementEdges.filter
        (fun e => δ.1.resolvedIsBoundaryEdge
          (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e))
      = z.1.1.complementEdges.filter (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge := by
    apply Multiset.filter_congr
    intro e he
    exact hpred e he
  rw [hcongr]
  unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges ResolvedAdmissibleSubgraph.complementEdges
  rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]

/-! ## Step 7 — external-leg raw equality (EVEN + ODD, under τ). -/

/-- **body-613 (Step 7, externalLegs) — the recontraction external legs (under `τ`) equal `δ`'s boundary-
completed legs.**  Both split EVEN + ODD: EVEN via body-609's leg transport + `encodeExistingLeg`; ODD via
`δ.rbe = P.rbe.map (A.retargetEdge starA)` + the inside-endpoint agreement.  Multiplicity/id/sector exact. -/
theorem phi4WTriplePrime_inv_recontraction_externalLegs_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)))).mapPerm
        (phi4WTriplePrime_inv_reconTau I)).externalLegs
      = δ.1.boundaryCompletedResolvedGraph.externalLegs := by
  show ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest I
          (phi4WTriplePrime_inv_innerForest_CD_proof I)))).externalLegs.map
        (ResolvedExternalLeg.map (phi4WTriplePrime_inv_reconTau I))
    = δ.1.boundaryCompletedResolvedGraph.externalLegs
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_externalLegs,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_externalLegs]
  unfold ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs
  rw [Multiset.map_add]
  congr 1
  · -- EVEN
    rw [phi4WTriplePrime_inv_recoveredParent_externalLegs_transport I,
      Multiset.map_map, Multiset.map_map]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hatt : ℓ.attachedTo ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices :=
      (phi4WTriplePrime_inv_recoveredParent I).legs_supported ℓ hℓ
    have hc := phi4WTriplePrime_inv_recon_coord I hatt
    simp only [Function.comp, ResolvedAdmissibleSubgraph.retargetExternalLeg,
      ResolvedExternalLeg.retarget, ResolvedExternalLeg.map, encodeExistingLeg, existingLegId]
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
    have hcoord := phi4WTriplePrime_inv_recon_coord I hinside
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
    show ResolvedExternalLeg.map (phi4WTriplePrime_inv_reconTau I)
        ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).retargetExternalLeg
          (phi4WTriplePrimeCanonicalSupply.starOf
            (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
            (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)))
          ((phi4WTriplePrime_inv_recoveredParent I).boundaryExternalLeg e))
      = δ.1.boundaryExternalLeg (z.1.1.retargetEdge (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) e)
    unfold ResolvedFeynmanSubgraph.boundaryExternalLeg ResolvedAdmissibleSubgraph.retargetExternalLeg
      ResolvedExternalLeg.retarget ResolvedExternalLeg.map
    rw [hend, hcoord]
    simp only [ResolvedFeynmanSubgraph.boundaryLegId, ResolvedAdmissibleSubgraph.retargetEdge,
      ResolvedFeynmanEdge.retarget]

/-! ## Step 8 — the raw graph equality + class descent + frontier discharge. -/

/-- **body-613 (Step 8, RAW) — the recontraction (under `τ`) reconstructs `δ`'s boundary-completion.**  A RAW
`ResolvedFeynmanGraph` equality on all three fields — the exact inverse of body-604's forward contract-twice. -/
theorem phi4WTriplePrime_inv_recontraction_raw
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ((phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest I (phi4WTriplePrime_inv_innerForest_CD_proof I)))).mapPerm
        (phi4WTriplePrime_inv_reconTau I)
      = δ.1.boundaryCompletedResolvedGraph := by
  have hgen : ∀ (a b : ResolvedFeynmanGraph), a.vertices = b.vertices → a.internalEdges = b.internalEdges →
      a.externalLegs = b.externalLegs → a = b := by
    intro a b h1 h2 h3
    cases a; cases b
    simp only [ResolvedFeynmanGraph.mk.injEq]
    exact ⟨h1, h2, h3⟩
  exact hgen _ _ (phi4WTriplePrime_inv_recontraction_vertices_eq I)
    (phi4WTriplePrime_inv_recontraction_internalEdges_eq I)
    (phi4WTriplePrime_inv_recontraction_externalLegs_eq I)

/-- **body-613 (VICTORY) — the body-609 recontraction-recovery proof frontier (CORRECTED target) is
DISCHARGED.**  Takes only `I`.  From the RAW equality, `toResolvedClass_mapPerm` collapses the correcting
permutation, giving the honest class equality against `δ.1.boundaryCompletedResolvedGraph`. -/
theorem phi4WTriplePrime_inv_recontraction_recovery_proof
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    phi4WTriplePrime_inv_recontraction_recovery I (phi4WTriplePrime_inv_innerForest_CD_proof I) := by
  unfold phi4WTriplePrime_inv_recontraction_recovery
  rw [← ResolvedFeynmanGraph.toResolvedClass_mapPerm _ (phi4WTriplePrime_inv_reconTau I),
    phi4WTriplePrime_inv_recontraction_raw I]

end GaugeGeometry.QFT.Combinatorial
