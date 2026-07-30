import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockInverseSectors

/-!
# QFT-R1-body-609 — star-touching parent + live inner-forest decontraction

This body is the INVERSE of the body-604/605 contract-twice: from a star-touching quotient component `δ`
(body-608's `ForestDecontractionInput`), reconstruct the forest occurrence — a recovered PARENT on the root
ambient `G`.

## Recovered parent as an induced subgraph (the key simplification)

The recovered parent REPLACES each `A`-star appearing in `δ` with its outer-component region:

```
recoveredParent.vertices = (δ.vertices \ A-stars) ∪ (touchedOuterForest z δ).vertices
```

Its internal edges are exactly the three families the spec dictates — `δ`'s non-star edges (already
`G`-native, so un-retargeted = identity), the `touchedOuterForest`'s own internal edges, and the boundary
edges reconnecting the star sites — and these are PRECISELY the `G`-internal edges with BOTH endpoints in
`recoveredParent.vertices`.  Hence the recovered parent is the **induced subgraph** of `G` on that vertex
set, and its external legs are the touched-leg lift (the genuine `G`-legs attached inside the region).  The
induced presentation makes the recovered parent automatically well-formed, internal-edge complete, and
external-leg saturated in `G` (all by definitional equality of the induced filter).

## Delivered here (axiom-clean, `sorry`-free)

* **Step 1** — `phi4WTriplePrime_inv_recoveredParent` (the induced-subgraph parent) + banking.
* **Step 2** — combinatorial leaves (`IsNonempty`, positive edges, `ResolvedAmbientSupported G`, id reuse,
  `ResolvedExternalLegSaturated G`, `ResolvedInternalEdgeComplete`); the **KEY MEMBERSHIP IFF**
  `phi4WTriplePrime_inv_retarget_mem_delta_iff` (retarget lands in `δ` iff `v` in the region); and the FULL
  **degree recovery** — leg-count eq + boundary-count eq + `physicalExternalLegCount` eq ⇒ the recovered
  parent is φ⁴ **`IsDivergent`** (PROVED outright, NO residual, NO ambient-invariance class).  Connectivity /
  1PI enter the parent CD through the SINGLE named topology residual `…_ForgetTopology`.
* **Step 3** — `phi4WTriplePrime_inv_recoveredInnerForest` (touched outer components transported as induced
  subgraphs into the parent's boundary-completed ambient); pairwise disjointness PROVED; component CD carried
  as the named residual `…_innerForest_CD`.
* **Step 4** — `phi4WTriplePrime_inv_recoveredInnerForest_mem` (live W‴): the four ambient gates (support +
  ids via body-589 & the input; class-CD via body-590 & the topology residual) + forest saturation /
  edge-completeness PROVED; only the complement positivity is the named residual `…_complement_pos`.
* **Step 5** — `phi4WTriplePrime_inv_promotion_recovery` (RAW element-set round-trip, via component saturation).

**Verdict — decontraction core + parent divergence + RAW promotion recovery.**  Body-609 banks the recovered
parent, the combinatorial leaves, the key membership iff, the full degree recovery (boundary + leg + physical
external valence) and hence **parent φ⁴ divergence PROVED outright**, and the RAW promotion round-trip.  The
conditional wiring lemmas (`…_isConnectedDivergent`, `…_recoveredInnerForest`, `…_recoveredInnerForest_mem`)
remain as frontier-threaded wiring; the single 4-field recovered-occurrence OWNER is NOT minted here (it is
issued once in body-614, after all frontiers discharge).

## Proof frontiers (NOT external input — provable-but-large proof debt, each its own body)

These four `Prop` predicates are **PROOF FRONTIERS**, not physics assumptions or residual laws.  Each is
PROVABLE; each is a body of its own, so they are named here and threaded honestly (never `sorry`, never
propagated to the final coassoc):
`…_ForgetTopology` → body-610 (parent forget support-connectivity + 1PI, ≈330-line 549–552 blueprint re-key);
`…_innerForest_CD` → body-611 (per-component divergence CD transport in the nested ambient);
`…_innerForest_complement_pos` → body-612 (residual-count identity, then `recoveredInnerForest_mem`
unconditional); `…_recontraction_recovery` → body-613 (inverse-direction mirror of the body-604 forward raw
equality, ≈860 lines, correcting-permutation class form).  Everything else is PROVED.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration's type; no `s` / `componentEquiv`; no union/global-split/whole-Equiv/summand/alpha/coassoc; no
strict cross-presentation star equality; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst609 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the recovered parent (induced subgraph on the de-contraction vertex set) -/

/-- **body-609 (Step 1) — the recovered-parent vertex set.**  The star-free part of `δ` (its vertices with
the `A`-stars removed) glued to the touched outer forest's vertices.  Depends only on `z` and `δ`. -/
noncomputable def phi4WTriplePrime_inv_recoveredParent_verts
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) : Finset VertexId :=
  (δ.1.vertices \ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1))
    ∪ (phi4WTriplePrime_touchedOuterForest z δ).vertices

/-- The recovered-parent vertex set lies in `G`.  The star-free part sits in `G.vertices ∖ A.vertices`
(remove the `Q`-star coordinates), the touched-outer part sits in `A.vertices ⊆ G.vertices`. -/
theorem phi4WTriplePrime_inv_recoveredParent_verts_subset
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_inv_recoveredParent_verts z δ ⊆ G.vertices := by
  intro v hv
  rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union] at hv
  rcases hv with hvd | hvt
  · rw [Finset.mem_sdiff] at hvd
    obtain ⟨hvδ, hvstar⟩ := hvd
    have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
      δ.1.vertices_subset hvδ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
    rcases hvQ with h | h
    · exact (Finset.mem_sdiff.mp h).1
    · exact absurd h hvstar
  · rw [ResolvedAdmissibleSubgraph.mem_vertices] at hvt
    obtain ⟨γ, _hγ, hvγ⟩ := hvt
    exact γ.vertices_subset hvγ

/-- **body-609 (Step 1, HEADLINE) — the recovered parent.**  The induced subgraph of `G` on the
de-contraction vertex set: internal edges are the `G`-edges with both endpoints inside the region (the
un-retargeted `δ`-edges + the touched-forest edges + the boundary reconnection edges, automatically), and
external legs are the touched-leg lift (the genuine `G`-legs attached inside the region). -/
noncomputable def phi4WTriplePrime_inv_recoveredParent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ) : ResolvedFeynmanSubgraph G where
  vertices := phi4WTriplePrime_inv_recoveredParent_verts z δ
  internalEdges := G.internalEdges.filter
    (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ ∧
              e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
  externalLegs := G.externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ)
  vertices_subset := phi4WTriplePrime_inv_recoveredParent_verts_subset z δ
  internalEdges_le := Multiset.filter_le _ _
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := fun _e he => (Multiset.mem_filter.mp he).2
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem phi4WTriplePrime_inv_recoveredParent_vertices
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).vertices
      = phi4WTriplePrime_inv_recoveredParent_verts z δ := rfl

@[simp] theorem phi4WTriplePrime_inv_recoveredParent_internalEdges
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).internalEdges
      = G.internalEdges.filter
          (fun e => e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ ∧
                    e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ) := rfl

@[simp] theorem phi4WTriplePrime_inv_recoveredParent_externalLegs
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).externalLegs
      = G.externalLegs.filter
          (fun ℓ => ℓ.attachedTo ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ) := rfl

/-! ## Step 2 — recovered-parent leaf facts (the combinatorial W‴ leaves) -/

/-- **body-609 (Step 2) — the recovered parent is internal-edge complete in `G`.**  Immediate: the induced
internal-edge filter IS `ResolvedInternalEdgeComplete`'s filter (definitional equality). -/
theorem phi4WTriplePrime_inv_recoveredParent_edgeComplete
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedInternalEdgeComplete (phi4WTriplePrime_inv_recoveredParent I) := le_refl _

/-- **body-609 (Step 2) — the recovered parent is external-leg saturated in `G`.**  Immediate: the induced
external-leg filter IS `ResolvedExternalLegSaturated`'s filter (definitional equality). -/
theorem phi4WTriplePrime_inv_recoveredParent_saturated
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedExternalLegSaturated G (phi4WTriplePrime_inv_recoveredParent I) := le_refl _

/-- **body-609 (Step 2) — root ambient support of `G` (reused from the input).** -/
theorem phi4WTriplePrime_inv_recoveredParent_ambientSupported
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedAmbientSupported G := I.rootAmbientSupported

/-- **body-609 (Step 2) — root edge-id uniqueness (reused from the input). -/
theorem phi4WTriplePrime_inv_recoveredParent_edgeIdsUnique
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    G.EdgeIdsUnique := I.rootEdgeIdsUnique

/-- **body-609 (Step 2) — root leg-id uniqueness (reused from the input). -/
theorem phi4WTriplePrime_inv_recoveredParent_legIdsUnique
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    G.LegIdsUnique := I.rootLegIdsUnique

/-- A touched outer component (from `touchedNonempty`) sits inside the touched outer forest and, being a
proper-forest component, is vertex-nonempty and positively edged — the witness for the parent's
nonemptiness / positive edge count. -/
theorem phi4WTriplePrime_inv_touched_witness
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ∃ γ, γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements ∧
      γ.vertices.Nonempty ∧ 0 < γ.internalEdges.card := by
  obtain ⟨γsub, hγsub⟩ := I.touchedNonempty
  simp only [phi4WTriplePrime_touchedOuterComponents, Finset.mem_filter] at hγsub
  obtain ⟨_, hstar⟩ := hγsub
  have hApf : z.1.1.IsProperForest := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1
  have hγA : γsub.1 ∈ z.1.1.elements := γsub.2
  have hγTOF : γsub.1 ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
    rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]
    exact ⟨hγA, hstar⟩
  have hne : γsub.1.vertices.Nonempty :=
    Finset.card_pos.mp (hApf.2.1 γsub.1 hγA)
  have hpos : 0 < γsub.1.internalEdges.card := hApf.2.2.2.1 γsub.1 hγA
  exact ⟨γsub.1, hγTOF, hne, hpos⟩

/-- **body-609 (Step 2) — the recovered parent is vertex-nonempty.**  A touched outer component contributes
its (nonempty) vertices to the parent's region. -/
theorem phi4WTriplePrime_inv_recoveredParent_isNonempty
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).IsNonempty := by
  obtain ⟨γ, hγTOF, ⟨v, hvγ⟩, _⟩ := phi4WTriplePrime_inv_touched_witness I
  have hvverts : v ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := by
    rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
    exact Or.inr (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγTOF, hvγ⟩)
  show 0 < (phi4WTriplePrime_inv_recoveredParent I).vertices.card
  rw [phi4WTriplePrime_inv_recoveredParent_vertices]
  exact Finset.card_pos.mpr ⟨v, hvverts⟩

/-- **body-609 (Step 2) — the recovered parent has positive internal edge count.**  A touched outer
component's own internal edges (both endpoints inside its region ⊆ the parent region) survive the induced
filter. -/
theorem phi4WTriplePrime_inv_recoveredParent_internalEdges_card_pos
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    0 < (phi4WTriplePrime_inv_recoveredParent I).internalEdges.card := by
  obtain ⟨γ, hγTOF, _, hpos⟩ := phi4WTriplePrime_inv_touched_witness I
  obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos)
  obtain ⟨hs, ht⟩ := γ.edges_supported e he
  have hsub : γ.vertices ⊆ phi4WTriplePrime_inv_recoveredParent_verts z δ := by
    intro w hw
    rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
    exact Or.inr (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγTOF, hw⟩)
  have heG : e ∈ G.internalEdges := Multiset.mem_of_le γ.internalEdges_le he
  have hemem : e ∈ (phi4WTriplePrime_inv_recoveredParent I).internalEdges := by
    rw [phi4WTriplePrime_inv_recoveredParent_internalEdges, Multiset.mem_filter]
    exact ⟨heG, hsub hs, hsub ht⟩
  exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, hemem⟩

/-! ## Step 2 (divergence) — the KEY MEMBERSHIP IFF + degree recovery -/

/-- **body-609 (Step 2, KEY MEMBERSHIP IFF) — the linchpin of the degree recovery.**  For an ambient vertex
`v`, its `A`-retarget lands in `δ` iff `v` lies in the recovered-parent region.  A carrier vertex retargets
to its component's star, which is in `δ` iff the component is touched (i.e. is in `touchedOuterForest`, i.e.
`v ∈ touchedOuterForest.vertices`); a non-carrier vertex is fixed and lies in `δ ∖ stars` iff it is in `δ`.
Star freshness (touched stars are `∉ G`) removes the star coordinates. -/
theorem phi4WTriplePrime_inv_retarget_mem_delta_iff
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) {v : VertexId} (hvG : v ∈ G.vertices) :
    z.1.1.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1) v ∈ δ.1.vertices
      ↔ v ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  by_cases hvA : v ∈ A.vertices
  · obtain ⟨γ, hγ, hvγ⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp hvA
    rw [phi4WTriplePrime_retargetVertex_eq_star A starOf hγ hvγ]
    rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
    constructor
    · intro hstar
      have hγTOF : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter]
        exact ⟨hγ, hstar⟩
      exact Or.inr (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγTOF, hvγ⟩)
    · rintro (hd | ht)
      · exfalso
        obtain ⟨hvδ, _⟩ := Finset.mem_sdiff.mp hd
        have hvQ := δ.1.vertices_subset hvδ
        rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
        rcases hvQ with h | h
        · exact (Finset.mem_sdiff.mp h).2 hvA
        · obtain ⟨γ', hγ', hv'⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp h
          exact phi4WTriplePrime_inv_star_not_mem_vertices A hApf hγ' (hv' ▸ hvG)
      · obtain ⟨γ'', hγ''TOF, hvγ''⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp ht
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter] at hγ''TOF
        obtain ⟨hγ''A, hstar''⟩ := hγ''TOF
        have hγeq : γ'' = γ := by
          by_contra hne
          exact Finset.disjoint_left.mp (A.pairwiseDisjoint hγ''A hγ hne) hvγ'' hvγ
        rwa [hγeq] at hstar''
  · rw [A.retargetVertex_of_not_mem starOf hvA]
    rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
    constructor
    · intro hvδ
      refine Or.inl (Finset.mem_sdiff.mpr ⟨hvδ, ?_⟩)
      intro hvstar
      obtain ⟨γ', hγ', hv'⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hvstar
      exact phi4WTriplePrime_inv_star_not_mem_vertices A hApf hγ' (hv' ▸ hvG)
    · rintro (hd | ht)
      · exact (Finset.mem_sdiff.mp hd).1
      · exfalso
        apply hvA
        obtain ⟨γ'', hγ''TOF, hvγ''⟩ := ResolvedAdmissibleSubgraph.mem_vertices.mp ht
        rw [phi4WTriplePrime_touchedOuterForest_elements, Finset.mem_filter] at hγ''TOF
        exact ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ'', hγ''TOF.1, hvγ''⟩

/-- δ is externally-leg saturated on the quotient `Q` (its live W‴ membership at `δ`). -/
theorem phi4WTriplePrime_inv_delta_saturated
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (_I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    ResolvedExternalLegSaturated
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) δ.1 :=
  (((mem_phi4WTriplePrimeIndex
    (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
      z.2.2).2.2.2.2.2.1) δ.1 δ.2

/-- **body-609 (Step 2, degree) — the recovered parent and `δ` carry the same external legs (transported).**
`δ`'s legs (saturated: the `Q`-legs attached in `δ`) are exactly the recovered parent's legs (the `G`-legs
attached in the region) retargeted through `A` — via the KEY MEMBERSHIP IFF. -/
theorem phi4WTriplePrime_inv_recoveredParent_externalLegs_transport
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    δ.1.externalLegs
      = (phi4WTriplePrime_inv_recoveredParent I).externalLegs.map
          (z.1.1.retargetExternalLeg (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  rw [externalLegs_eq_filter_of_saturated δ.1 (phi4WTriplePrime_inv_delta_saturated I),
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs,
    ← Multiset.map_filter_of_iff (A.retargetExternalLeg starOf) G.externalLegs
        (fun ℓ => (A.retargetExternalLeg starOf ℓ).attachedTo ∈ δ.1.vertices)
        (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) (fun _ => Iff.rfl)]
  rw [phi4WTriplePrime_inv_recoveredParent_externalLegs]
  congr 1
  apply Multiset.filter_congr
  intro ℓ hℓ
  show A.retargetVertex starOf ℓ.attachedTo ∈ δ.1.vertices ↔ _
  exact phi4WTriplePrime_inv_retarget_mem_delta_iff I (I.rootAmbientSupported.2 ℓ hℓ)

/-- **body-609 (Step 2, degree) — the recovered parent's physical external leg count matches `δ`'s
external-leg contribution.** -/
theorem phi4WTriplePrime_inv_recoveredParent_externalLegs_card_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.externalLegs.card
      = δ.1.forget.externalLegs.card := by
  rw [ResolvedFeynmanSubgraph.forget_externalLegs, ResolvedFeynmanSubgraph.forget_externalLegs,
    Multiset.card_map, Multiset.card_map,
    phi4WTriplePrime_inv_recoveredParent_externalLegs_transport I, Multiset.card_map]

/-- **body-609 (Step 2, degree) — the recovered parent's induced boundary count equals `δ`'s.**  The
touched `A`-stars are INTERNAL to the de-contraction (each `A`-internal edge stays on one side of the region
by the KEY MEMBERSHIP IFF), so they contribute NO boundary; on the complement edges the retarget carries
`δ`-boundary-ness to region-boundary-ness (again the KEY IFF). -/
theorem phi4WTriplePrime_inv_recoveredParent_boundaryEdgeCount_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.boundaryEdgeCount
      = δ.1.forget.boundaryEdgeCount := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  set r := A.retargetEdge starOf with hr
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hAmb : ResolvedAmbientSupported G := I.rootAmbientSupported
  -- reduce both boundary counts to resolved boundary edge counts (body-589)
  have hP : (phi4WTriplePrime_inv_recoveredParent I).forget.boundaryEdgeCount
      = (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges.card := by
    unfold FeynmanSubgraph.boundaryEdgeCount
    rw [← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map]
  have hD : δ.1.forget.boundaryEdgeCount = δ.1.resolvedBoundaryEdges.card := by
    unfold FeynmanSubgraph.boundaryEdgeCount
    rw [← ResolvedFeynmanSubgraph.resolvedBoundaryEdges_forget, Multiset.card_map]
  rw [hP, hD]
  -- A-internal edges never cross the region boundary (same-component endpoints)
  have hAfail : A.internalEdges.filter (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge
      = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨γ', hγ', heγ'⟩ : ∃ γ' ∈ A.elements, e ∈ γ'.internalEdges := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he; exact he
    obtain ⟨hs, ht⟩ := γ'.edges_supported e heγ'
    have hsG : e.source ∈ G.vertices := γ'.vertices_subset hs
    have htG : e.target ∈ G.vertices := γ'.vertices_subset ht
    have hse : e.source ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ↔ starOf γ' ∈ δ.1.vertices := by
      rw [← phi4WTriplePrime_inv_retarget_mem_delta_iff I hsG,
        phi4WTriplePrime_retargetVertex_eq_star A starOf hγ' hs]
    have hte : e.target ∈ phi4WTriplePrime_inv_recoveredParent_verts z δ
        ↔ starOf γ' ∈ δ.1.vertices := by
      rw [← phi4WTriplePrime_inv_retarget_mem_delta_iff I htG,
        phi4WTriplePrime_retargetVertex_eq_star A starOf hγ' ht]
    intro hbd
    rcases hbd with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2 (hte.mpr (hse.mp h1))
    · exact h1 (hse.mpr (hte.mp h2))
  -- the recovered parent's resolved boundary edges are exactly the complement edges cut by the region
  have hR : (phi4WTriplePrime_inv_recoveredParent I).resolvedBoundaryEdges
      = A.complementEdges.filter (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge := by
    unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges ResolvedAdmissibleSubgraph.complementEdges
    rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]
  -- δ's resolved boundary edges over the quotient ambient
  have hDbd : δ.1.resolvedBoundaryEdges
      = (A.complementEdges.map r).filter δ.1.resolvedIsBoundaryEdge := by
    unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
  -- on complement edges, the retarget carries δ-boundary-ness to region-boundary-ness
  have hpred : ∀ e ∈ A.complementEdges,
      δ.1.resolvedIsBoundaryEdge (r e) ↔ (phi4WTriplePrime_inv_recoveredParent I).resolvedIsBoundaryEdge e := by
    intro e he
    have hsG : e.source ∈ G.vertices :=
      (hAmb.1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).1
    have htG : e.target ∈ G.vertices :=
      (hAmb.1 e (Multiset.mem_of_le (Multiset.sub_le_self _ _) he)).2
    have hs := phi4WTriplePrime_inv_retarget_mem_delta_iff I hsG
    have ht := phi4WTriplePrime_inv_retarget_mem_delta_iff I htG
    show ((r e).source ∈ δ.1.vertices ∧ (r e).target ∉ δ.1.vertices)
        ∨ ((r e).source ∉ δ.1.vertices ∧ (r e).target ∈ δ.1.vertices)
      ↔ (e.source ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices
          ∧ e.target ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices)
        ∨ (e.source ∉ (phi4WTriplePrime_inv_recoveredParent I).vertices
          ∧ e.target ∈ (phi4WTriplePrime_inv_recoveredParent I).vertices)
    simp only [hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget,
      phi4WTriplePrime_inv_recoveredParent_vertices]
    rw [hs, ht]
  rw [hR, hDbd, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp]
  rw [Multiset.filter_congr hpred]

/-- **body-609 (Step 2, degree HEADLINE) — the recovered parent's φ⁴ physical external valence equals `δ`'s.** -/
theorem phi4WTriplePrime_inv_recoveredParent_physicalExternalLegCount_eq
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.physicalExternalLegCount
      = δ.1.forget.physicalExternalLegCount := by
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
    FeynmanSubgraph.boundaryEdgeCount
  rw [phi4WTriplePrime_inv_recoveredParent_externalLegs_card_eq I]
  have hb := phi4WTriplePrime_inv_recoveredParent_boundaryEdgeCount_eq I
  unfold FeynmanSubgraph.boundaryEdgeCount at hb
  rw [hb]

/-- **body-609 (Step 2, VICTORY) — the recovered parent is φ⁴ DIVERGENT on `G`.**  Via the explicit degree
recovery: `δ` is divergent (a `B`-component), and the recovered parent shares `δ`'s physical external
valence, so it too is `≤ 4`.  NO ambient-invariance / Parent supply / reflection class. -/
theorem phi4WTriplePrime_inv_recoveredParent_isDivergent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.IsDivergent := by
  have hCDδ : δ.1.forget.IsConnectedDivergent := z.2.1.isConnectedDivergent δ.1 δ.2
  have hdivδ : δ.1.forget.physicalExternalLegCount ≤ 4 :=
    (phi4_isDivergent_iff δ.1.forget).mp hCDδ.2.2
  exact (phi4_isDivergent_iff _).mpr
    (by rw [phi4WTriplePrime_inv_recoveredParent_physicalExternalLegCount_eq I]; exact hdivδ)

/-! ## Step 2 (topology) — the recovered parent's forget connectivity + 1PI

**PROOF FRONTIER — NOT EXTERNAL INPUT (discharged in body-610).**  The recovered parent's `forget`
support-connectivity and one-particle irreducibility are the un-contraction
(splice-a-connected-blob-at-each-star-site) topology facts.  These are PROVABLE (a clean re-key of the
body-549–552 parent-reachability blueprint — ≈330 lines of support-reachability monotonicity / edge-step /
reachable-lift, currently POLLUTED by `ForestBlockCodType D`, re-derived clean at this induced owner) — they
are proof debt, NOT a new physics assumption or residual law.  That topology re-derivation is a body of its
own (body-610), so it is named here as a frontier predicate threaded honestly through the conditional wiring
lemmas below.  Divergence (above) is proved OUTRIGHT and needs NO frontier. -/
def phi4WTriplePrime_inv_recoveredParent_ForgetTopology
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) : Prop :=
  (phi4WTriplePrime_inv_recoveredParent I).forget.IsConnected
    ∧ (phi4WTriplePrime_inv_recoveredParent I).forget.IsOnePI

/-- **body-609 (Step 2) — the recovered parent is φ⁴ connected-divergent on `G`.**  Divergence is proved
outright (degree recovery); connectivity + 1PI enter through the named topology residual. -/
theorem phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (htop : phi4WTriplePrime_inv_recoveredParent_ForgetTopology I) :
    (phi4WTriplePrime_inv_recoveredParent I).forget.IsConnectedDivergent :=
  ⟨htop.1, htop.2, phi4WTriplePrime_inv_recoveredParent_isDivergent I⟩

/-- **body-609 (Step 2) — the recovered parent's boundary-completed ambient is self-connected-divergent**
(via body-590 `boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent`, fed the parent's own CD).
This is the CD gate for the parent's boundary-completed ambient used by Steps 3–4. -/
theorem phi4WTriplePrime_inv_recoveredParent_boundaryCompleted_isConnectedDivergent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (htop : phi4WTriplePrime_inv_recoveredParent_ForgetTopology I) :
    ∃ hWF : (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self
          (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.forget hWF) :=
  ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent _
    (phi4WTriplePrime_inv_recoveredParent_isConnectedDivergent I htop)

/-! ## Step 3 — the recovered inner forest (touched outer components, transported) -/

/-- A touched outer component's vertices lie in the recovered-parent region. -/
theorem phi4WTriplePrime_inv_touchedComponent_verts_subset
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    γ.vertices ⊆ phi4WTriplePrime_inv_recoveredParent_verts z δ := by
  intro w hw
  rw [phi4WTriplePrime_inv_recoveredParent_verts, Finset.mem_union]
  exact Or.inr (ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨γ, hγ, hw⟩)

/-- A touched outer component's internal edges embed into the recovered parent's internal edges. -/
theorem phi4WTriplePrime_inv_touchedComponent_internalEdges_le
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    γ.internalEdges ≤ (phi4WTriplePrime_inv_recoveredParent I).internalEdges := by
  rw [phi4WTriplePrime_inv_recoveredParent_internalEdges, Multiset.le_iff_count]
  intro e
  by_cases he : 0 < Multiset.count e γ.internalEdges
  · have heγ : e ∈ γ.internalEdges := Multiset.count_pos.mp he
    obtain ⟨hs, ht⟩ := γ.edges_supported e heγ
    have hsub := phi4WTriplePrime_inv_touchedComponent_verts_subset (z := z) (δ := δ) hγ
    rw [Multiset.count_filter, if_pos ⟨hsub hs, hsub ht⟩]
    exact Multiset.count_le_of_le e γ.internalEdges_le
  · rw [Nat.eq_zero_of_not_pos he]; exact Nat.zero_le _

/-- **body-609 (Step 3) — a touched outer component transported into the recovered parent's boundary-completed
ambient** (the induced subgraph on the component's vertices; its legs are the parent's completed legs
saturating the component — NO re-encoding). -/
noncomputable def phi4WTriplePrime_inv_innerComponent
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    ResolvedFeynmanSubgraph (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.externalLegs.filter
    (fun ℓ => ℓ.attachedTo ∈ γ.vertices)
  vertices_subset := by
    rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices,
      phi4WTriplePrime_inv_recoveredParent_vertices]
    exact phi4WTriplePrime_inv_touchedComponent_verts_subset (z := z) (δ := δ) hγ
  internalEdges_le := by
    rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges]
    exact phi4WTriplePrime_inv_touchedComponent_internalEdges_le I hγ
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := γ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem phi4WTriplePrime_inv_innerComponent_vertices
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).vertices = γ.vertices := rfl

@[simp] theorem phi4WTriplePrime_inv_innerComponent_internalEdges
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    (phi4WTriplePrime_inv_innerComponent I γ hγ).internalEdges = γ.internalEdges := rfl

/-- **body-609 (Step 3) — PROOF FRONTIER — NOT EXTERNAL INPUT (discharged in body-611): the transported inner
components are connected-divergent.**  Their `forget` support-topology (`IsConnected` / `IsOnePI`) coincides
with the outer component's (same vertices + internal edges, `γ ∈ A.elements`); only the φ⁴ divergence within
the parent's boundary-completed ambient needs a per-component degree bound (a CD transport, body-611).
PROVABLE proof debt, NOT a physics assumption — named here as a frontier predicate. -/
def phi4WTriplePrime_inv_innerForest_CD
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) : Prop :=
  ∀ (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements),
    (phi4WTriplePrime_inv_innerComponent I γ hγ).forget.IsConnectedDivergent

/-- **body-609 (Step 3, HEADLINE) — the recovered inner forest** in the recovered parent's boundary-completed
ambient: one transported component per touched outer component.  Admissible via the residual CD + the outer
components' pairwise disjointness (transported verbatim). -/
noncomputable def phi4WTriplePrime_inv_recoveredInnerForest
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily
      (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph :=
  ResolvedAdmissibleSubgraph.ofElements
    ((phi4WTriplePrime_touchedOuterForest z δ).elements.attach.image
      (fun γ => phi4WTriplePrime_inv_innerComponent I γ.1 γ.2))
    (by
      intro δ' hδ'
      obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ'
      exact hCD γ.1 γ.2)
    (by
      intro δ' hδ' δ'' hδ'' hne
      obtain ⟨γ₁, -, rfl⟩ := Finset.mem_image.mp hδ'
      obtain ⟨γ₂, -, rfl⟩ := Finset.mem_image.mp hδ''
      have hγsubne : γ₁ ≠ γ₂ :=
        fun h => hne (congrArg (fun g => phi4WTriplePrime_inv_innerComponent I g.1 g.2) h)
      have hγne : γ₁.1 ≠ γ₂.1 := fun h => hγsubne (Subtype.ext h)
      have hsubel : (phi4WTriplePrime_touchedOuterForest z δ).elements ⊆ z.1.1.elements := by
        rw [phi4WTriplePrime_touchedOuterForest_elements]; exact Finset.filter_subset _ _
      have hγ₁A : γ₁.1 ∈ z.1.1.elements := hsubel γ₁.2
      have hγ₂A : γ₂.1 ∈ z.1.1.elements := hsubel γ₂.2
      show _root_.Disjoint (phi4WTriplePrime_inv_innerComponent I γ₁.1 γ₁.2).vertices
        (phi4WTriplePrime_inv_innerComponent I γ₂.1 γ₂.2).vertices
      exact z.1.1.pairwiseDisjoint hγ₁A hγ₂A hγne)

@[simp] theorem phi4WTriplePrime_inv_recoveredInnerForest_elements
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    (phi4WTriplePrime_inv_recoveredInnerForest I hCD).elements
      = (phi4WTriplePrime_touchedOuterForest z δ).elements.attach.image
          (fun γ => phi4WTriplePrime_inv_innerComponent I γ.1 γ.2) := rfl

/-! ## Step 4 — the recovered inner forest is a live W‴ forest -/

/-- Touched outer forest elements are `A`-components. -/
theorem phi4WTriplePrime_inv_touchedForest_subset_A
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}} :
    (phi4WTriplePrime_touchedOuterForest z δ).elements ⊆ z.1.1.elements := by
  rw [phi4WTriplePrime_touchedOuterForest_elements]; exact Finset.filter_subset _ _

/-- Every recovered-inner-forest element is a transported touched component. -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_element_origin
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I)
    {δ' : ResolvedFeynmanSubgraph (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph}
    (hδ' : δ' ∈ (phi4WTriplePrime_inv_recoveredInnerForest I hCD).elements) :
    ∃ (γ : ResolvedFeynmanSubgraph G) (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements),
      δ' = phi4WTriplePrime_inv_innerComponent I γ hγ := by
  rw [phi4WTriplePrime_inv_recoveredInnerForest_elements] at hδ'
  obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ'
  exact ⟨γ.1, γ.2, rfl⟩

/-- **body-609 (Step 4) — the recovered inner forest is externally-leg saturated** (each transported component
carries the parent-completion legs saturating it, by construction). -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_forestSaturated
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    ResolvedForestExternalLegSaturated (phi4WTriplePrime_inv_recoveredInnerForest I hCD) := by
  intro δ' hδ'
  obtain ⟨γ, hγ, rfl⟩ := phi4WTriplePrime_inv_recoveredInnerForest_element_origin I hCD hδ'
  exact le_refl _

/-- **body-609 (Step 4) — the recovered inner forest is internal-edge complete** (from each outer component's
own edge-completeness in `G`, restricted through the parent's edges). -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_forestEdgeComplete
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily
      (phi4WTriplePrime_inv_recoveredInnerForest I hCD) := by
  intro δ' hδ'
  obtain ⟨γ, hγ, rfl⟩ := phi4WTriplePrime_inv_recoveredInnerForest_element_origin I hCD hδ'
  have hγA : γ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ
  have hEC : ResolvedInternalEdgeComplete γ :=
    ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.2 γ hγA
  have hHle : (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.internalEdges
      ≤ G.internalEdges := by
    rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges]
    exact (phi4WTriplePrime_inv_recoveredParent I).internalEdges_le
  show (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph.internalEdges.filter
      (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) ≤ γ.internalEdges
  exact le_trans (Multiset.filter_le_filter _ hHle) hEC

/-- **body-609 (Step 4) — PROOF FRONTIER — NOT EXTERNAL INPUT (discharged in body-612): the recovered inner
forest's complement is positive.**  The recovered parent's boundary-completed ambient has more internal edges
than the touched outer forest (a residual-count identity mirroring body-606's outer-properness
complement-positivity route).  PROVABLE from the parent/δ residual-count once the inner forest is live
(body-612); named here as a frontier predicate, NOT a new hypothesis pre-added to the audit. -/
def phi4WTriplePrime_inv_innerForest_complement_pos
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    Prop :=
  0 < (phi4WTriplePrime_inv_recoveredInnerForest I hCD).complementEdges.card

/-- **body-609 (Step 4) — the recovered inner forest is a proper forest.**  Nonemptiness / positive edges from
the touched witness + the outer components' properness; complement positivity via the named residual. -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_isProperForest
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I)
    (hCompPos : phi4WTriplePrime_inv_innerForest_complement_pos I hCD) :
    (phi4WTriplePrime_inv_recoveredInnerForest I hCD).IsProperForest := by
  have hApf : z.1.1.IsProperForest := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.1
  obtain ⟨γ₀, hγ₀, _, hpos₀⟩ := phi4WTriplePrime_inv_touched_witness I
  have hc0mem : phi4WTriplePrime_inv_innerComponent I γ₀ hγ₀
      ∈ (phi4WTriplePrime_inv_recoveredInnerForest I hCD).elements := by
    rw [phi4WTriplePrime_inv_recoveredInnerForest_elements]
    exact Finset.mem_image.mpr ⟨⟨γ₀, hγ₀⟩, Finset.mem_attach _ _, rfl⟩
  refine ⟨⟨_, hc0mem⟩, ?_, ?_, ?_, hCompPos⟩
  · intro δ' hδ'
    obtain ⟨γ, hγ, rfl⟩ := phi4WTriplePrime_inv_recoveredInnerForest_element_origin I hCD hδ'
    exact hApf.2.1 γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)
  · obtain ⟨e, he⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos₀)
    have hle : (phi4WTriplePrime_inv_innerComponent I γ₀ hγ₀).internalEdges
        ≤ (phi4WTriplePrime_inv_recoveredInnerForest I hCD).internalEdges :=
      Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hc0mem
    exact Multiset.card_pos_iff_exists_mem.mpr ⟨e, Multiset.mem_of_le hle he⟩
  · intro δ' hδ'
    obtain ⟨γ, hγ, rfl⟩ := phi4WTriplePrime_inv_recoveredInnerForest_element_origin I hCD hδ'
    exact hApf.2.2.2.1 γ (phi4WTriplePrime_inv_touchedForest_subset_A hγ)

/-- **body-609 (Step 4, HEADLINE) — the recovered inner forest is a LIVE W‴ forest** on the recovered parent's
boundary-completed ambient.  Four ambient gates (support + IDs from body-589 & the input; class-CD from the
parent's own CD via body-590 & `htop`) plus the Step-4 forest facts (properness / saturation / edge-
completeness). -/
theorem phi4WTriplePrime_inv_recoveredInnerForest_mem
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I)
    (htop : phi4WTriplePrime_inv_recoveredParent_ForgetTopology I)
    (hCompPos : phi4WTriplePrime_inv_innerForest_complement_pos I hCD) :
    phi4WTriplePrime_inv_recoveredInnerForest I hCD
      ∈ phi4WTriplePrimeIndex (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph := by
  rw [mem_phi4WTriplePrimeIndex]
  refine ⟨?_, ?_, ?_, ?_,
    phi4WTriplePrime_inv_recoveredInnerForest_isProperForest I hCD hCompPos,
    phi4WTriplePrime_inv_recoveredInnerForest_forestSaturated I hCD,
    phi4WTriplePrime_inv_recoveredInnerForest_forestEdgeComplete I hCD⟩
  · -- ambient support of the parent's boundary-completed ambient
    refine ⟨?_, ?_⟩
    · intro e he
      rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_internalEdges] at he
      rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]
      exact (phi4WTriplePrime_inv_recoveredParent I).edges_supported e he
    · intro ℓ hℓ
      rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_vertices]
      rw [ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_externalLegs] at hℓ
      exact (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedExternalLegs_supported ℓ hℓ
  · -- class-CD via body-590 + htop
    exact (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
        phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily _).mpr
      (phi4WTriplePrime_inv_recoveredParent_boundaryCompleted_isConnectedDivergent I htop)
  · -- EdgeIdsUnique via body-589 + input
    exact ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_edgeIdsUnique _ I.rootEdgeIdsUnique
  · -- LegIdsUnique via body-589 + input
    exact ResolvedFeynmanSubgraph.boundaryCompletedResolvedGraph_legIdsUnique _
      I.rootLegIdsUnique I.rootEdgeIdsUnique

/-! ## Step 5 — decontraction round-trips + the recovered forest occurrence bundle -/

/-- **body-609 (Step 5, promotion recovery — per component, RAW).**  Promoting a transported inner component
back to the root `G` (body-597 `rootRelativeInner`) recovers the original touched outer component EXACTLY —
its legs re-inflate to `G`'s legs saturating it (the component's own saturation on `G`). -/
theorem phi4WTriplePrime_inv_promotion_recovery_component
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ)
    {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements) :
    rootRelativeInner (phi4WTriplePrime_inv_recoveredParent I)
        (phi4WTriplePrime_inv_innerComponent I γ hγ) = γ := by
  have hγA : γ ∈ z.1.1.elements := phi4WTriplePrime_inv_touchedForest_subset_A hγ
  have hsat : ResolvedExternalLegSaturated G γ :=
    ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.2.2.1 γ hγA
  apply ResolvedFeynmanSubgraph.ext
  · rfl
  · rfl
  · rw [rootRelativeInner_externalLegs, phi4WTriplePrime_inv_innerComponent_vertices I hγ,
      externalLegs_eq_filter_of_saturated γ hsat]

/-- **body-609 (Step 5, promotion recovery — RAW element/subgraph).**  The promotion of the whole recovered
inner forest (each component promoted by `rootRelativeInner`) recovers the touched outer forest's element set
EXACTLY.  RAW component-wise, so a RAW element-set equality (the honest strongest form). -/
theorem phi4WTriplePrime_inv_promotion_recovery
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    (phi4WTriplePrime_inv_recoveredInnerForest I hCD).elements.image
        (rootRelativeInner (phi4WTriplePrime_inv_recoveredParent I))
      = (phi4WTriplePrime_touchedOuterForest z δ).elements := by
  rw [phi4WTriplePrime_inv_recoveredInnerForest_elements, Finset.image_image]
  rw [show (rootRelativeInner (phi4WTriplePrime_inv_recoveredParent I)
        ∘ fun γ : {x // x ∈ (phi4WTriplePrime_touchedOuterForest z δ).elements} =>
            phi4WTriplePrime_inv_innerComponent I γ.1 γ.2)
      = Subtype.val from
    funext (fun γ => phi4WTriplePrime_inv_promotion_recovery_component I γ.2)]
  exact Finset.attach_image_val

/-- **body-609 (Step 5) — PROOF FRONTIER — NOT EXTERNAL INPUT (discharged in body-613): recontraction
recovery (honest class form).**  Contracting the recovered parent's boundary-completed ambient by the
recovered inner forest returns `δ` — at the resolved CLASS level (a strict raw star equality is NOT claimed;
the canonical recontraction star and `δ`'s quotient star generally differ, so the honest statement is a
`toResolvedClass` equality, discharged via ONE body-580 correcting permutation).  PROVABLE proof debt (the
inverse-direction mirror of the body-604 forward contract-twice raw equality, ≈860 lines — a body of its own,
body-613), NOT a physics assumption — named here as a frontier predicate. -/
def phi4WTriplePrime_inv_recontraction_recovery
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (I : phi4WTriplePrime_ForestDecontractionInput z δ) (hCD : phi4WTriplePrime_inv_innerForest_CD I) :
    Prop :=
  ((phi4WTriplePrime_inv_recoveredInnerForest I hCD).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent I).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest I hCD))).toResolvedClass
    = δ.1.toResolvedFeynmanGraph.toResolvedClass

/-! ## The canonical `RecoveredForestOccurrence` owner is NOT issued here.

Per the body-609 scope decision, the single 4-field recovered-occurrence owner (bundling parent + inner
forest + parent CD + inner W‴ membership + both round-trips) is issued ONCE — in body-614 — only AFTER all
four proof frontiers (`_ForgetTopology` [610], `_innerForest_CD` [611], `_innerForest_complement_pos` [612],
`_recontraction_recovery` [613]) are discharged.  Emitting a residual-fielded owner here would propagate the
frontiers downstream and blur the audit unit; the conditional `_of_frontiers`-style wiring lemmas above
(`…_isConnectedDivergent`, `…_recoveredInnerForest_mem`, `…_promotion_recovery`) already package the wiring
without minting an owner. -/

end GaugeGeometry.QFT.Combinatorial
