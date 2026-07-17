import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocChoiceAlignmentDesign
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSurvivor
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionValue

/-!
# R-6c-body-337 — the concrete right region: a star-avoiding survivor de-embeds STRAIGHT back to `G`

Three-hundred-and-thirty-seventh genuine-body step — the Front-2 entry (`componentToRight`).  A quotient
component `δ ∈ rightDomain z` is **star-avoiding** (`Disjoint δ.vertices (starOfZ z)`), so it never touched
the contraction: its vertices sit in `G \ z.1.1`, and — crucially — the star-contraction retarget is the
IDENTITY on its edges/legs (their endpoints avoid `z.1.1`).  Hence `δ` lifts back to a subgraph of `G` with
the SAME carrier data via the general `ResolvedFeynmanSubgraph.reembed` — NO de-contraction, NO promotion,
NO parent machinery (contrast the forest half's `parent`/`innerIdx`).  This is the LIGHT half of the
codomain reconstruction.

## The genuine work — the three contracted→`G` support facts (retarget-inversion)

`δ.internalEdges ≤ (contractWithStars).internalEdges = complementEdges.map retargetEdge` a-priori only sees
the RETARGETED complement edges.  To land `δ.internalEdges ≤ G.internalEdges` we invert the map: split the
base by "has an endpoint in `z.1.1`", note the retarget is the identity off `z.1.1`, and note every
retargeted-through-`z.1.1` edge/leg lands on a STAR vertex — which a star-avoiding `δ` never carries.  So
`δ`'s edges/legs draw only from the identity (complement / original-`G`) part.

Landed (all axiom-clean):

* `multiset_le_of_le_add_of_notMem` — the count lemma "`s ≤ a + b`, `s ∩ b = ∅` ⟹ `s ≤ a`";
* `retargetVertex_mem_starVertices` — a retargeted `z.1.1`-vertex is a star;
* `starAvoiding_vertices_subset` / `starAvoiding_internalEdges_le` / `starAvoiding_externalLegs_le` — the
  three contracted→`G` support facts for a star-avoiding `δ`;
* `rightReembed` — the concrete `componentToRight`, `δ`'s data re-embedded into `G`;
* `ResolvedConcreteRightRegionValueSupply` + `resolvedConcreteRightRegion` — the concrete right-region
  supply: `rightComponentCD` via `reembed_forget_isConnectedDivergent` (same intrinsic graph), and
  `rightComponentDisjoint` transported from `z.2.1.pairwiseDisjoint` (the re-embedding keeps vertices).

No facade, no flat term, no `forgetHopf`, no rep/perm, no `Classical.choose` for `componentToRight`, no
carrier-membership assumption, no de-contraction on the survivor side.  Per the HALT: `componentToRight` is
built LIGHT; the multi-star `Region` wiring + the three cross-disjointness lemmas (body-338), the touched
`recoverChoice` alignment (body-339), and the biUnion `forward_outer_value` (body-340) remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-337 — count lemma.**  If `s ≤ a + b` and every element of `s` avoids `b`, then `s ≤ a`. -/
theorem multiset_le_of_le_add_of_notMem {α : Type*} [DecidableEq α] {s a b : Multiset α}
    (h : s ≤ a + b) (hb : ∀ x ∈ s, x ∉ b) : s ≤ a := by
  rw [Multiset.le_iff_count]
  intro x
  by_cases hxs : x ∈ s
  · have hx := (Multiset.le_iff_count.mp h) x
    rw [Multiset.count_add, Multiset.count_eq_zero.mpr (hb x hxs)] at hx
    omega
  · rw [Multiset.count_eq_zero.mpr hxs]
    exact Nat.zero_le _

/-- **R-6c-body-337 — a retargeted `A`-vertex is a star.**  For `v ∈ A.vertices`, `A.retargetVertex` sends
`v` to its component's star. -/
theorem retargetVertex_mem_starVertices (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) {v : VertexId} (hv : v ∈ A.vertices) :
    A.retargetVertex starOf v ∈ A.starVertices starOf := by
  rw [ResolvedAdmissibleSubgraph.retargetVertex, ResolvedAdmissibleSubgraph.componentAt?_of_mem A hv]
  exact ResolvedAdmissibleSubgraph.mem_starVertices.mpr
    ⟨A.componentAt hv, A.componentAt_mem hv, rfl⟩

/-- **R-6c-body-337 — star-avoiding vertices support.**  A star-avoiding `δ` in the contracted graph has
all its vertices in `G` (they sit in `G \ A`). -/
theorem starAvoiding_vertices_subset (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (A.contractWithStars starOf))
    (hstar : Disjoint δ.vertices (A.starVertices starOf)) :
    δ.vertices ⊆ G.vertices := by
  intro v hv
  have hmem := δ.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hmem
  cases hmem with
  | inl h => exact (Finset.mem_sdiff.mp h).1
  | inr h => exact absurd h (Finset.disjoint_left.mp hstar hv)

/-- **R-6c-body-337 — star-avoiding external-legs support.**  A star-avoiding `δ`'s legs draw only from the
identity (off-`A`) part of the retargeted legs, hence sit unchanged among `G`'s legs. -/
theorem starAvoiding_externalLegs_le (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (A.contractWithStars starOf))
    (hstar : Disjoint δ.vertices (A.starVertices starOf)) :
    δ.externalLegs ≤ G.externalLegs := by
  have hle : δ.externalLegs ≤ G.externalLegs.map (A.retargetExternalLeg starOf) := by
    have h := δ.externalLegs_le
    rwa [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at h
  -- the retarget is the identity on legs attached off `A`
  have hid : (G.externalLegs.filter (fun ℓ => ¬ (ℓ.attachedTo ∈ A.vertices))).map
        (A.retargetExternalLeg starOf)
      = G.externalLegs.filter (fun ℓ => ¬ (ℓ.attachedTo ∈ A.vertices)) := by
    conv_rhs => rw [← Multiset.map_id (G.externalLegs.filter (fun ℓ => ¬ (ℓ.attachedTo ∈ A.vertices)))]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hnm : ℓ.attachedTo ∉ A.vertices := (Multiset.mem_filter.mp hℓ).2
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [A.retargetVertex_of_not_mem starOf hnm]
    rfl
  -- split the retargeted legs into off-`A` (identity) and on-`A` (star) parts
  have hsplit : G.externalLegs.map (A.retargetExternalLeg starOf)
      = (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ A.vertices)).map (A.retargetExternalLeg starOf)
        + G.externalLegs.filter (fun ℓ => ¬ (ℓ.attachedTo ∈ A.vertices)) := by
    rw [← hid, ← Multiset.map_add, Multiset.filter_add_not]
  rw [hsplit, add_comm] at hle
  have hstep : δ.externalLegs ≤ G.externalLegs.filter (fun ℓ => ¬ (ℓ.attachedTo ∈ A.vertices)) := by
    apply multiset_le_of_le_add_of_notMem hle
    intro ℓ hℓ hcontra
    obtain ⟨ℓ'', hℓ''f, hℓ''eq⟩ := Multiset.mem_map.mp hcontra
    have hmemA : ℓ''.attachedTo ∈ A.vertices := (Multiset.mem_filter.mp hℓ''f).2
    have hstarmem : ℓ.attachedTo ∈ A.starVertices starOf := by
      rw [← hℓ''eq]
      show (A.retargetExternalLeg starOf ℓ'').attachedTo ∈ A.starVertices starOf
      unfold ResolvedAdmissibleSubgraph.retargetExternalLeg
      rw [ResolvedExternalLeg.retarget_attachedTo]
      exact retargetVertex_mem_starVertices A starOf hmemA
    exact (Finset.disjoint_left.mp hstar (δ.legs_supported ℓ hℓ)) hstarmem
  exact le_trans hstep (Multiset.filter_le _ _)

/-- **R-6c-body-337 — star-avoiding internal-edges support.**  A star-avoiding `δ`'s edges draw only from
the identity (off-`A`) complement edges, hence sit among `G`'s internal edges. -/
theorem starAvoiding_internalEdges_le (A : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (δ : ResolvedFeynmanSubgraph (A.contractWithStars starOf))
    (hstar : Disjoint δ.vertices (A.starVertices starOf)) :
    δ.internalEdges ≤ G.internalEdges := by
  have hle : δ.internalEdges ≤ A.complementEdges.map (A.retargetEdge starOf) := by
    have h := δ.internalEdges_le
    rwa [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at h
  -- the retarget is the identity on edges with both endpoints off `A`
  have hid : (A.complementEdges.filter (fun e => ¬ (e.source ∈ A.vertices ∨ e.target ∈ A.vertices))).map
        (A.retargetEdge starOf)
      = A.complementEdges.filter (fun e => ¬ (e.source ∈ A.vertices ∨ e.target ∈ A.vertices)) := by
    conv_rhs => rw [← Multiset.map_id
      (A.complementEdges.filter (fun e => ¬ (e.source ∈ A.vertices ∨ e.target ∈ A.vertices)))]
    apply Multiset.map_congr rfl
    intro e he
    have hnm := (Multiset.mem_filter.mp he).2
    rw [not_or] at hnm
    unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
    rw [A.retargetVertex_of_not_mem starOf hnm.1, A.retargetVertex_of_not_mem starOf hnm.2]
    rfl
  have hsplit : A.complementEdges.map (A.retargetEdge starOf)
      = (A.complementEdges.filter (fun e => e.source ∈ A.vertices ∨ e.target ∈ A.vertices)).map
          (A.retargetEdge starOf)
        + A.complementEdges.filter (fun e => ¬ (e.source ∈ A.vertices ∨ e.target ∈ A.vertices)) := by
    rw [← hid, ← Multiset.map_add, Multiset.filter_add_not]
  rw [hsplit, add_comm] at hle
  have hstep : δ.internalEdges
      ≤ A.complementEdges.filter (fun e => ¬ (e.source ∈ A.vertices ∨ e.target ∈ A.vertices)) := by
    apply multiset_le_of_le_add_of_notMem hle
    intro e he hcontra
    obtain ⟨e'', he''f, he''eq⟩ := Multiset.mem_map.mp hcontra
    have hq : e''.source ∈ A.vertices ∨ e''.target ∈ A.vertices := (Multiset.mem_filter.mp he''f).2
    have hstarmem : e.source ∈ A.starVertices starOf ∨ e.target ∈ A.starVertices starOf := by
      rw [← he''eq]
      unfold ResolvedAdmissibleSubgraph.retargetEdge
      rw [ResolvedFeynmanEdge.retarget_source, ResolvedFeynmanEdge.retarget_target]
      cases hq with
      | inl h => exact Or.inl (retargetVertex_mem_starVertices A starOf h)
      | inr h => exact Or.inr (retargetVertex_mem_starVertices A starOf h)
    obtain ⟨hs, ht⟩ := δ.edges_supported e he
    cases hstarmem with
    | inl h => exact (Finset.disjoint_left.mp hstar hs) h
    | inr h => exact (Finset.disjoint_left.mp hstar ht) h
  refine le_trans hstep (le_trans (Multiset.filter_le _ _) ?_)
  unfold ResolvedAdmissibleSubgraph.complementEdges
  exact tsub_le_self

/-- **R-6c-body-337 — the concrete `componentToRight`.**  A star-avoiding survivor `δ ∈ rightDomain z`
re-embedded straight into `G` with its own data (no de-contraction). -/
noncomputable def rightReembed (z : ForestBlockCodType D G) (δ : {x // x ∈ rightDomain z}) :
    ResolvedFeynmanSubgraph G :=
  δ.1.reembed
    (starAvoiding_vertices_subset z.1.1 (D.starOf G z.1.1) δ.1 (Finset.mem_filter.mp δ.2).2)
    (starAvoiding_internalEdges_le z.1.1 (D.starOf G z.1.1) δ.1 (Finset.mem_filter.mp δ.2).2)
    (starAvoiding_externalLegs_le z.1.1 (D.starOf G z.1.1) δ.1 (Finset.mem_filter.mp δ.2).2)

@[simp] theorem rightReembed_vertices (z : ForestBlockCodType D G) (δ : {x // x ∈ rightDomain z}) :
    (rightReembed z δ).vertices = δ.1.vertices := rfl

/-- **R-6c-body-337 — the concrete right-region supply.**  The three right fields of body-277's
`ResolvedRegionConstructionFromSectorValueSupply`, isolated as a stand-alone concretely-inhabited record. -/
structure ResolvedConcreteRightRegionValueSupply (D : ResolvedCoproductProperForestData) where
  /-- A star-avoiding survivor pulled back to its source outer component. -/
  componentToRight : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x // x ∈ rightDomain z} → ResolvedFeynmanSubgraph G
  /-- Each recovered right component is connected-divergent. -/
  rightComponentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ rightDomain z}), (componentToRight z δ).forget.IsConnectedDivergent
  /-- The recovered right components are pairwise disjoint. -/
  rightComponentDisjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ ⦃γ⦄, γ ∈ (rightDomain z).attach.image (componentToRight z) →
    ∀ ⦃δ⦄, δ ∈ (rightDomain z).attach.image (componentToRight z) → γ ≠ δ → γ.Disjoint δ

/-- **R-6c-body-337 — the concrete inhabitant.**  `componentToRight := rightReembed` (LIGHT survivor
re-embedding); CD via `reembed_forget_isConnectedDivergent`; disjointness from `z.2.1.pairwiseDisjoint`
(the re-embedding keeps vertices). -/
noncomputable def resolvedConcreteRightRegion (D : ResolvedCoproductProperForestData) :
    ResolvedConcreteRightRegionValueSupply D where
  componentToRight := fun z δ => rightReembed z δ
  rightComponentCD := fun z δ =>
    reembed_forget_isConnectedDivergent δ.1 _ _ _
      (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1)
  rightComponentDisjoint := fun z => by
    intro γ hγ δ hδ hne
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hγ
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hδ
    by_cases hab : a.1 = b.1
    · exact absurd (ResolvedFeynmanSubgraph.ext
        (by show a.1.vertices = b.1.vertices; rw [hab])
        (by show a.1.internalEdges = b.1.internalEdges; rw [hab])
        (by show a.1.externalLegs = b.1.externalLegs; rw [hab])) hne
    · show a.1.Disjoint b.1
      exact z.2.1.pairwiseDisjoint (Finset.mem_filter.mp a.2).1 (Finset.mem_filter.mp b.2).1 hab

end GaugeGeometry.QFT.Combinatorial
