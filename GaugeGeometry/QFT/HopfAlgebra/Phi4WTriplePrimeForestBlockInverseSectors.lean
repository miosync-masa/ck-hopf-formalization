import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeForestBlockSectors

/-!
# QFT-R1-body-608 — arbitrary-codomain inverse sectors + touchedOuter ownership

Body-607 fixed the forest-block FORWARD map and the component correspondence `componentEquiv s`.  That
equivalence already KNOWS the source split choice `s`.  To invert the forest-block map one must recover the
source data from an ARBITRARY codomain pair `z = (A, B)` WITHOUT reading any `s`.  This body therefore builds
the **source-independent inverse geometry root**, all as functions of an explicit

```
z : Σ A : {A // A ∈ phi4WTriplePrimeIndex G},
      {B // B ∈ phi4WTriplePrimeIndex ((A.1).contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))}
```

* **Step 1** — the source-independent star classifier `phi4WTriplePrime_inv_isForestImage z δ` (reads only
  `z`), its exclusive partition, and a forward-consistency anchor certifying it agrees with 607's classifier.
* **Step 2** — touchedOuter recovery: the `touchedOuterComponents` finset + `touchedOuterForest`, and the
  VICTORY iff `inv_isForestImage ↔ touchedOuterComponents.Nonempty`.
* **Step 3** — owner coherence: each outer component's star touches AT MOST ONE `δ`
  (`touchedOuter_unique`), whence the two touched outer forests of distinct `δ`s have DISJOINT element sets.
* **Step 4** — the load-bearing STAR-FREE right recovery: a star-free `δ` (a component of `B` on the quotient
  `Q`) is fully `G`-native, so it re-embeds back to a `ResolvedFeynmanSubgraph G` with a RAW round-trip;
  its `G`-side connected-divergence is proved by an explicit degree recovery (`boundaryEdgeCount`
  preservation under the star-free retarget), and its external-leg saturation + internal-edge completeness
  in `G` are re-derived clean.
* **Step 5** — the forest-case decontraction INPUT is packaged as a `Prop`-structure with NO parent / inner
  forest field (that is deferred to body-609), then the body HALTS.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in ANY
declaration's type (the survivor-embed stack / `resolvedComponentGen` / polluted supply lemmas are NOT
consumed — the reverse-direction degree machinery is re-derived clean).  No `componentEquiv` / `s`-indexed
607 construction inside any inverse definition (circularity).  No global inverse split choice, no whole
forest-block `Equiv`, no parent / inner-forest, no `sum_bij` / alpha / coassoc.  NO strict cross-presentation
star equality — only canonical star freshness/injectivity.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst608 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-- Abbreviation for the arbitrary codomain pair `z` (the forward map's target). -/
abbrev Phi4WTriplePrimeInverseCodomain (G : ResolvedFeynmanGraph) : Type :=
  Σ A : {A // A ∈ phi4WTriplePrimeIndex G},
    {B // B ∈ phi4WTriplePrimeIndex
      ((A.1).contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G A.1))}

/-! ## Reusable clean engine — star freshness, retarget preimage, and δ-membership fixing -/

/-- **body-608 (engine) — the canonical star of a proper forest `A` is fresh** (outside `G`), source
independent (any `A : ResolvedAdmissibleSubgraph G`, `A.IsProperForest`).  Clean re-derivation via
`cleanStarOfTotal` / `cleanStarOf_not_mem_vertices`. -/
theorem phi4WTriplePrime_inv_star_not_mem_vertices (A : ResolvedAdmissibleSubgraph G)
    (hApf : A.IsProperForest) {γ : ResolvedFeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    phi4WTriplePrimeCanonicalSupply.starOf G A γ ∉ G.vertices := by
  have hEq : phi4WTriplePrimeCanonicalSupply.starOf G A γ
      = cleanStarOf phi4DivergenceMeasureFamily A hApf γ := by
    show cleanStarOfTotal phi4DivergenceMeasureFamily G A γ = _
    unfold cleanStarOfTotal
    rw [dif_pos hApf]
  rw [hEq]
  exact cleanStarOf_not_mem_vertices A hApf hγ

/-- **body-608 (engine) — a retarget value landing back in `G` is FIXED.**  Since the canonical star is
fresh, `A.retargetVertex starOf w ∈ G.vertices` forces `w ∉ A.vertices`, so the retarget is the identity. -/
theorem phi4WTriplePrime_inv_retargetVertex_preimage (A : ResolvedAdmissibleSubgraph G)
    (hApf : A.IsProperForest) {w : VertexId}
    (hmem : A.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G A) w ∈ G.vertices) :
    A.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G A) w = w := by
  by_cases hwA : w ∈ A.vertices
  · exfalso
    have hval : A.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G A) w
        = phi4WTriplePrimeCanonicalSupply.starOf G A (A.componentAt hwA) := by
      simp only [ResolvedAdmissibleSubgraph.retargetVertex, A.componentAt?_of_mem hwA]
    rw [hval] at hmem
    exact phi4WTriplePrime_inv_star_not_mem_vertices A hApf (A.componentAt_mem hwA) hmem
  · exact A.retargetVertex_of_not_mem _ hwA

/-- **body-608 (engine) — the retarget FIXES membership in a `G`-native set `D` disjoint from `A`.**  For
`D ⊆ G.vertices` disjoint from `A.vertices`: `A`-vertices go to fresh stars (outside `D`) and are outside `D`
themselves; non-`A` vertices are fixed.  (Reverse-direction analogue of body-603's `retargetVertex_mem_iff`,
re-derived clean.) -/
theorem phi4WTriplePrime_inv_retargetVertex_mem_iff (A : ResolvedAdmissibleSubgraph G)
    (hApf : A.IsProperForest) {D : Finset VertexId} (hdisj : Disjoint D A.vertices)
    (hsub : D ⊆ G.vertices) (v : VertexId) :
    A.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G A) v ∈ D ↔ v ∈ D := by
  by_cases hvA : v ∈ A.vertices
  · have hval : A.retargetVertex (phi4WTriplePrimeCanonicalSupply.starOf G A) v
        = phi4WTriplePrimeCanonicalSupply.starOf G A (A.componentAt hvA) := by
      simp only [ResolvedAdmissibleSubgraph.retargetVertex, A.componentAt?_of_mem hvA]
    rw [hval]
    constructor
    · intro hmem
      exact absurd (hsub hmem)
        (phi4WTriplePrime_inv_star_not_mem_vertices A hApf (A.componentAt_mem hvA))
    · intro hmem
      exact absurd hmem (Finset.disjoint_right.mp hdisj hvA)
  · rw [A.retargetVertex_of_not_mem _ hvA]

/-! ## Step 1 — source-independent sector classification -/

/-- **body-608 (Step 1) — the source-independent star classifier.**  A component `δ` of `B` (on the quotient
`Q`) is a "forest image" iff one of its vertices lies on the outer forest `A`'s canonical star carrier.
Reads only `z` — never any split choice `s`. -/
def phi4WTriplePrime_inv_isForestImage (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop :=
  ∃ v ∈ δ.1.vertices, v ∈ z.1.1.starVertices (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)

/-- **body-608 (Step 1) — the star-TOUCHING sector** (a forest image). -/
def phi4WTriplePrime_StarTouchingComponent (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop :=
  phi4WTriplePrime_inv_isForestImage z δ

/-- **body-608 (Step 1) — the star-FREE sector** (not a forest image). -/
def phi4WTriplePrime_StarFreeComponent (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop :=
  ¬ phi4WTriplePrime_inv_isForestImage z δ

/-- **body-608 (Step 1) — the exclusive partition** into star-touching / star-free. -/
theorem phi4WTriplePrime_inv_sector_exclusive (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_StarTouchingComponent z δ ∨ phi4WTriplePrime_StarFreeComponent z δ :=
  em _

/-- **body-608 (Step 1) — mutual exclusion.** -/
theorem phi4WTriplePrime_inv_sector_not_both (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    ¬ (phi4WTriplePrime_StarTouchingComponent z δ ∧ phi4WTriplePrime_StarFreeComponent z δ) :=
  fun h => h.2 h.1

/-- **body-608 (Step 1) — forward-consistency anchor** (BANK — not used inside any inverse definition).  When
`z = forestBlockForward s`, the source-independent classifier agrees with body-607's `s`-indexed classifier
(both unfold to the same star-incidence on `selectedOuter s`). -/
theorem phi4WTriplePrime_inv_isForestImage_forward
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (δ : {x // x ∈ (phi4WTriplePrime_forestBlockForward s).2.1.elements}) :
    phi4WTriplePrime_inv_isForestImage (phi4WTriplePrime_forestBlockForward s) δ ↔
      phi4WTriplePrime_isForestImage s δ := Iff.rfl

/-! ## Step 2 — touchedOuter recovery -/

/-- **body-608 (Step 2) — the touched outer components** of `δ`: the outer components whose canonical star
lands inside `δ`.  Multiplicity / ID preserved. -/
noncomputable def phi4WTriplePrime_touchedOuterComponents (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Finset {γ // γ ∈ z.1.1.elements} :=
  z.1.1.elements.attach.filter
    (fun γ => phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ.1 ∈ δ.1.vertices)

/-- **body-608 (Step 2) — the touched outer forest** of `δ`: the sub-forest of `A` cut out by the same
predicate (CD + disjointness inherited from `A`). -/
noncomputable def phi4WTriplePrime_touchedOuterForest (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : ResolvedAdmissibleSubgraph G :=
  z.1.1.filterElements
    (fun γ => phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices)

@[simp] theorem phi4WTriplePrime_touchedOuterForest_elements (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) :
    (phi4WTriplePrime_touchedOuterForest z δ).elements
      = z.1.1.elements.filter
          (fun γ => phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices) :=
  ResolvedAdmissibleSubgraph.filterElements_elements _ _

/-- **body-608 (Step 2, VICTORY) — the classifier IS touched-outer nonemptiness.**  A star vertex in `δ`
means some outer component `γ` has `starOf γ ∈ δ.vertices`, i.e. `γ` is a touched outer component. -/
theorem phi4WTriplePrime_isForestImage_iff_touchedNonempty
    (z : Phi4WTriplePrimeInverseCodomain G) (δ : {x // x ∈ z.2.1.elements}) :
    phi4WTriplePrime_inv_isForestImage z δ ↔
      (phi4WTriplePrime_touchedOuterComponents z δ).Nonempty := by
  constructor
  · rintro ⟨v, hv, hstar⟩
    obtain ⟨γ, hγ, hγv⟩ := ResolvedAdmissibleSubgraph.mem_starVertices.mp hstar
    refine ⟨⟨γ, hγ⟩, ?_⟩
    simp only [phi4WTriplePrime_touchedOuterComponents, Finset.mem_filter]
    exact ⟨Finset.mem_attach _ _, by rw [hγv]; exact hv⟩
  · rintro ⟨⟨γ, hγ⟩, hmem⟩
    simp only [phi4WTriplePrime_touchedOuterComponents, Finset.mem_filter] at hmem
    exact ⟨_, hmem.2, ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨γ, hγ, rfl⟩⟩

/-! ## Step 3 — owner coherence

A star-touching `δ` may carry MULTIPLE outer stars, so there is NO unique outer OWNER — the touched outer
FOREST is the owner.  We therefore build NO `uniqueOuterOwner`; instead each outer component's star touches
AT MOST ONE `δ`, whence the touched outer forests of distinct `δ`s have disjoint element sets. -/

/-- **body-608 (Step 3) — each outer component's star touches AT MOST ONE `δ`.**  `starOf γ` in both `δ₁`,
`δ₂` meets their vertex sets, but `B`'s components are pairwise disjoint, forcing `δ₁ = δ₂`. -/
theorem phi4WTriplePrime_touchedOuter_unique (z : Phi4WTriplePrimeInverseCodomain G)
    {γ : ResolvedFeynmanSubgraph G} (_hγ : γ ∈ z.1.1.elements)
    {δ₁ δ₂ : {x // x ∈ z.2.1.elements}}
    (h₁ : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ₁.1.vertices)
    (h₂ : phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ₂.1.vertices) : δ₁ = δ₂ := by
  by_contra hne
  have hd : δ₁.1.Disjoint δ₂.1 :=
    z.2.1.pairwiseDisjoint δ₁.2 δ₂.2 (fun h => hne (Subtype.ext h))
  exact (Finset.disjoint_left.mp hd h₁) h₂

/-- **body-608 (Step 3) — the two touched outer forests of distinct `δ`s have DISJOINT element sets.**  A
shared `γ` would have `starOf γ` in both `δ`s, forcing them equal (Step-3 uniqueness) — contradiction. -/
theorem phi4WTriplePrime_touchedOuterForest_disjoint (z : Phi4WTriplePrimeInverseCodomain G)
    {δ₁ δ₂ : {x // x ∈ z.2.1.elements}} (hne : δ₁ ≠ δ₂) :
    Disjoint (phi4WTriplePrime_touchedOuterForest z δ₁).elements
      (phi4WTriplePrime_touchedOuterForest z δ₂).elements := by
  rw [phi4WTriplePrime_touchedOuterForest_elements, phi4WTriplePrime_touchedOuterForest_elements,
    Finset.disjoint_left]
  intro γ hγ₁ hγ₂
  rw [Finset.mem_filter] at hγ₁ hγ₂
  exact hne (phi4WTriplePrime_touchedOuter_unique z hγ₁.1 hγ₁.2 hγ₂.2)

/-! ## Step 4 — star-free right recovery (the load-bearing recovery) -/

/-- **body-608 (Step 4) — a star-free `δ` sits inside `G`.**  Its vertices lie in `Q = (G∖A) ∪ star(A)`, and
star-freeness removes the star part, leaving `G.vertices ∖ A.vertices ⊆ G.vertices`. -/
theorem phi4WTriplePrime_inv_recoveredRight_vertices_subset
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) : δ.1.vertices ⊆ G.vertices := by
  intro v hv
  have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
    δ.1.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
  rcases hvQ with h | h
  · exact (Finset.mem_sdiff.mp h).1
  · exact absurd ⟨v, hv, h⟩ hfree

/-- **body-608 (Step 4) — a star-free `δ` is disjoint from the outer forest `A`.** -/
theorem phi4WTriplePrime_inv_recoveredRight_disjoint
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    Disjoint δ.1.vertices z.1.1.vertices := by
  rw [Finset.disjoint_left]
  intro v hv hvA
  have hvQ : v ∈ (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)).vertices :=
    δ.1.vertices_subset hv
  rw [ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union] at hvQ
  rcases hvQ with h | h
  · exact (Finset.mem_sdiff.mp h).2 hvA
  · exact absurd ⟨v, hv, h⟩ hfree

/-- **body-608 (Step 4) — a star-free `δ`'s internal edges are genuine `G`-edges.**  Every `δ`-edge is
`r`-fixed with a `G`-native pre-image (freshness of `A`'s stars rules out star pre-images), so it lies in
`A.complementEdges ⊆ G.internalEdges`.  Count-level re-derivation (clean). -/
theorem phi4WTriplePrime_inv_recoveredRight_internalEdges_le
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) : δ.1.internalEdges ≤ G.internalEdges := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hsub : δ.1.vertices ⊆ G.vertices :=
    phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree
  have hdisj : Disjoint δ.1.vertices A.vertices :=
    phi4WTriplePrime_inv_recoveredRight_disjoint z hfree
  rw [Multiset.le_iff_count]
  intro e
  by_cases he : e ∈ δ.1.internalEdges
  · obtain ⟨hsE, htE⟩ := δ.1.edges_supported e he
    have hsG : e.source ∈ G.vertices := hsub hsE
    have htG : e.target ∈ G.vertices := hsub htE
    have hsA : e.source ∉ A.vertices := Finset.disjoint_left.mp hdisj hsE
    have htA : e.target ∉ A.vertices := Finset.disjoint_left.mp hdisj htE
    have hre : A.retargetEdge starOf e = e := by
      unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
      rw [A.retargetVertex_of_not_mem starOf hsA, A.retargetVertex_of_not_mem starOf htA]
    have hcm : Multiset.count e (A.complementEdges.map (A.retargetEdge starOf))
        = Multiset.count e A.complementEdges := by
      conv_rhs => rw [← Multiset.map_id A.complementEdges]
      rw [Multiset.count_map, Multiset.count_map]
      refine congrArg _ (Multiset.filter_congr (fun e₀ _ => ?_))
      simp only [id_eq]
      constructor
      · intro heq
        have h1 : A.retargetVertex starOf e₀.source ∈ G.vertices := by
          have hsrc := congrArg ResolvedFeynmanEdge.source heq
          simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_source] at hsrc
          rw [← hsrc]; exact hsG
        have h2 : A.retargetVertex starOf e₀.target ∈ G.vertices := by
          have htrg := congrArg ResolvedFeynmanEdge.target heq
          simp only [ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget_target] at htrg
          rw [← htrg]; exact htG
        have hs0 := phi4WTriplePrime_inv_retargetVertex_preimage A hApf h1
        have ht0 := phi4WTriplePrime_inv_retargetVertex_preimage A hApf h2
        have hfix : A.retargetEdge starOf e₀ = e₀ := by
          unfold ResolvedAdmissibleSubgraph.retargetEdge ResolvedFeynmanEdge.retarget
          rw [hs0, ht0]
        exact heq.trans hfix
      · intro heq
        subst heq
        exact hre.symm
    calc Multiset.count e δ.1.internalEdges
        ≤ Multiset.count e (A.contractWithStars starOf).internalEdges :=
          Multiset.le_iff_count.mp δ.1.internalEdges_le e
      _ = Multiset.count e (A.complementEdges.map (A.retargetEdge starOf)) := by
          rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
      _ = Multiset.count e A.complementEdges := hcm
      _ ≤ Multiset.count e G.internalEdges :=
          Multiset.le_iff_count.mp (Multiset.sub_le_self G.internalEdges A.internalEdges) e
  · rw [Multiset.count_eq_zero_of_notMem he]; exact Nat.zero_le _

/-- **body-608 (Step 4) — a star-free `δ`'s external legs are genuine `G`-legs.**  Same reverse-retarget-fixed
argument; the retarget fixes each `δ`-leg's `G`-native attachment. -/
theorem phi4WTriplePrime_inv_recoveredRight_externalLegs_le
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) : δ.1.externalLegs ≤ G.externalLegs := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hsub : δ.1.vertices ⊆ G.vertices :=
    phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree
  have hdisj : Disjoint δ.1.vertices A.vertices :=
    phi4WTriplePrime_inv_recoveredRight_disjoint z hfree
  rw [Multiset.le_iff_count]
  intro ℓ
  by_cases hℓ : ℓ ∈ δ.1.externalLegs
  · have hatt : ℓ.attachedTo ∈ δ.1.vertices := δ.1.legs_supported ℓ hℓ
    have hattA : ℓ.attachedTo ∉ A.vertices := Finset.disjoint_left.mp hdisj hatt
    have hrl : A.retargetExternalLeg starOf ℓ = ℓ := by
      unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
      rw [A.retargetVertex_of_not_mem starOf hattA]
    have hclm : Multiset.count ℓ (G.externalLegs.map (A.retargetExternalLeg starOf))
        = Multiset.count ℓ G.externalLegs := by
      conv_rhs => rw [← Multiset.map_id G.externalLegs]
      rw [Multiset.count_map, Multiset.count_map]
      refine congrArg _ (Multiset.filter_congr (fun ℓ₀ _ => ?_))
      simp only [id_eq]
      constructor
      · intro heq
        have h1 : A.retargetVertex starOf ℓ₀.attachedTo ∈ G.vertices := by
          have hat := congrArg ResolvedExternalLeg.attachedTo heq
          simp only [ResolvedAdmissibleSubgraph.retargetExternalLeg,
            ResolvedExternalLeg.retarget_attachedTo] at hat
          rw [← hat]; exact hsub hatt
        have hf0 := phi4WTriplePrime_inv_retargetVertex_preimage A hApf h1
        have hfix : A.retargetExternalLeg starOf ℓ₀ = ℓ₀ := by
          unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
          rw [hf0]
        exact heq.trans hfix
      · intro heq
        subst heq
        exact hrl.symm
    calc Multiset.count ℓ δ.1.externalLegs
        ≤ Multiset.count ℓ (A.contractWithStars starOf).externalLegs :=
          Multiset.le_iff_count.mp δ.1.externalLegs_le ℓ
      _ = Multiset.count ℓ (G.externalLegs.map (A.retargetExternalLeg starOf)) := by
          rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs]
      _ = Multiset.count ℓ G.externalLegs := hclm
  · rw [Multiset.count_eq_zero_of_notMem hℓ]; exact Nat.zero_le _

/-- **body-608 (Step 4, HEADLINE) — the recovered right component.**  A star-free `δ` (a subgraph of the
quotient `Q`) recovered as a subgraph of `G`, with the SAME data (via the instance-free
`ResolvedFeynmanSubgraph.reembed`), the supports supplied by the two reverse-direction lemmas above. -/
noncomputable def phi4WTriplePrime_recoveredRight (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    ResolvedFeynmanSubgraph G :=
  δ.1.reembed
    (phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree)
    (phi4WTriplePrime_inv_recoveredRight_internalEdges_le z hfree)
    (phi4WTriplePrime_inv_recoveredRight_externalLegs_le z hfree)

@[simp] theorem phi4WTriplePrime_recoveredRight_vertices (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).vertices = δ.1.vertices := rfl

@[simp] theorem phi4WTriplePrime_recoveredRight_internalEdges (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).internalEdges = δ.1.internalEdges := rfl

@[simp] theorem phi4WTriplePrime_recoveredRight_externalLegs (z : Phi4WTriplePrimeInverseCodomain G)
    {δ : {x // x ∈ z.2.1.elements}} (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).externalLegs = δ.1.externalLegs := rfl

/-- **body-608 (Step 4) — the RAW round-trip.**  The recovered right component carries `δ`'s intrinsic
resolved graph (same data), so recovering then re-reading the intrinsic graph returns `δ`'s — a RAW graph
equality (achievable because a star-free `δ` is fully `G`-native; no drop to a class equality is needed). -/
@[simp] theorem phi4WTriplePrime_recoveredRight_toResolvedFeynmanGraph
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).toResolvedFeynmanGraph = δ.1.toResolvedFeynmanGraph := rfl

/-- **body-608 (Step 4, CRUX) — the recovered right's induced boundary count equals `δ`'s.**  Reverse of
body-603's survivor boundary calculation: the star-free retarget fixes every `δ`-endpoint and sends
`A`-endpoints to fresh stars outside `δ`, so an edge is a `δ`-boundary edge in `G` iff it was in `Q` — and
the retarget is cardinality-preserving.  Re-derived clean; NO ambient-invariance class. -/
theorem phi4WTriplePrime_inv_recoveredRight_boundaryEdgeCount_eq
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).forget.boundaryEdgeCount
      = δ.1.forget.boundaryEdgeCount := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  set r := A.retargetEdge starOf with hr
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hsub : δ.1.vertices ⊆ G.vertices :=
    phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree
  have hdisj : Disjoint δ.1.vertices A.vertices :=
    phi4WTriplePrime_inv_recoveredRight_disjoint z hfree
  set Bd : FeynmanEdge → Prop := δ.1.forget.IsBoundaryEdge with hBd
  -- δ-internal edges (both endpoints inside δ) fail Bd
  have hδfail : (δ.1.internalEdges.map ResolvedFeynmanEdge.forget).filter Bd = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e' he'
    obtain ⟨e, he, rfl⟩ := Multiset.mem_map.mp he'
    obtain ⟨hs, ht⟩ := δ.1.edges_supported e he
    simp only [hBd, FeynmanSubgraph.IsBoundaryEdge, ResolvedFeynmanSubgraph.forget_vertices,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact h ht
    · exact h hs
  -- A-internal edges (both endpoints inside A, hence outside δ) fail Bd
  have hAfail : (A.internalEdges.filter (fun e => Bd e.forget)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨hsA, htA⟩ : e.source ∈ A.vertices ∧ e.target ∈ A.vertices := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
      obtain ⟨δ', hδ', heδ⟩ := he
      obtain ⟨hsδ, htδ⟩ := δ'.edges_supported e heδ
      exact ⟨ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ', hδ', hsδ⟩,
        ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ', hδ', htδ⟩⟩
    have hsδ : e.source ∉ δ.1.vertices := Finset.disjoint_right.mp hdisj hsA
    have htδ : e.target ∉ δ.1.vertices := Finset.disjoint_right.mp hdisj htA
    simp only [hBd, FeynmanSubgraph.IsBoundaryEdge, ResolvedFeynmanSubgraph.forget_vertices,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact hsδ h
    · exact htδ h
  -- the recovered right's boundary edges = the Bd-filter of the ambient G internal edges
  have hRbd : (phi4WTriplePrime_recoveredRight z hfree).forget.boundaryEdges
      = (G.internalEdges.map ResolvedFeynmanEdge.forget).filter Bd := by
    show (G.forget.internalEdges
        - (phi4WTriplePrime_recoveredRight z hfree).forget.internalEdges).filter Bd = _
    simp only [ResolvedFeynmanGraph.forget_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges,
      phi4WTriplePrime_recoveredRight_internalEdges]
    rw [Multiset.filter_sub, hδfail, Multiset.sub_zero]
  -- δ's boundary edges = the Bd-filter of the retargeted complement edges
  have hδbd : δ.1.forget.boundaryEdges
      = ((A.complementEdges.map r).map ResolvedFeynmanEdge.forget).filter Bd := by
    show ((A.contractWithStars starOf).forget.internalEdges - δ.1.forget.internalEdges).filter Bd = _
    simp only [ResolvedFeynmanGraph.forget_internalEdges, ResolvedFeynmanSubgraph.forget_internalEdges,
      ResolvedAdmissibleSubgraph.contractWithStars_internalEdges]
    rw [Multiset.filter_sub, hδfail, Multiset.sub_zero]
  -- assemble the counts
  unfold FeynmanSubgraph.boundaryEdgeCount
  rw [hRbd, hδbd, Multiset.map_map, Multiset.filter_map, Multiset.filter_map,
    Multiset.card_map, Multiset.card_map]
  simp only [Function.comp]
  -- retarget preserves δ-boundary-ness on the complement edges
  have hpred : ∀ e ∈ A.complementEdges, Bd (r e).forget ↔ Bd e.forget := by
    intro e _
    have hs := phi4WTriplePrime_inv_retargetVertex_mem_iff A hApf hdisj hsub e.source
    have ht := phi4WTriplePrime_inv_retargetVertex_mem_iff A hApf hdisj hsub e.target
    simp only [hBd, hr, ResolvedAdmissibleSubgraph.retargetEdge, FeynmanSubgraph.IsBoundaryEdge,
      ResolvedFeynmanSubgraph.forget_vertices, ResolvedFeynmanEdge.forget_retarget,
      ResolvedFeynmanEdge.forget_source, ResolvedFeynmanEdge.forget_target]
    rw [hs, ht]
  rw [Multiset.filter_congr hpred]
  congr 1
  show G.internalEdges.filter (fun e => Bd e.forget)
      = (G.internalEdges - A.internalEdges).filter (fun e => Bd e.forget)
  rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]

/-- **body-608 (Step 4) — the recovered right's φ⁴ physical external valence equals `δ`'s.** -/
theorem phi4WTriplePrime_inv_recoveredRight_physicalExternalLegCount_eq
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).forget.physicalExternalLegCount
      = δ.1.forget.physicalExternalLegCount := by
  have hleg : (phi4WTriplePrime_recoveredRight z hfree).forget.externalLegs.card
      = δ.1.forget.externalLegs.card := rfl
  unfold FeynmanSubgraph.physicalExternalLegCount FeynmanSubgraph.externalLegCount
  rw [phi4WTriplePrime_inv_recoveredRight_boundaryEdgeCount_eq z hfree, hleg]

/-- **body-608 (Step 4, VICTORY) — the recovered right component is φ⁴ connected-divergent on `G`.**
Connectivity + 1PI transport definitionally (shared intrinsic graph); divergence transports through the
degree equality via the explicit φ⁴ criterion — NO ambient-invariance class. -/
theorem phi4WTriplePrime_inv_recoveredRight_isConnectedDivergent
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    (phi4WTriplePrime_recoveredRight z hfree).forget.IsConnectedDivergent := by
  have hCDδ : δ.1.forget.IsConnectedDivergent := z.2.1.isConnectedDivergent δ.1 δ.2
  refine ⟨hCDδ.1, hCDδ.2.1, ?_⟩
  have hpelc := phi4WTriplePrime_inv_recoveredRight_physicalExternalLegCount_eq z hfree
  have hdivδ : δ.1.forget.physicalExternalLegCount ≤ 4 :=
    (phi4_isDivergent_iff δ.1.forget).mp hCDδ.2.2
  exact (phi4_isDivergent_iff _).mpr (by rw [hpelc]; exact hdivδ)

/-- **body-608 (Step 4) — the recovered right is externally-leg saturated in `G`** (a W‴ leaf fact). -/
theorem phi4WTriplePrime_inv_recoveredRight_saturated
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    ResolvedExternalLegSaturated G (phi4WTriplePrime_recoveredRight z hfree) := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hsub : δ.1.vertices ⊆ G.vertices :=
    phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree
  have hdisj : Disjoint δ.1.vertices A.vertices :=
    phi4WTriplePrime_inv_recoveredRight_disjoint z hfree
  have hpred : ∀ ℓ ∈ G.externalLegs,
      (A.retargetExternalLeg starOf ℓ).attachedTo ∈ δ.1.vertices ↔ ℓ.attachedTo ∈ δ.1.vertices := by
    intro ℓ _
    show A.retargetVertex starOf ℓ.attachedTo ∈ δ.1.vertices ↔ ℓ.attachedTo ∈ δ.1.vertices
    exact phi4WTriplePrime_inv_retargetVertex_mem_iff A hApf hdisj hsub ℓ.attachedTo
  have hmapid : (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices)).map
      (A.retargetExternalLeg starOf) = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) := by
    conv_rhs => rw [← Multiset.map_id (G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices))]
    apply Multiset.map_congr rfl
    intro ℓ hℓ
    have hℓδ : ℓ.attachedTo ∈ δ.1.vertices := (Multiset.mem_filter.mp hℓ).2
    show A.retargetExternalLeg starOf ℓ = id ℓ
    unfold ResolvedAdmissibleSubgraph.retargetExternalLeg ResolvedExternalLeg.retarget
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hℓδ)]
    rfl
  have hδsat : (A.contractWithStars starOf).externalLegs.filter
      (fun ℓ => ℓ.attachedTo ∈ δ.1.vertices) ≤ δ.1.externalLegs :=
    (((mem_phi4WTriplePrimeIndex (A.contractWithStars starOf) z.2.1).mp z.2.2).2.2.2.2.2.1) δ.1 δ.2
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.filter_map] at hδsat
  simp only [Function.comp] at hδsat
  rw [Multiset.filter_congr hpred, hmapid] at hδsat
  show G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (phi4WTriplePrime_recoveredRight z hfree).vertices)
      ≤ (phi4WTriplePrime_recoveredRight z hfree).externalLegs
  simpa only [phi4WTriplePrime_recoveredRight_vertices, phi4WTriplePrime_recoveredRight_externalLegs]
    using hδsat

/-- **body-608 (Step 4) — the recovered right is internal-edge complete in `G`** (a W‴ leaf fact). -/
theorem phi4WTriplePrime_inv_recoveredRight_edgeComplete
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hfree : ¬ phi4WTriplePrime_inv_isForestImage z δ) :
    ResolvedInternalEdgeComplete (phi4WTriplePrime_recoveredRight z hfree) := by
  set A := z.1.1 with hAdef
  set starOf := phi4WTriplePrimeCanonicalSupply.starOf G A with hstardef
  set r := A.retargetEdge starOf with hr
  have hApf : A.IsProperForest := ((mem_phi4WTriplePrimeIndex G A).mp z.1.2).2.2.2.2.1
  have hsub : δ.1.vertices ⊆ G.vertices :=
    phi4WTriplePrime_inv_recoveredRight_vertices_subset z hfree
  have hdisj : Disjoint δ.1.vertices A.vertices :=
    phi4WTriplePrime_inv_recoveredRight_disjoint z hfree
  set P : ResolvedFeynmanEdge → Prop :=
    fun e => e.source ∈ δ.1.vertices ∧ e.target ∈ δ.1.vertices with hP
  have hpred : ∀ e ∈ A.complementEdges, P (r e) ↔ P e := by
    intro e _
    have hs := phi4WTriplePrime_inv_retargetVertex_mem_iff A hApf hdisj hsub e.source
    have ht := phi4WTriplePrime_inv_retargetVertex_mem_iff A hApf hdisj hsub e.target
    simp only [hP, hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [hs, ht]
  have hmapid : (A.complementEdges.filter P).map r = A.complementEdges.filter P := by
    conv_rhs => rw [← Multiset.map_id (A.complementEdges.filter P)]
    apply Multiset.map_congr rfl
    intro e he
    obtain ⟨hsδ, htδ⟩ : P e := (Multiset.mem_filter.mp he).2
    show r e = id e
    simp only [hr, ResolvedAdmissibleSubgraph.retargetEdge, ResolvedFeynmanEdge.retarget]
    rw [A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj hsδ),
      A.retargetVertex_of_not_mem starOf (Finset.disjoint_left.mp hdisj htδ)]
    rfl
  have hAfail : A.internalEdges.filter P = 0 := by
    rw [Multiset.filter_eq_nil]
    intro e he
    obtain ⟨hsA, -⟩ : e.source ∈ A.vertices ∧ e.target ∈ A.vertices := by
      simp only [ResolvedAdmissibleSubgraph.internalEdges, Multiset.mem_sum] at he
      obtain ⟨δ', hδ', heδ⟩ := he
      obtain ⟨hsδ', htδ'⟩ := δ'.edges_supported e heδ
      exact ⟨ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ', hδ', hsδ'⟩,
        ResolvedAdmissibleSubgraph.mem_vertices.mpr ⟨δ', hδ', htδ'⟩⟩
    intro hPe
    exact (Finset.disjoint_right.mp hdisj hsA) hPe.1
  have hδEC : (A.contractWithStars starOf).internalEdges.filter P ≤ δ.1.internalEdges :=
    (((mem_phi4WTriplePrimeIndex (A.contractWithStars starOf) z.2.1).mp z.2.2).2.2.2.2.2.2) δ.1 δ.2
  rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges, Multiset.filter_map] at hδEC
  simp only [Function.comp] at hδEC
  rw [Multiset.filter_congr hpred, hmapid] at hδEC
  have hGeq : G.internalEdges.filter P = A.complementEdges.filter P := by
    show _ = (G.internalEdges - A.internalEdges).filter P
    rw [Multiset.filter_sub, hAfail, Multiset.sub_zero]
  show G.internalEdges.filter P ≤ δ.1.internalEdges
  rw [hGeq]
  exact hδEC

/-! ## Step 5 — forest-case decontraction input (package ONLY; NO parent / inner forest) -/

/-- **body-608 (Step 5) — the forest-case decontraction INPUT.**  For a star-touching `δ`, the inputs
body-609 will read to reconstruct the forest-case parent / inner forest — packaged with NO parent field and
NO inner-forest field (that reconstruction is deferred).  All fields are source-independent (functions of
`z` and `δ` only). -/
structure phi4WTriplePrime_ForestDecontractionInput (z : Phi4WTriplePrimeInverseCodomain G)
    (δ : {x // x ∈ z.2.1.elements}) : Prop where
  /-- `δ` is a live component of `B`. -/
  liveMem : δ.1 ∈ z.2.1.elements
  /-- `δ` is star-touching (a forest image). -/
  starTouching : phi4WTriplePrime_inv_isForestImage z δ
  /-- the touched outer components are nonempty (Step-2 victory + star-touching). -/
  touchedNonempty : (phi4WTriplePrime_touchedOuterComponents z δ).Nonempty
  /-- touched-owner coherence (Step 3): any outer component touching both `δ` and `δ'` forces `δ' = δ`. -/
  ownerCoherent : ∀ {γ : ResolvedFeynmanSubgraph G}, γ ∈ z.1.1.elements →
    ∀ {δ' : {x // x ∈ z.2.1.elements}},
      phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ.1.vertices →
      phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 γ ∈ δ'.1.vertices → δ' = δ
  /-- root ambient support of `G`. -/
  rootAmbientSupported : ResolvedAmbientSupported G
  /-- root edge-id uniqueness of `G`. -/
  rootEdgeIdsUnique : G.EdgeIdsUnique
  /-- root leg-id uniqueness of `G`. -/
  rootLegIdsUnique : G.LegIdsUnique
  /-- edge-completeness of `δ` (from `B`'s W‴ membership at `δ`). -/
  deltaEdgeComplete : ResolvedInternalEdgeComplete δ.1

/-- **body-608 (Step 5) — the forest-case input builder.**  For a star-touching `δ`, assemble the
decontraction input from the two W‴ index memberships (`A ∈ index G`, `B ∈ index Q`) and Steps 2–3.  Builds
NO parent and NO inner forest — the body HALTS here. -/
theorem phi4WTriplePrime_forestDecontractionInput_of_starTouching
    (z : Phi4WTriplePrimeInverseCodomain G) {δ : {x // x ∈ z.2.1.elements}}
    (hST : phi4WTriplePrime_inv_isForestImage z δ) :
    phi4WTriplePrime_ForestDecontractionInput z δ where
  liveMem := δ.2
  starTouching := hST
  touchedNonempty := (phi4WTriplePrime_isForestImage_iff_touchedNonempty z δ).mp hST
  ownerCoherent := by
    intro γ hγ δ' h₁ h₂
    exact phi4WTriplePrime_touchedOuter_unique z hγ h₂ h₁
  rootAmbientSupported := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).1
  rootEdgeIdsUnique := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.1
  rootLegIdsUnique := ((mem_phi4WTriplePrimeIndex G z.1.1).mp z.1.2).2.2.2.1
  deltaEdgeComplete :=
    (((mem_phi4WTriplePrimeIndex
      (z.1.1.contractWithStars (phi4WTriplePrimeCanonicalSupply.starOf G z.1.1)) z.2.1).mp
        z.2.2).2.2.2.2.2.2) δ.1 δ.2

end GaugeGeometry.QFT.Combinatorial
