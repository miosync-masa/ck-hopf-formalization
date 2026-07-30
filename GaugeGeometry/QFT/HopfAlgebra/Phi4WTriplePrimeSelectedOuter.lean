import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeCoproductOwner

/-!
# QFT-R1-body-602 — ungated root-relative selectedOuter

Body-601 threaded the fifth axis (vertex-induced internal-edge completeness) through the entire W‴
ownership chain and issued the **ungated** split-choice CD landing
`phi4EdgeCompleteSplitChoice_rootRelativeInner_isConnectedDivergent`: for every outer component `γ` of a
W‴ split choice and every externally-leg-saturated inner `δ` carrying its own component CD, the nested
root lift `rootRelativeInner γ δ` (which KEEPS the second-order boundary) is connected divergent on
`G.forget` — with NO external boundary-closed gate.

This body assembles the **selectedOuter admissible forest** of a W‴ filtered split choice by:

* Step 1 — the three-way partition of each outer component's choice: `Sum.inl true` → LEFT,
  `Sum.inl false` → RIGHT (dropped), `Sum.inr B` → FOREST (keep the live W‴ inner `B`).
* Step 2 — the stable promotion of each forest branch through `rootRelativeInner γ δ` (NOT the old
  `ResolvedAdmissibleSubgraph.promote` / `toResolvedFeynmanGraph`, which DISCARD the boundary).
* Step 3 — the promotion closure: every promoted `rootRelativeInner γ δ` is connected divergent,
  externally-leg-saturated, AND internal-edge complete on the root `G` (the two-stage edge-completeness
  transitivity `count e G.internalEdges ≤ count e γ.internalEdges ≤ count e δ.internalEdges`).
* Steps 4–5 — `phi4WTriplePrime_leftOf` / `phi4WTriplePrime_promotedOf` / `phi4WTriplePrime_cross`, the
  `selectedOuter := leftOf.union promotedOf cross`, and the HEADLINE `phi4WTriplePrime_selectedOuter_mem`
  landing back in `phi4WTriplePrimeIndex G` — the fifth axis is CLOSED under this internal operation, with
  NO external gate / `Measure` / `E` hypothesis.
* Step 6 — the origin anchors (`selectedOuter_elements`, `selectedOuter_component_origin`) for body-603.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `...ByAdmissibleForestContract` /
`IsDivergenceReflectedByAdmissibleForestContract`) in ANY declaration's type — the polluted aggregation
helpers (`internalEdges_le_of_mem` / `internalEdges_le_of_components_le` /
`complementEdges_card_pos_of_internalEdges_le` / `internalEdges_card_pos_of_isNonempty` /
`mem_internalEdges` / `multiset_count_finset_sum`) are NOT consumed; the ones needed are RE-DERIVED clean
here.  Promotion goes ONLY through `rootRelativeInner`; the old `promote` / `toResolvedFeynmanGraph` /
`selectedOuterRawOf` are FORBIDDEN.  No right survivor / remnant / corrected quotient / forest-block
bijection / alpha / coassoc.  The only divergence binders are the concrete `phi4DivergenceMeasureFamily` /
`phi4PermInvariantDivergenceMeasureFamily`.  No `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 0 — clean re-derivations of the (otherwise-polluted) aggregation helpers -/

/-- **body-602 (Step 0) — count of a Finset-indexed multiset sum, re-derived clean.**  (The library
`multiset_count_finset_sum` carries the forbidden-class section binders; this is the same fact with a clean
type.) -/
theorem phi4WTriplePrime_count_finset_sum (e : ResolvedFeynmanEdge)
    (S : Finset (ResolvedFeynmanSubgraph G)) :
    Multiset.count e (S.sum (fun γ => γ.internalEdges))
      = ∑ δ ∈ S, Multiset.count e δ.internalEdges := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Multiset.count_add, ih, Finset.sum_insert ha]

/-- **body-602 (Step 0) — the aggregate internal edges are bounded by any per-component bound, re-derived
clean.**  Pairwise-disjoint components share no edge, so the aggregate count at `e` is the single
containing component's, bounded by `M`.  (Clean re-derivation of `internalEdges_le_of_components_le`.) -/
theorem phi4WTriplePrime_internalEdges_le_of_components_le
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    {M : Multiset ResolvedFeynmanEdge}
    (h : ∀ γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A,
      γ.internalEdges ≤ M) :
    @ResolvedAdmissibleSubgraph.internalEdges phi4DivergenceMeasureFamily G A ≤ M := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rw [Multiset.le_iff_count]
  intro e
  have hCountSum : Multiset.count e A.internalEdges
      = ∑ δ ∈ A.elements, Multiset.count e δ.internalEdges :=
    phi4WTriplePrime_count_finset_sum e A.elements
  rw [hCountSum]
  by_cases hex : ∃ γ ∈ A.elements, 0 < Multiset.count e γ.internalEdges
  · obtain ⟨γ, hγ, hpos⟩ := hex
    have hcoll : (∑ δ ∈ A.elements, Multiset.count e δ.internalEdges)
        = Multiset.count e γ.internalEdges := by
      refine Finset.sum_eq_single γ ?_ (fun hγnot => absurd hγ hγnot)
      intro δ hδ hne
      by_contra hne0
      have hposδ : 0 < Multiset.count e δ.internalEdges := Nat.pos_of_ne_zero hne0
      have heδ : e ∈ δ.internalEdges := Multiset.count_pos.mp hposδ
      have heγ : e ∈ γ.internalEdges := Multiset.count_pos.mp hpos
      have hdisj : _root_.Disjoint δ.vertices γ.vertices := A.pairwiseDisjoint hδ hγ hne
      obtain ⟨hsδ, _⟩ := δ.edges_supported e heδ
      obtain ⟨hsγ, _⟩ := γ.edges_supported e heγ
      exact absurd hsγ (Finset.disjoint_left.mp hdisj hsδ)
    rw [hcoll]; exact Multiset.count_le_of_le e (h γ hγ)
  · have hz : (∑ δ ∈ A.elements, Multiset.count e δ.internalEdges) = 0 := by
      refine Finset.sum_eq_zero (fun δ hδ => ?_)
      by_contra hcon
      exact hex ⟨δ, hδ, Nat.pos_of_ne_zero hcon⟩
    rw [hz]; exact Nat.zero_le _

/-- **body-602 (Step 0) — complement-edge positivity is anti-monotone in internal edges, re-derived
clean.**  (Clean re-derivation of `complementEdges_card_pos_of_internalEdges_le`.) -/
theorem phi4WTriplePrime_complementEdges_card_pos_of_internalEdges_le
    {A B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G}
    (hAB : @ResolvedAdmissibleSubgraph.internalEdges phi4DivergenceMeasureFamily G A
        ≤ @ResolvedAdmissibleSubgraph.internalEdges phi4DivergenceMeasureFamily G B)
    (hB : 0 < (@ResolvedAdmissibleSubgraph.complementEdges phi4DivergenceMeasureFamily G B).card) :
    0 < (@ResolvedAdmissibleSubgraph.complementEdges phi4DivergenceMeasureFamily G A).card := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rcases Multiset.card_pos_iff_exists_mem.mp hB with ⟨e, he⟩
  have heB : Multiset.count e B.internalEdges < Multiset.count e G.internalEdges := by
    have hmem : e ∈ G.internalEdges - B.internalEdges := he
    exact Multiset.mem_sub.mp hmem
  refine Multiset.card_pos_iff_exists_mem.mpr ⟨e, ?_⟩
  show e ∈ G.internalEdges - A.internalEdges
  rw [Multiset.mem_sub]
  exact lt_of_le_of_lt (Multiset.count_le_of_le e hAB) heB

/-! ## Step 2/3 — stable promotion + the promotion closure (single-branch core) -/

/-- **body-602 (Step 3) — the root lift of an inner forest component sits inside its owner.** -/
theorem phi4WTriplePrime_rootRelativeInner_vertices_subset (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph) :
    (rootRelativeInner γ δ).vertices ⊆ γ.vertices := by
  simp only [rootRelativeInner_vertices]; exact δ.vertices_subset

/-- **body-602 (Step 3, CRUX) — the promotion closure for a single forest branch.**  For an outer
component `γ` of a W‴ split choice, a live W‴ inner forest index `B`, and an inner component
`δ ∈ B.elements`, the root lift `rootRelativeInner γ δ` is:
* connected divergent on `G.forget` (via the body-601 UNGATED landing — the boundary-closed gate is
  derived internally from `s.outer_mem`);
* externally-leg-saturated on `G` (direct `le_refl` from the 597 vertex/leg preservation);
* internal-edge complete on `G` (two-stage transitivity: `count e G.internalEdges ≤ count e γ.internalEdges`
  by OUTER completeness, then `= count e γ.bcrg.internalEdges ≤ count e δ.internalEdges` by INNER
  completeness). -/
theorem phi4WTriplePrime_rootRelativeInner_closure
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {γ : ResolvedFeynmanSubgraph G}
    (hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer)
    (B : (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx)
    {δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
            γ.boundaryCompletedResolvedGraph B.1) :
    (@FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily _)
        (rootRelativeInner γ δ).forget)
    ∧ ResolvedExternalLegSaturated G (rootRelativeInner γ δ)
    ∧ ResolvedInternalEdgeComplete (rootRelativeInner γ δ) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have hmem := (mem_phi4WTriplePrimeIndex _ B.1).mp B.2
  have hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ := hmem.2.2.2.2.2.1 δ hδ
  have hδEC : ResolvedInternalEdgeComplete δ := hmem.2.2.2.2.2.2 δ hδ
  have hδCD : @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
      (phi4DivergenceMeasureFamily _) δ.forget := B.1.isConnectedDivergent δ hδ
  have hECγ : ResolvedInternalEdgeComplete γ :=
    phi4EdgeCompleteSplitChoice_forestEdgeComplete s γ hγ
  refine ⟨?_, ?_, ?_⟩
  · exact phi4EdgeCompleteSplitChoice_rootRelativeInner_isConnectedDivergent s hγ hδsat hδCD
  · show G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (rootRelativeInner γ δ).vertices)
        ≤ (rootRelativeInner γ δ).externalLegs
    rw [rootRelativeInner_externalLegs]
    apply le_of_eq
    simp only [rootRelativeInner_vertices]
  · show G.internalEdges.filter
        (fun e => e.source ∈ (rootRelativeInner γ δ).vertices
          ∧ e.target ∈ (rootRelativeInner γ δ).vertices)
        ≤ (rootRelativeInner γ δ).internalEdges
    simp only [rootRelativeInner_vertices, rootRelativeInner_internalEdges]
    rw [Multiset.le_iff_count]
    intro e
    rw [Multiset.count_filter]
    by_cases hP : (e.source ∈ δ.vertices ∧ e.target ∈ δ.vertices)
    · rw [if_pos hP]
      obtain ⟨hsδ, htδ⟩ := hP
      have hsγ : e.source ∈ γ.vertices := δ.vertices_subset hsδ
      have htγ : e.target ∈ γ.vertices := δ.vertices_subset htδ
      have hOuter := resolvedInternalEdgeComplete_count hECγ hsγ htγ
      have hInner := resolvedInternalEdgeComplete_count hδEC hsδ htδ
      exact le_trans hOuter hInner
    · rw [if_neg hP]; exact Nat.zero_le _

/-! ## Step 1/4 — three-way partition: LEFT selection + FOREST promotion elements -/

/-- **body-602 (Step 1) — a component is LEFT-chosen** (its split choice is `Sum.inl true`). -/
def phi4WTriplePrime_leftPred (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
    s.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inl true

/-- **body-602 (Step 4) — the LEFT-selected outer forest** (`filterElements` of the LEFT components; CD
and pairwise-disjointness inherited from `s.outer`). -/
noncomputable def phi4WTriplePrime_leftOf (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact s.outer.filterElements (phi4WTriplePrime_leftPred s)

@[simp] theorem phi4WTriplePrime_leftOf_elements (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (phi4WTriplePrime_leftOf s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).filter
          (phi4WTriplePrime_leftPred s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rfl

/-- **body-602 (Step 2) — the promoted (root-lifted) components at a single outer component `a`.**  The
inner ambient is `a.1.boundaryCompletedResolvedGraph`; on a `Sum.inr B` leg the promoted set is the image
of `B`'s components under `rootRelativeInner a.1`; on a primitive leg it is empty. -/
noncomputable def phi4WTriplePrime_promotedElemsAt (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (a : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer}) :
    Finset (ResolvedFeynmanSubgraph G) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact (s.choice a (Finset.mem_attach _ a)).elim
    (fun _ => (∅ : Finset (ResolvedFeynmanSubgraph G)))
    (fun B => B.1.elements.image (rootRelativeInner a.1))

/-- **body-602 (Step 2) — membership in the promoted set at `a`.** -/
theorem phi4WTriplePrime_mem_promotedElemsAt (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    (a : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer})
    {η : ResolvedFeynmanSubgraph G} :
    η ∈ phi4WTriplePrime_promotedElemsAt s a ↔
      ∃ B : (phi4WTriplePrimeCanonicalSupply.summandSupply a.1.boundaryCompletedResolvedGraph).ForestIdx,
        s.choice a (Finset.mem_attach _ a) = Sum.inr B ∧
        ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
              a.1.boundaryCompletedResolvedGraph B.1, η = rootRelativeInner a.1 δ := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  unfold phi4WTriplePrime_promotedElemsAt
  cases hc : s.choice a (Finset.mem_attach _ a) with
  | inl b =>
    simp only [Sum.elim_inl]
    constructor
    · intro h; simp at h
    · rintro ⟨B, hB, -⟩; simp at hB
  | inr B =>
    simp only [Sum.elim_inr, Finset.mem_image]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact ⟨B, rfl, δ, hδ, rfl⟩
    · rintro ⟨B', hB', δ, hδ, rfl⟩
      have hBB : B = B' := Sum.inr.inj hB'
      subst hBB
      exact ⟨δ, hδ, rfl⟩

/-- **body-602 (Step 4) — the PROMOTED forest** (`ofElements` on the biUnion of the per-component promoted
sets).  CD from the Step-3 closure; pairwise-disjointness from inner (`B.pairwiseDisjoint`) and outer
(`s.outer.pairwiseDisjoint`) disjointness lifted through `rootRelativeInner`'s vertex preservation. -/
noncomputable def phi4WTriplePrime_promotedOf (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  refine ResolvedAdmissibleSubgraph.ofElements
    ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach.biUnion
      (phi4WTriplePrime_promotedElemsAt s)) ?_ ?_
  · -- CD of every promoted component
    intro η hη
    rw [Finset.mem_biUnion] at hη
    obtain ⟨a, -, hηa⟩ := hη
    rw [phi4WTriplePrime_mem_promotedElemsAt] at hηa
    obtain ⟨B, -, δ, hδ, rfl⟩ := hηa
    exact (phi4WTriplePrime_rootRelativeInner_closure s a.2 B hδ).1
  · -- pairwise-disjointness within the promoted forest
    intro η₁ hη₁ η₂ hη₂ hne
    rw [Finset.mem_biUnion] at hη₁ hη₂
    obtain ⟨a₁, -, hη₁a⟩ := hη₁
    obtain ⟨a₂, -, hη₂a⟩ := hη₂
    rw [phi4WTriplePrime_mem_promotedElemsAt] at hη₁a hη₂a
    obtain ⟨B₁, hchoice₁, δ₁, hδ₁, rfl⟩ := hη₁a
    obtain ⟨B₂, hchoice₂, δ₂, hδ₂, rfl⟩ := hη₂a
    by_cases haeq : a₁ = a₂
    · subst haeq
      have hBeq : B₁ = B₂ := Sum.inr.inj (hchoice₁.symm.trans hchoice₂)
      subst hBeq
      have hδne : δ₁ ≠ δ₂ := fun h => hne (by rw [h])
      have hdd : δ₁.Disjoint δ₂ := B₁.1.pairwiseDisjoint hδ₁ hδ₂ hδne
      show _root_.Disjoint (rootRelativeInner a₁.1 δ₁).vertices (rootRelativeInner a₁.1 δ₂).vertices
      simpa only [rootRelativeInner_vertices] using hdd
    · have ha1ne : a₁.1 ≠ a₂.1 := fun h => haeq (Subtype.ext h)
      have hodisj : a₁.1.Disjoint a₂.1 := s.outer.pairwiseDisjoint a₁.2 a₂.2 ha1ne
      show _root_.Disjoint (rootRelativeInner a₁.1 δ₁).vertices (rootRelativeInner a₂.1 δ₂).vertices
      exact Finset.disjoint_of_subset_left
        (phi4WTriplePrime_rootRelativeInner_vertices_subset a₁.1 δ₁)
        (Finset.disjoint_of_subset_right
          (phi4WTriplePrime_rootRelativeInner_vertices_subset a₂.1 δ₂) hodisj)

@[simp] theorem phi4WTriplePrime_promotedOf_elements
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (phi4WTriplePrime_promotedOf s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach.biUnion
          (phi4WTriplePrime_promotedElemsAt s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rfl

/-- **body-602 (Step 4) — cross-disjointness between LEFT and PROMOTED components.**  A left component
`γ_L` and a promoted `rootRelativeInner γ_F δ` have DIFFERENT owners (the same `γ` cannot be both left-
and forest-chosen — the choice is a function), so `s.outer.pairwiseDisjoint` separates them. -/
theorem phi4WTriplePrime_cross (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ∀ γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_leftOf s),
      ∀ η ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_promotedOf s), γ ≠ η → γ.Disjoint η := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro γL hγL η hη _hne
  rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter] at hγL
  obtain ⟨hγLmem, hleft, hleftEq⟩ := hγL
  rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion] at hη
  obtain ⟨a, -, hηa⟩ := hη
  rw [phi4WTriplePrime_mem_promotedElemsAt] at hηa
  obtain ⟨B, hchoice, δ, hδ, rfl⟩ := hηa
  have hownerNe : γL ≠ a.1 := by
    intro hEq
    subst hEq
    -- γL = a.1 ⇒ the two choice reads coincide ⇒ `Sum.inl true = Sum.inr B`, impossible
    have hlt : s.choice a (Finset.mem_attach _ a) = Sum.inl true := hleftEq
    rw [hchoice] at hlt
    simp at hlt
  have hodisj : γL.Disjoint a.1 := s.outer.pairwiseDisjoint hγLmem a.2 hownerNe
  show _root_.Disjoint γL.vertices (rootRelativeInner a.1 δ).vertices
  exact Finset.disjoint_of_subset_right
    (phi4WTriplePrime_rootRelativeInner_vertices_subset a.1 δ) hodisj

/-! ## Step 5 — selectedOuter + W‴ membership -/

/-- **body-602 (Step 5) — the selectedOuter admissible forest of a W‴ split choice.** -/
noncomputable def phi4WTriplePrime_selectedOuter (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact (phi4WTriplePrime_leftOf s).union (phi4WTriplePrime_promotedOf s)
    (phi4WTriplePrime_cross s)

/-- **body-602 (Step 6) — the selectedOuter component set** (`leftOf ∪ promotedOf`). -/
@[simp] theorem phi4WTriplePrime_selectedOuter_elements
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
            (phi4WTriplePrime_leftOf s))
        ∪ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
            (phi4WTriplePrime_promotedOf s)) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  unfold phi4WTriplePrime_selectedOuter
  ext c
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]

/-- **body-602 (Step 6) — the origin of each selectedOuter component.**  Either it is a LEFT-chosen outer
component, or it is a promoted `rootRelativeInner γ δ` for a forest-chosen outer component `γ` and an inner
`δ ∈ B.elements`.  The witnesses (`γ`, `B`, `δ`) are carried concretely for body-603. -/
theorem phi4WTriplePrime_selectedOuter_component_origin
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G)
    {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s)) :
    (c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer
        ∧ phi4WTriplePrime_leftPred s c)
    ∨ (∃ γ, ∃ hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
        ∃ B : (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx,
          s.choice ⟨γ, hγ⟩ (Finset.mem_attach _ ⟨γ, hγ⟩) = Sum.inr B
          ∧ ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
              γ.boundaryCompletedResolvedGraph B.1, c = rootRelativeInner γ δ) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rw [phi4WTriplePrime_selectedOuter_elements, Finset.mem_union] at hc
  rcases hc with hL | hP
  · rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter] at hL
    exact Or.inl ⟨hL.1, hL.2⟩
  · rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion] at hP
    obtain ⟨a, -, hηa⟩ := hP
    rw [phi4WTriplePrime_mem_promotedElemsAt] at hηa
    obtain ⟨B, hchoice, δ, hδ, hceq⟩ := hηa
    exact Or.inr ⟨a.1, a.2, B, hchoice, δ, hδ, hceq⟩

/-- **body-602 (Step 5) — selectedOuter is forest-internal-edge complete.** -/
theorem phi4WTriplePrime_selectedOuter_forestEdgeComplete
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily
      (phi4WTriplePrime_selectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro c hc
  rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
  · exact phi4EdgeCompleteSplitChoice_forestEdgeComplete s c hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    exact (phi4WTriplePrime_rootRelativeInner_closure s hγ B hδ).2.2

/-- **body-602 (Step 5) — selectedOuter is forest externally-leg saturated.** -/
theorem phi4WTriplePrime_selectedOuter_forestSaturated
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro c hc
  rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
  · exact (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.1) c hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    exact (phi4WTriplePrime_rootRelativeInner_closure s hγ B hδ).2.1

/-- **body-602 (Step 5) — selectedOuter is a proper forest.** -/
theorem phi4WTriplePrime_selectedOuter_isProperForest
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G
      (phi4WTriplePrime_selectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have houterMem := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have houterProper : s.outer.IsProperForest := houterMem.2.2.2.2.1
  -- HasNonemptyComponents
  have hNC : (phi4WTriplePrime_selectedOuter s).HasNonemptyComponents := by
    intro c hc
    rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
    · exact houterProper.2.1 c hcmem
    · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
      have hBproper : B.1.IsProperForest := ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      exact hBproper.2.1 δ hδ
  -- HasPositiveInternalEdgesComponents
  have hPC : (phi4WTriplePrime_selectedOuter s).HasPositiveInternalEdgesComponents := by
    intro c hc
    rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
    · exact houterProper.2.2.2.1 c hcmem
    · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
      have hBproper : B.1.IsProperForest := ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      exact hBproper.2.2.2.1 δ hδ
  -- IsNonempty (from the filtered split choice avoiding the all-primitive-right choice)
  have hNE : (phi4WTriplePrime_selectedOuter s).IsNonempty := by
    have hfilt := (mem_phi4EdgeCompleteForestChoiceCarrier s.outer).mp s.choice_filtered
    have hNePR : s.choice ≠ phi4EdgeCompleteChoicePR s.outer := hfilt.2.1
    -- some component's choice ≠ Sum.inl false
    have h1 : ∃ a, s.choice a ≠ phi4EdgeCompleteChoicePR s.outer a := by
      by_contra hcon
      exact hNePR (funext (fun a => by
        by_contra hne; exact hcon ⟨a, hne⟩))
    obtain ⟨a, ha⟩ := h1
    have h2 : ∃ hatt, s.choice a hatt ≠ phi4EdgeCompleteChoicePR s.outer a hatt := by
      by_contra hcon
      exact ha (funext (fun hatt => by
        by_contra hne; exact hcon ⟨hatt, hne⟩))
    obtain ⟨hatt, ha2⟩ := h2
    -- classify the non-right choice at `a`
    show (phi4WTriplePrime_selectedOuter s).elements.Nonempty
    rw [phi4WTriplePrime_selectedOuter_elements]
    rcases hcase : s.choice a hatt with b | B
    · rcases b with _ | _
      · exact absurd hcase ha2
      · -- Sum.inl true → a.1 is a LEFT component → leftOf nonempty
        refine Finset.Nonempty.inl ⟨a.1, ?_⟩
        rw [phi4WTriplePrime_leftOf_elements, Finset.mem_filter]
        exact ⟨a.2, a.2, hcase⟩
    · -- Sum.inr B → a promotes a nonempty inner forest → promotedOf nonempty
      have hBproper : B.1.IsProperForest := ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      obtain ⟨δ, hδ⟩ := hBproper.1
      refine Finset.Nonempty.inr ⟨rootRelativeInner a.1 δ, ?_⟩
      rw [phi4WTriplePrime_promotedOf_elements, Finset.mem_biUnion]
      refine ⟨a, Finset.mem_attach _ a, ?_⟩
      rw [phi4WTriplePrime_mem_promotedElemsAt]
      exact ⟨B, hcase, δ, hδ, rfl⟩
  -- 0 < internalEdges.card (from IsNonempty + HasPositiveInternalEdgesComponents)
  have hIEpos : 0 < (phi4WTriplePrime_selectedOuter s).internalEdges.card := by
    obtain ⟨η, hη⟩ := hNE
    have hηle : η.internalEdges ≤ (phi4WTriplePrime_selectedOuter s).internalEdges :=
      Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
        (fun i _ => Multiset.zero_le _) hη
    exact lt_of_lt_of_le (hPC η hη) (Multiset.card_le_card hηle)
  -- 0 < complementEdges.card (selectedOuter internal edges ≤ s.outer's, whose complement is positive)
  have hcompPos : 0 < (phi4WTriplePrime_selectedOuter s).complementEdges.card := by
    have hcompLe : ∀ c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (phi4WTriplePrime_selectedOuter s), c.internalEdges ≤ s.outer.internalEdges := by
      intro c hc
      rcases phi4WTriplePrime_selectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
      · exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
          (fun i _ => Multiset.zero_le _) hcmem
      · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
        have h1 : (rootRelativeInner γ δ).internalEdges ≤ γ.internalEdges := by
          show δ.internalEdges ≤ γ.internalEdges
          exact δ.internalEdges_le
        have h2 : γ.internalEdges ≤ s.outer.internalEdges :=
          Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
            (fun i _ => Multiset.zero_le _) hγ
        exact le_trans h1 h2
    have hle : (phi4WTriplePrime_selectedOuter s).internalEdges ≤ s.outer.internalEdges :=
      phi4WTriplePrime_internalEdges_le_of_components_le (phi4WTriplePrime_selectedOuter s) hcompLe
    exact phi4WTriplePrime_complementEdges_card_pos_of_internalEdges_le hle
      (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest houterProper)
  exact ⟨hNE, hNC, hIEpos, hPC, hcompPos⟩

/-- **body-602 (Step 5, HEADLINE) — the selectedOuter of a W‴ filtered split choice lands back in the W‴
(fifth-axis) index.**  NO external gate / `Measure` / `E` hypothesis: the four ambient conjuncts come from
`s.outer_mem` (same ambient `G`); properness / saturation / edge-completeness are the three construction
theorems above. -/
theorem phi4WTriplePrime_selectedOuter_mem
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    phi4WTriplePrime_selectedOuter s ∈ phi4WTriplePrimeIndex G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have houterMem := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  exact (mem_phi4WTriplePrimeIndex G (phi4WTriplePrime_selectedOuter s)).mpr
    ⟨houterMem.1, houterMem.2.1, houterMem.2.2.1, houterMem.2.2.2.1,
      phi4WTriplePrime_selectedOuter_isProperForest s,
      phi4WTriplePrime_selectedOuter_forestSaturated s,
      phi4WTriplePrime_selectedOuter_forestEdgeComplete s⟩

end GaugeGeometry.QFT.Combinatorial
