import GaugeGeometry.QFT.HopfAlgebra.Phi4StableRootRelativeCDLanding

/-!
# QFT-R1-body-632 — the STABLE-carrier selectedOuter + the full LEFT-factor product

Body-625 proved a class-level **no-go**: on the OLD carrier the naive nested completion re-encodes an
inherited outer boundary leg EVEN while the root-direct route keeps it ODD, so the per-occurrence left-factor
generators disagree and the whole left-factor product identity CANNOT be emitted.  Body-629 built the PARALLEL
STABLE resolved Hopf carrier; body-630 rebuilt the per-occurrence FOREST generator match on that carrier
(`stableForestLeftFactor_gen_eq_promoted`), and body-631 supplied the NATIVE root-relative CD landing with
ZERO gate (`stableSplitChoice_rootRelativeInner_isConnectedDivergent`).  This body **completes**, on the
STABLE carrier, the left-factor product that body-625 broke — turning the breakage into a design theorem.

## Steps

* Step 1 — the stable promotion closure `stableRootRelativeInner_closure`: per FOREST branch `B`, component
  `δ`, the root lift `stableRootRelativeInner γ.1 δ` is connected-divergent (body-631, zero gate),
  externally-leg saturated (le_refl — the lift's legs ARE the saturating filter), and internal-edge complete
  (outer/inner two-stage transitivity).  NO gate / ambient transport / old divergence class.
* Step 2 — the exact component partition: `stableRootRelativeInner_injOn_elements` (INJECTIVITY on
  `B.elements`, via inner disjointness + nonempty components — `Finset.image` loses NO multiplicity), then
  `stableLeftOf` / `stablePromotedElemsAt` / `stablePromotedOf` / `stableCross` mirroring body-602.
* Step 3 — `stableSelectedOuter := (stableLeftOf s).union (stablePromotedOf s) (stableCross s)`, its
  component-origin, proper-forest / saturation / edge-complete lemmas, and **HEADLINE 1**
  `stableSelectedOuter_mem : stableSelectedOuter s ∈ phi4WTriplePrimeIndex G` (only `hSt`, `s`; ZERO gate).
* Step 4 — the product reindex: a single `contribSet` per outer component (LEFT → primitive generator, RIGHT
  → `1`, FOREST → the promoted image), each FOREST factor consuming body-630's
  `stableForestLeftFactor_gen_eq_promoted` DIRECTLY; flattened with `Finset.prod_biUnion` (pairwise disjoint
  contributions) + `Finset.prod_image` (the Step-2 injectivity).  No `toFinset` / dedup / orbit quotient.
* Step 5 — **HEADLINE 2** `stableSelectedOuter_leftFactor_product`: the branchwise outer left weight equals
  the stable selectedOuter aggregate `stableLeftAggregate (stableSelectedOuter s) hSt`.

## HALT / red lines
body-625's no-go, body-630, body-629, the OLD carrier / coproduct, and every existing file are UNEDITED; NO
equality / Equiv / cast / coalgebra bridge to the old resolved carrier / coproduct.  Right factor / `quot_eq`
/ summand agreement / `sum_bij` / alpha / coassoc are NOT entered; body-258's polluted product theorem is
BLUEPRINT-only (NOT consumed).  ZERO new `class` / `structure` / permanent `instance` (one file-local `local
instance` for the φ⁴ divergence family, as in body-630/631).  ZERO forbidden divergence classes in any
declaration TYPE; ZERO `sorry` / `admit` / `native_decide`; NO public `HEq` / `cast` / graph-data `▸`; every
`Finset.image` carries an injectivity proof.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option maxHeartbeats 1600000

variable {G : ResolvedFeynmanGraph}

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family (mirrors body-630/631), so the
resolved admissible-subgraph / carrier plumbing elaborates against the φ⁴ family. -/
local instance instPhi4DivergenceMeasureFamily632 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the stable promotion closure -/

/-- **body-632 (Step 1) — the root lift of an inner forest component sits inside its owner.** -/
theorem stableRootRelativeInner_vertices_subset (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).vertices ⊆ γ.vertices := by
  simp only [stableRootRelativeInner_vertices]; exact δ.vertices_subset

/-- **body-632 (Step 1, CRUX) — the stable promotion closure for a single forest branch.**  For an outer
component `γ` of a stable split choice `s`, a live stable inner forest `B` over `stableLocalBoundaryCompletedGraph
γ.1`, and an inner component `δ ∈ B.1.elements`, the root lift `stableRootRelativeInner γ.1 δ` is:
* connected divergent on `G.forget` — body-631's NATIVE landing, EVERY premise recovered from the types, NO
  boundary-closed gate;
* externally-leg saturated on `G` — the lift's external legs ARE the `G`-legs saturating its vertices, so
  `le_refl` (from the body-630 preservation of vertices/legs);
* internal-edge complete on `G` — the two-stage transitivity `count e G.internalEdges ≤ count e γ.1.internalEdges
  ≤ count e δ.internalEdges`. -/
theorem stableRootRelativeInner_closure {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer})
    (B : StableLocalForestIdx γ.1)
    {δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ.1)}
    (hδ : δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph γ.1) B.1) :
    (@FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily _)
        (stableRootRelativeInner γ.1 δ).forget)
    ∧ ResolvedExternalLegSaturated G (stableRootRelativeInner γ.1 δ)
    ∧ ResolvedInternalEdgeComplete (stableRootRelativeInner γ.1 δ) := by
  have hO := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have hEC : ResolvedInternalEdgeComplete γ.1 := hO.2.2.2.2.2.2 γ.1 γ.2
  have hB := (mem_phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph γ.1) B.1).mp B.2
  have hδEC : ResolvedInternalEdgeComplete δ := hB.2.2.2.2.2.2 δ hδ
  refine ⟨?_, ?_, ?_⟩
  · exact stableSplitChoice_rootRelativeInner_isConnectedDivergent s γ B ⟨δ, hδ⟩
  · show G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ (stableRootRelativeInner γ.1 δ).vertices)
        ≤ (stableRootRelativeInner γ.1 δ).externalLegs
    rw [stableRootRelativeInner_externalLegs]
    apply le_of_eq
    simp only [stableRootRelativeInner_vertices]
  · show G.internalEdges.filter
        (fun e => e.source ∈ (stableRootRelativeInner γ.1 δ).vertices
          ∧ e.target ∈ (stableRootRelativeInner γ.1 δ).vertices)
        ≤ (stableRootRelativeInner γ.1 δ).internalEdges
    simp only [stableRootRelativeInner_vertices, stableRootRelativeInner_internalEdges]
    rw [Multiset.le_iff_count]
    intro e
    rw [Multiset.count_filter]
    by_cases hP : (e.source ∈ δ.vertices ∧ e.target ∈ δ.vertices)
    · rw [if_pos hP]
      obtain ⟨hsδ, htδ⟩ := hP
      have hsγ : e.source ∈ γ.1.vertices := δ.vertices_subset hsδ
      have htγ : e.target ∈ γ.1.vertices := δ.vertices_subset htδ
      exact le_trans (resolvedInternalEdgeComplete_count hEC hsγ htγ)
        (resolvedInternalEdgeComplete_count hδEC hsδ htδ)
    · rw [if_neg hP]; exact Nat.zero_le _

/-! ## Step 2 — the exact component partition (stable-native) -/

/-- **body-632 (Step 2, INJECTIVITY) — the root lift is injective on a nonempty-component forest.**  If two
inner components `δ₁, δ₂ ∈ B.elements` have the same root lift, then their vertex sets coincide; but the forest
is pairwise disjoint and every component is vertex-nonempty, so `δ₁ = δ₂`.  Hence `Finset.image
(stableRootRelativeInner γ)` loses NO component multiplicity. -/
theorem stableRootRelativeInner_injOn_elements (γ : ResolvedFeynmanSubgraph G)
    (B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph γ))
    (hBNE : B.HasNonemptyComponents) :
    Set.InjOn (stableRootRelativeInner γ)
      (↑(@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
        (stableLocalBoundaryCompletedGraph γ) B)) := by
  intro δ₁ hδ₁ δ₂ hδ₂ heq
  by_contra hne
  have hv : δ₁.vertices = δ₂.vertices := by
    have := congrArg ResolvedFeynmanSubgraph.vertices heq
    simpa only [stableRootRelativeInner_vertices] using this
  have hdisj : _root_.Disjoint δ₁.vertices δ₂.vertices :=
    B.pairwiseDisjoint (Finset.mem_coe.mp hδ₁) (Finset.mem_coe.mp hδ₂) hne
  rw [hv] at hdisj
  have hpos : 0 < δ₂.vertices.card := hBNE δ₂ (Finset.mem_coe.mp hδ₂)
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  exact Finset.disjoint_left.mp hdisj hx hx

/-- **body-632 (Step 2) — a component is LEFT-chosen** (its split choice is `Sum.inl true`). -/
def stableLeftPred {hSt : StableResolvedBoundaryIds G} (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : ResolvedFeynmanSubgraph G) : Prop :=
  ∃ h : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
    s.choice ⟨γ, h⟩ (Finset.mem_attach _ ⟨γ, h⟩) = Sum.inl true

/-- **body-632 (Step 2) — the LEFT-selected outer forest.** -/
noncomputable def stableLeftOf {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact s.outer.filterElements (stableLeftPred s)

@[simp] theorem stableLeftOf_elements {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableLeftOf s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).filter
          (stableLeftPred s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rfl

/-- **body-632 (Step 2) — the promoted (root-lifted) components at a single outer component `a`.** -/
noncomputable def stablePromotedElemsAt {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (a : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer}) :
    Finset (ResolvedFeynmanSubgraph G) :=
  (s.choice a (Finset.mem_attach _ a)).elim
    (fun _ => (∅ : Finset (ResolvedFeynmanSubgraph G)))
    (fun B => B.1.elements.image (stableRootRelativeInner a.1))

/-- **body-632 (Step 2) — membership in the promoted set at `a`.** -/
theorem mem_stablePromotedElemsAt {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (a : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer})
    {η : ResolvedFeynmanSubgraph G} :
    η ∈ stablePromotedElemsAt s a ↔
      ∃ B : StableLocalForestIdx a.1, s.choice a (Finset.mem_attach _ a) = Sum.inr B ∧
        ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
              (stableLocalBoundaryCompletedGraph a.1) B.1, η = stableRootRelativeInner a.1 δ := by
  unfold stablePromotedElemsAt
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

/-- **body-632 (Step 2) — the PROMOTED forest** (`ofElements` on the biUnion of the per-component promoted
sets).  CD from the Step-1 closure; pairwise-disjointness from inner + outer disjointness lifted through the
root lift's vertex preservation. -/
noncomputable def stablePromotedOf {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  refine ResolvedAdmissibleSubgraph.ofElements
    ((@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach.biUnion
      (stablePromotedElemsAt s)) ?_ ?_
  · intro η hη
    rw [Finset.mem_biUnion] at hη
    obtain ⟨a, -, hηa⟩ := hη
    rw [mem_stablePromotedElemsAt] at hηa
    obtain ⟨B, -, δ, hδ, rfl⟩ := hηa
    exact (stableRootRelativeInner_closure s a B hδ).1
  · intro η₁ hη₁ η₂ hη₂ hne
    rw [Finset.mem_biUnion] at hη₁ hη₂
    obtain ⟨a₁, -, hη₁a⟩ := hη₁
    obtain ⟨a₂, -, hη₂a⟩ := hη₂
    rw [mem_stablePromotedElemsAt] at hη₁a hη₂a
    obtain ⟨B₁, hchoice₁, δ₁, hδ₁, rfl⟩ := hη₁a
    obtain ⟨B₂, hchoice₂, δ₂, hδ₂, rfl⟩ := hη₂a
    by_cases haeq : a₁ = a₂
    · subst haeq
      have hBeq : B₁ = B₂ := Sum.inr.inj (hchoice₁.symm.trans hchoice₂)
      subst hBeq
      have hδne : δ₁ ≠ δ₂ := fun h => hne (by rw [h])
      have hdd : δ₁.Disjoint δ₂ := B₁.1.pairwiseDisjoint hδ₁ hδ₂ hδne
      show _root_.Disjoint (stableRootRelativeInner a₁.1 δ₁).vertices
        (stableRootRelativeInner a₁.1 δ₂).vertices
      simpa only [stableRootRelativeInner_vertices] using hdd
    · have ha1ne : a₁.1 ≠ a₂.1 := fun h => haeq (Subtype.ext h)
      have hodisj : a₁.1.Disjoint a₂.1 := s.outer.pairwiseDisjoint a₁.2 a₂.2 ha1ne
      show _root_.Disjoint (stableRootRelativeInner a₁.1 δ₁).vertices
        (stableRootRelativeInner a₂.1 δ₂).vertices
      exact Finset.disjoint_of_subset_left
        (stableRootRelativeInner_vertices_subset a₁.1 δ₁)
        (Finset.disjoint_of_subset_right
          (stableRootRelativeInner_vertices_subset a₂.1 δ₂) hodisj)

@[simp] theorem stablePromotedOf_elements {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stablePromotedOf s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach.biUnion
          (stablePromotedElemsAt s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rfl

/-- **body-632 (Step 2) — cross-disjointness between LEFT and PROMOTED components.** -/
theorem stableCross {hSt : StableResolvedBoundaryIds G} (s : StablePhi4ResolvedSplitChoice G hSt) :
    ∀ γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableLeftOf s),
      ∀ η ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stablePromotedOf s),
        γ ≠ η → γ.Disjoint η := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro γL hγL η hη _hne
  rw [stableLeftOf_elements, Finset.mem_filter] at hγL
  obtain ⟨hγLmem, hleft, hleftEq⟩ := hγL
  rw [stablePromotedOf_elements, Finset.mem_biUnion] at hη
  obtain ⟨a, -, hηa⟩ := hη
  rw [mem_stablePromotedElemsAt] at hηa
  obtain ⟨B, hchoice, δ, hδ, rfl⟩ := hηa
  have hownerNe : γL ≠ a.1 := by
    intro hEq
    subst hEq
    have hlt : s.choice a (Finset.mem_attach _ a) = Sum.inl true := hleftEq
    rw [hchoice] at hlt
    simp at hlt
  have hodisj : γL.Disjoint a.1 := s.outer.pairwiseDisjoint hγLmem a.2 hownerNe
  show _root_.Disjoint γL.vertices (stableRootRelativeInner a.1 δ).vertices
  exact Finset.disjoint_of_subset_right
    (stableRootRelativeInner_vertices_subset a.1 δ) hodisj

/-! ## Step 3 — the stable selectedOuter + W‴ membership -/

/-- **body-632 (Step 3) — the stable selectedOuter admissible forest of a stable split choice.** -/
noncomputable def stableSelectedOuter {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact (stableLeftOf s).union (stablePromotedOf s) (stableCross s)

@[simp] theorem stableSelectedOuter_elements {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableSelectedOuter s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableLeftOf s))
        ∪ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stablePromotedOf s)) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  unfold stableSelectedOuter
  ext c
  simp only [ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]

/-- **body-632 (Step 3) — the origin of each stable selectedOuter component.** -/
theorem stableSelectedOuter_component_origin {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) {c : ResolvedFeynmanSubgraph G}
    (hc : c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableSelectedOuter s)) :
    (c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer
        ∧ stableLeftPred s c)
    ∨ (∃ γ, ∃ hγ : γ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer,
        ∃ B : StableLocalForestIdx γ,
          s.choice ⟨γ, hγ⟩ (Finset.mem_attach _ ⟨γ, hγ⟩) = Sum.inr B
          ∧ ∃ δ ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily
              (stableLocalBoundaryCompletedGraph γ) B.1, c = stableRootRelativeInner γ δ) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  rw [stableSelectedOuter_elements, Finset.mem_union] at hc
  rcases hc with hL | hP
  · rw [stableLeftOf_elements, Finset.mem_filter] at hL
    exact Or.inl ⟨hL.1, hL.2⟩
  · rw [stablePromotedOf_elements, Finset.mem_biUnion] at hP
    obtain ⟨a, -, hηa⟩ := hP
    rw [mem_stablePromotedElemsAt] at hηa
    obtain ⟨B, hchoice, δ, hδ, hceq⟩ := hηa
    exact Or.inr ⟨a.1, a.2, B, hchoice, δ, hδ, hceq⟩

/-- **body-632 (Step 3) — stableSelectedOuter is forest-internal-edge complete.** -/
theorem stableSelectedOuter_forestEdgeComplete {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily (stableSelectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro c hc
  rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
  · exact (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.2) c hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    exact (stableRootRelativeInner_closure s ⟨γ, hγ⟩ B hδ).2.2

/-- **body-632 (Step 3) — stableSelectedOuter is forest externally-leg saturated.** -/
theorem stableSelectedOuter_forestSaturated {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily G (stableSelectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  intro c hc
  rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
  · exact (((mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem).2.2.2.2.2.1) c hcmem
  · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
    exact (stableRootRelativeInner_closure s ⟨γ, hγ⟩ B hδ).2.1

/-- **body-632 (Step 3) — stableSelectedOuter is a proper forest.** -/
theorem stableSelectedOuter_isProperForest {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G (stableSelectedOuter s) := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have houterMem := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have houterProper : s.outer.IsProperForest := houterMem.2.2.2.2.1
  have hNC : (stableSelectedOuter s).HasNonemptyComponents := by
    intro c hc
    rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
    · exact houterProper.2.1 c hcmem
    · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
      have hBproper : B.1.IsProperForest :=
        ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      show 0 < (stableRootRelativeInner γ δ).vertices.card
      simp only [stableRootRelativeInner_vertices]
      exact hBproper.2.1 δ hδ
  have hPC : (stableSelectedOuter s).HasPositiveInternalEdgesComponents := by
    intro c hc
    rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
    · exact houterProper.2.2.2.1 c hcmem
    · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
      have hBproper : B.1.IsProperForest :=
        ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      show 0 < (stableRootRelativeInner γ δ).internalEdges.card
      simp only [stableRootRelativeInner_internalEdges]
      exact hBproper.2.2.2.1 δ hδ
  have hNE : (stableSelectedOuter s).IsNonempty := by
    obtain ⟨a, hatt, hane⟩ := s.choice_nontrivial
    have hane' : s.choice a (Finset.mem_attach _ a) ≠ Sum.inl false := hane
    show (stableSelectedOuter s).elements.Nonempty
    rw [stableSelectedOuter_elements]
    rcases hcase : s.choice a (Finset.mem_attach _ a) with b | B
    · rcases b with _ | _
      · exact absurd hcase hane'
      · refine Finset.Nonempty.inl ⟨a.1, ?_⟩
        rw [stableLeftOf_elements, Finset.mem_filter]
        exact ⟨a.2, a.2, hcase⟩
    · have hBproper : B.1.IsProperForest :=
        ((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1
      obtain ⟨δ, hδ⟩ := hBproper.1
      refine Finset.Nonempty.inr ⟨stableRootRelativeInner a.1 δ, ?_⟩
      rw [stablePromotedOf_elements, Finset.mem_biUnion]
      refine ⟨a, Finset.mem_attach _ a, ?_⟩
      rw [mem_stablePromotedElemsAt]
      exact ⟨B, hcase, δ, hδ, rfl⟩
  have hIEpos : 0 < (stableSelectedOuter s).internalEdges.card := by
    obtain ⟨η, hη⟩ := hNE
    have hηle : η.internalEdges ≤ (stableSelectedOuter s).internalEdges :=
      Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
        (fun i _ => Multiset.zero_le _) hη
    exact lt_of_lt_of_le (hPC η hη) (Multiset.card_le_card hηle)
  have hcompPos : 0 < (stableSelectedOuter s).complementEdges.card := by
    have hcompLe : ∀ c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G
        (stableSelectedOuter s), c.internalEdges ≤ s.outer.internalEdges := by
      intro c hc
      rcases stableSelectedOuter_component_origin s hc with ⟨hcmem, -⟩ | hP
      · exact Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
          (fun i _ => Multiset.zero_le _) hcmem
      · obtain ⟨γ, hγ, B, -, δ, hδ, rfl⟩ := hP
        have h1 : (stableRootRelativeInner γ δ).internalEdges ≤ γ.internalEdges := by
          show δ.internalEdges ≤ γ.internalEdges
          exact δ.internalEdges_le
        have h2 : γ.internalEdges ≤ s.outer.internalEdges :=
          Finset.single_le_sum (f := fun x : ResolvedFeynmanSubgraph G => x.internalEdges)
            (fun i _ => Multiset.zero_le _) hγ
        exact le_trans h1 h2
    have hle : (stableSelectedOuter s).internalEdges ≤ s.outer.internalEdges :=
      phi4WTriplePrime_internalEdges_le_of_components_le (stableSelectedOuter s) hcompLe
    exact phi4WTriplePrime_complementEdges_card_pos_of_internalEdges_le hle
      (ResolvedAdmissibleSubgraph.complementEdges_card_pos_of_isProperForest houterProper)
  exact ⟨hNE, hNC, hIEpos, hPC, hcompPos⟩

/-- **body-632 (Step 3, HEADLINE 1) — the stable selectedOuter lands back in the W‴ (fifth-axis) index.**
NO external gate / `Measure` / `E` hypothesis: the four ambient conjuncts come from `s.outer_mem` (same ambient
`G`); properness / saturation / edge-completeness are the three construction theorems above. -/
theorem stableSelectedOuter_mem {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    stableSelectedOuter s ∈ phi4WTriplePrimeIndex G := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have houterMem := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  exact (mem_phi4WTriplePrimeIndex G (stableSelectedOuter s)).mpr
    ⟨houterMem.1, houterMem.2.1, houterMem.2.2.1, houterMem.2.2.2.1,
      stableSelectedOuter_isProperForest s,
      stableSelectedOuter_forestSaturated s,
      stableSelectedOuter_forestEdgeComplete s⟩

/-! ## Step 4 — the per-component contribution + the product reindex -/

/-- **body-632 (Step 4) — one stable local left generator** (raw CD proof; keyed by the inherited-verbatim
completion `stableLocalBoundaryCompletedGraph c`). -/
noncomputable def stableLocalLeftGen (hSt : StableResolvedBoundaryIds G) (c : ResolvedFeynmanSubgraph G)
    (hCD : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) c.forget) :
    StableResolvedPhi4HopfH :=
  MvPolynomial.X ((stableLocalBoundaryCompletedGraph c).toStableResolvedPhi4HopfGen
    (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent c hCD)
    (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph c hSt))

/-- **body-632 (Step 4) — the totalized stable local left generator** (`1` off the CD locus, the real
generator on it).  The `dite` makes the aggregate a plain product-over-elements with no proof dependence. -/
noncomputable def stableLocalLeftGenTotal (hSt : StableResolvedBoundaryIds G)
    (c : ResolvedFeynmanSubgraph G) : StableResolvedPhi4HopfH :=
  if hc : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) c.forget
  then stableLocalLeftGen hSt c hc else 1

/-- **body-632 (Step 4) — the stable left aggregate as a plain product over the elements.**  The `.attach`
product of body-629's aggregate equals the total-generator product over `A.elements`, because the totalized
generator is `dif_pos` at every live component. -/
theorem stableLeftAggregate_eq_prod {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) (hSt : StableResolvedBoundaryIds G) :
    stableLeftAggregate A hSt
      = ∏ c ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G A,
          stableLocalLeftGenTotal hSt c := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  have hLHS : stableLeftAggregate A hSt
      = ∏ γ ∈ A.elements.attach, stableLocalLeftGen hSt γ.1 (A.isConnectedDivergent γ.1 γ.2) := rfl
  rw [hLHS, ← Finset.prod_attach A.elements (stableLocalLeftGenTotal hSt)]
  refine Finset.prod_congr rfl (fun γ _ => ?_)
  rw [stableLocalLeftGenTotal, dif_pos (A.isConnectedDivergent γ.1 γ.2)]

/-- **body-632 (Step 4) — the contribution set of one outer component.**  LEFT (`inl true`) → the singleton
`{γ.1}`; RIGHT (`inl false`) → `∅`; FOREST (`inr B`) → the promoted image `stableRootRelativeInner γ.1 '' B`. -/
noncomputable def stableContribSet {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer}) :
    Finset (ResolvedFeynmanSubgraph G) :=
  (s.choice γ (Finset.mem_attach _ γ)).elim
    (fun b => bif b then ({γ.1} : Finset (ResolvedFeynmanSubgraph G)) else ∅)
    (fun B => B.1.elements.image (stableRootRelativeInner γ.1))

/-- **body-632 (Step 4) — every contribution is a nonempty component inside its owner.** -/
theorem stableContribSet_subset_and_nonempty {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer})
    {c : ResolvedFeynmanSubgraph G} (hc : c ∈ stableContribSet s γ) :
    c.vertices ⊆ γ.1.vertices ∧ 0 < c.vertices.card := by
  have hO := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
  have houterNE : s.outer.HasNonemptyComponents := (hO.2.2.2.2.1).2.1
  rw [stableContribSet] at hc
  cases hch : s.choice γ (Finset.mem_attach _ γ) with
  | inl b =>
    rw [hch] at hc
    cases b with
    | true =>
      rw [Sum.elim_inl, cond_true, Finset.mem_singleton] at hc
      subst hc
      exact ⟨Finset.Subset.refl _, houterNE γ.1 γ.2⟩
    | false =>
      rw [Sum.elim_inl, cond_false] at hc
      exact absurd hc (Finset.notMem_empty c)
  | inr B =>
    rw [hch, Sum.elim_inr, Finset.mem_image] at hc
    obtain ⟨δ, hδ, rfl⟩ := hc
    have hBNE : B.1.HasNonemptyComponents :=
      (((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1).2.1
    refine ⟨?_, ?_⟩
    · simp only [stableRootRelativeInner_vertices]; exact δ.vertices_subset
    · show 0 < (stableRootRelativeInner γ.1 δ).vertices.card
      simp only [stableRootRelativeInner_vertices]; exact hBNE δ hδ

/-- **body-632 (Step 4) — the contributions of distinct outer components are Finset-disjoint.** -/
theorem stableContribSet_pairwiseDisjoint {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    Set.PairwiseDisjoint
      (↑(@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach)
      (stableContribSet s) := by
  intro γ₁ _ γ₂ _ hne
  show Disjoint (stableContribSet s γ₁) (stableContribSet s γ₂)
  have h1ne : γ₁.1 ≠ γ₂.1 := fun h => hne (Subtype.ext h)
  have hodisj : _root_.Disjoint γ₁.1.vertices γ₂.1.vertices :=
    s.outer.pairwiseDisjoint γ₁.2 γ₂.2 h1ne
  refine Finset.disjoint_left.mpr (fun c hc1 hc2 => ?_)
  obtain ⟨hsub1, hpos1⟩ := stableContribSet_subset_and_nonempty s γ₁ hc1
  obtain ⟨hsub2, _⟩ := stableContribSet_subset_and_nonempty s γ₂ hc2
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos1
  exact Finset.disjoint_left.mp hodisj (hsub1 hx) (hsub2 hx)

/-- **body-632 (Step 4) — the selectedOuter elements are the disjoint union of the contribution sets.** -/
theorem stableSelectedOuter_elements_eq_biUnion {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G (stableSelectedOuter s)
      = (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach.biUnion
          (stableContribSet s) := by
  rw [stableSelectedOuter_elements, stableLeftOf_elements, stablePromotedOf_elements]
  ext c
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_attach, true_and]
  constructor
  · rintro (⟨hc_mem, h, hchoice⟩ | ⟨a, hca⟩)
    · refine ⟨⟨c, h⟩, ?_⟩
      rw [stableContribSet, hchoice, Sum.elim_inl, cond_true]
      exact Finset.mem_singleton.mpr rfl
    · refine ⟨a, ?_⟩
      rw [stableContribSet]
      cases hac : s.choice a (Finset.mem_attach _ a) with
      | inl b =>
        rw [stablePromotedElemsAt, hac, Sum.elim_inl] at hca
        exact absurd hca (Finset.notMem_empty c)
      | inr B =>
        rw [Sum.elim_inr]
        rw [stablePromotedElemsAt, hac, Sum.elim_inr] at hca
        exact hca
  · rintro ⟨γ, hc⟩
    rw [stableContribSet] at hc
    cases hch : s.choice γ (Finset.mem_attach _ γ) with
    | inl b =>
      rw [hch] at hc
      cases b with
      | true =>
        rw [Sum.elim_inl, cond_true, Finset.mem_singleton] at hc
        subst hc
        exact Or.inl ⟨γ.2, γ.2, hch⟩
      | false =>
        rw [Sum.elim_inl, cond_false] at hc
        exact absurd hc (Finset.notMem_empty c)
    | inr B =>
      rw [hch, Sum.elim_inr, Finset.mem_image] at hc
      obtain ⟨δ, hδ, rfl⟩ := hc
      refine Or.inr ⟨γ, ?_⟩
      rw [mem_stablePromotedElemsAt]
      exact ⟨B, hch, δ, hδ, rfl⟩

/-- **body-632 (Step 4, per-component factor — the crux) — the local left factor of one outer component equals
the total-generator product over its contribution set.**  LEFT → the primitive generator; RIGHT → `1`; FOREST →
body-629's stable aggregate re-keyed onto the promoted image, each factor closed by body-630's
`stableForestLeftFactor_gen_eq_promoted` and the Step-2 injectivity. -/
theorem stableLocalLeftFactor_eq_prod_contribSet {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt)
    (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer}) :
    stableLocalLeftFactor hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
        (s.choice γ (Finset.mem_attach _ γ))
      = ∏ c ∈ stableContribSet s γ, stableLocalLeftGenTotal hSt c := by
  rw [stableContribSet]
  cases hc : s.choice γ (Finset.mem_attach _ γ) with
  | inl b =>
    cases b with
    | true =>
      rw [Sum.elim_inl, cond_true, Finset.prod_singleton, stableLocalLeftFactor_inl_true,
        stableLocalLeftGenTotal, dif_pos (s.outer.isConnectedDivergent γ.1 γ.2)]
      rfl
    | false =>
      rw [Sum.elim_inl, cond_false, Finset.prod_empty, stableLocalLeftFactor_inl_false]
  | inr B =>
    rw [Sum.elim_inr, stableLocalLeftFactor_inr, stableLeftAggregate_eq_prod,
      Finset.prod_image (stableRootRelativeInner_injOn_elements γ.1 B.1
        (((mem_phi4WTriplePrimeIndex _ B.1).mp B.2).2.2.2.2.1).2.1)]
    have hO := (mem_phi4WTriplePrimeIndex G s.outer).mp s.outer_mem
    have hγsat : ResolvedExternalLegSaturated G γ.1 := hO.2.2.2.2.2.1 γ.1 γ.2
    have hEC : ResolvedInternalEdgeComplete γ.1 := hO.2.2.2.2.2.2 γ.1 γ.2
    have hB := (mem_phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph γ.1) B.1).mp B.2
    refine Finset.prod_congr rfl (fun δ hδ => ?_)
    have hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ.1) δ :=
      hB.2.2.2.2.2.1 δ hδ
    have hCDsub : δ.forget.IsConnectedDivergent := B.1.isConnectedDivergent δ hδ
    have hCDprom : (stableRootRelativeInner γ.1 δ).forget.IsConnectedDivergent :=
      (stableRootRelativeInner_closure s γ B hδ).1
    rw [stableLocalLeftGenTotal, stableLocalLeftGenTotal, dif_pos hCDsub, dif_pos hCDprom]
    exact stableForestLeftFactor_gen_eq_promoted γ.1 δ hγsat hδsat hEC _ _ _ _

/-- **body-632 (Step 5, HEADLINE 2) — the full stable LEFT-factor product.**  The branchwise outer left weight
`∏ γ stableLocalLeftFactor (s.choice γ)` equals the stable selectedOuter aggregate — the identity body-625's
no-go DENIED on the OLD carrier, now PROVED on the STABLE carrier.  Flatten the outer product over the
per-component contribution sets (`Finset.prod_biUnion`, pairwise-disjoint), match each contribution factor by
`stableLocalLeftFactor_eq_prod_contribSet`, and recognize the union as `(stableSelectedOuter s).elements`. -/
theorem stableSelectedOuter_leftFactor_product {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    (∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach,
        stableLocalLeftFactor hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
          (s.choice γ (Finset.mem_attach _ γ)))
      = stableLeftAggregate (stableSelectedOuter s) hSt := by
  rw [stableLeftAggregate_eq_prod, stableSelectedOuter_elements_eq_biUnion,
    Finset.prod_biUnion (stableContribSet_pairwiseDisjoint s)]
  exact Finset.prod_congr rfl (fun γ _ => stableLocalLeftFactor_eq_prod_contribSet s γ)

end GaugeGeometry.QFT.Combinatorial
