import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoubleTriplePrimeTopology

/-!
# QFT-R1-body-653b-2b — the strictness crown `W‴ ⊊ W″` (Figure 1, the FINAL body)

Body-653b-1 built the concrete 12-edge φ⁴ graph `phi4CarrierGapAmbient`, its outer subgraph
`phi4CarrierGapOuter` (10 edges, the two hidden root edges `h03,h14` omitted), the inner marginal
triangle `phi4CarrierGapInner`, the exact hidden defect `{h03,h14}` and the four degrees.  Body-653b-2a
delivered the NATIVE topology of those graphs — the two `IsConnectedDivergentFor` packages
(ambient self, boundary-completed-outer self) and the two forest-level `IsConnectedDivergent` facts
(outer, inner), all proved from explicit reachability / bridge-free witnesses, never transported from an
abstract divergence class.

This body creates NO new topology.  It loads the 2a witnesses onto the two singleton forests, proves
both W″ memberships, the fifth-axis (edge-completeness) FAILURE at `h03`, and crowns the strict inclusion.

## Steps (this file = 653b-2b, FINAL)

1. The two singleton forests `phi4CarrierGapOuterForest := ⟨{γ}⟩`,
   `phi4CarrierGapInnerForest := ⟨{δ}⟩` (via `singletonResolvedAdmissibleSubgraph`; CD from the 2a
   `_forget_isConnectedDivergent`, disjointness trivial for a singleton).
2. Properness + saturation of each forest: the five `IsProperForest` conjuncts by concrete card (outer —
   total & component `internalEdges.card = 10 > 0`, complement `{h03,h14}` card `2 > 0`; inner — `3 > 0`,
   complement `outerEdges + visibleCrossEdges` card `7 > 0`), and `ResolvedForestExternalLegSaturated`
   from the 653b-1 per-component saturation.
3. Both W″ memberships via `(mem_resolvedLegSaturatedIndexFor …).mpr` of the six conjuncts (ambient
   support proved directly; `EdgeIdsUnique` concrete; `LegIdsUnique` trivial — empty legs; CD = the 2a
   packages; properness/saturation = Step 2).
4. The `h03` fifth-axis failure: `count h03 (filtered ambient) = 1` but `count h03 γ.internalEdges = 0`,
   so `¬ ResolvedInternalEdgeComplete γ`, hence the singleton forest is not forest-edge-complete and
   `phi4CarrierGapOuterForest ∉ phi4WTriplePrimeIndex`.
5. The strictness crown `phi4CarrierGap_wTriplePrime_lt_wDoublePrime`, the existential
   `exists_mem_wDoublePrime_not_mem_wTriplePrime`, and the paper headline
   `phi4CarrierGap_strictness_with_marginal_defect`.

## Figure 1 (the caption, realized)

> The SAME concrete witness `phi4CarrierGapOuterForest` owns W″ membership, W‴ rejection, the marginal
> degree drop (`ω(δ) = 0` → root-relative `ω = −2`), and the exact hidden defect `{h03,h14}`.  The W‴
> edge-completeness condition excludes precisely this forest — `h03` has both endpoints inside `γ` but is
> not an internal edge of `γ`.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`; NO `Lean.ofReduceBool` — NO `native_decide`).
NO topology re-proof (every topological fact is a consumed 2a package).  ZERO forbidden divergence
classes in ANY declaration type.  Multiplicity-exact: the hidden defect `{h03,h14}` is kept as a
`Multiset` equality (`hiddenRootBoundary … = hiddenCrossEdges`), never weakened to card.  No coproduct /
body-556 / evaluation; no `HEq` / `cast` / graph-data `▸` (the only `▸`/`rw` on equalities are on
`Prop`-level Finset membership); no cross-ambient subgraph `Eq`.  One file-local `local instance` (never
global); ZERO new `structure` / `class` / global `instance`; bodies ≤653b-2a UNEDITED.  W‴ is NOT claimed
to equal the defect-zero sector, and `defect = 0 → edge-complete` is NOT claimed.

**This is the FINAL body** — membership and the strictness headline live together here.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

/-- **body-653b-2b — file-local φ⁴ divergence-measure family instance** (same value as 653b-2a). -/
local instance instPhi4DivergenceMeasureFamily653b2b :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## Step 1 — the two singleton forests -/

/-- **body-653b-2b (Step 1) — the outer singleton forest** `A := {γ}` on the ambient. -/
noncomputable def phi4CarrierGapOuterForest :
    ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily phi4CarrierGapAmbient :=
  singletonResolvedAdmissibleSubgraph phi4CarrierGapOuter
    phi4CarrierGapOuter_forget_isConnectedDivergent

/-- **body-653b-2b (Step 1) — the inner singleton forest** `B := {δ}` on the boundary-completed outer
ambient. -/
noncomputable def phi4CarrierGapInnerForest :
    ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
      phi4CarrierGapOuter.boundaryCompletedResolvedGraph :=
  singletonResolvedAdmissibleSubgraph phi4CarrierGapInner
    phi4CarrierGapInner_forget_isConnectedDivergent

/-- Outer forest aggregate internal edges = the single component's internal edges. -/
theorem phi4CarrierGapOuterForest_internalEdges :
    phi4CarrierGapOuterForest.internalEdges = phi4CarrierGapOuter.internalEdges := by
  show (singletonResolvedAdmissibleSubgraph phi4CarrierGapOuter
    phi4CarrierGapOuter_forget_isConnectedDivergent).internalEdges = _
  exact singletonResolvedAdmissibleSubgraph_internalEdges _ _

/-- Inner forest aggregate internal edges = the single component's internal edges. -/
theorem phi4CarrierGapInnerForest_internalEdges :
    phi4CarrierGapInnerForest.internalEdges = phi4CarrierGapInner.internalEdges := by
  show (singletonResolvedAdmissibleSubgraph phi4CarrierGapInner
    phi4CarrierGapInner_forget_isConnectedDivergent).internalEdges = _
  exact singletonResolvedAdmissibleSubgraph_internalEdges _ _

/-- **body-653b-2b — the outer forest complement is exactly the hidden defect `{h03,h14}`.**  The ambient
has the 12 edges, the outer forest carries the 10 non-hidden edges, so the multiset difference is exactly
`hiddenCrossEdges`.  EXACT Multiset equality — not weakened to card. -/
theorem phi4CarrierGapOuterForest_complementEdges :
    phi4CarrierGapOuterForest.complementEdges = hiddenCrossEdges := by
  show phi4CarrierGapAmbient.internalEdges - phi4CarrierGapOuterForest.internalEdges = hiddenCrossEdges
  rw [phi4CarrierGapOuterForest_internalEdges]
  show (innerEdges + outerEdges + visibleCrossEdges + hiddenCrossEdges)
      - (innerEdges + outerEdges + visibleCrossEdges) = hiddenCrossEdges
  rw [add_tsub_cancel_left]

/-- **body-653b-2b — the inner forest complement is `outerEdges + visibleCrossEdges` (seven edges).** -/
theorem phi4CarrierGapInnerForest_complementEdges :
    phi4CarrierGapInnerForest.complementEdges = outerEdges + visibleCrossEdges := by
  show phi4CarrierGapOuter.boundaryCompletedResolvedGraph.internalEdges
      - phi4CarrierGapInnerForest.internalEdges = outerEdges + visibleCrossEdges
  rw [phi4CarrierGapInnerForest_internalEdges, boundaryCompletedResolvedGraph_internalEdges]
  show (innerEdges + outerEdges + visibleCrossEdges) - innerEdges = outerEdges + visibleCrossEdges
  rw [add_assoc, add_tsub_cancel_left]

/-! ## Step 2 — properness + saturation -/

/-- **body-653b-2b (Step 2) — the outer singleton forest is a proper forest.**  Nonempty, one nonempty
component, `10 > 0` total & component internal edges, complement `{h03,h14}` card `2 > 0`. -/
theorem phi4CarrierGapOuterForest_isProperForest :
    phi4CarrierGapOuterForest.IsProperForest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- IsNonempty
    exact Finset.singleton_nonempty _
  · -- HasNonemptyComponents
    intro γ hγ
    have hγ' : γ ∈ ({phi4CarrierGapOuter} : Finset (ResolvedFeynmanSubgraph phi4CarrierGapAmbient)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    show 0 < phi4CarrierGapOuter.vertices.card
    decide
  · -- total internal edges
    rw [phi4CarrierGapOuterForest_internalEdges]; decide
  · -- HasPositiveInternalEdgesComponents
    intro γ hγ
    have hγ' : γ ∈ ({phi4CarrierGapOuter} : Finset (ResolvedFeynmanSubgraph phi4CarrierGapAmbient)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    decide
  · -- complement edges card
    rw [phi4CarrierGapOuterForest_complementEdges]; decide

/-- **body-653b-2b (Step 2) — the inner singleton forest is a proper forest.**  Nonempty, one nonempty
component, `3 > 0` total & component internal edges, complement `outerEdges + visibleCrossEdges` card
`7 > 0`. -/
theorem phi4CarrierGapInnerForest_isProperForest :
    phi4CarrierGapInnerForest.IsProperForest := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.singleton_nonempty _
  · intro γ hγ
    have hγ' : γ ∈ ({phi4CarrierGapInner} :
        Finset (ResolvedFeynmanSubgraph phi4CarrierGapOuter.boundaryCompletedResolvedGraph)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    show 0 < phi4CarrierGapInner.vertices.card
    decide
  · rw [phi4CarrierGapInnerForest_internalEdges]; decide
  · intro γ hγ
    have hγ' : γ ∈ ({phi4CarrierGapInner} :
        Finset (ResolvedFeynmanSubgraph phi4CarrierGapOuter.boundaryCompletedResolvedGraph)) := hγ
    rw [Finset.mem_singleton] at hγ'
    subst hγ'
    decide
  · rw [phi4CarrierGapInnerForest_complementEdges]; decide

/-- **body-653b-2b (Step 2) — the outer forest is external-leg saturated** (its single component is). -/
theorem phi4CarrierGapOuterForest_saturated :
    ResolvedForestExternalLegSaturated phi4CarrierGapOuterForest := by
  intro δ hδ
  have hδ' : δ ∈ ({phi4CarrierGapOuter} : Finset (ResolvedFeynmanSubgraph phi4CarrierGapAmbient)) := hδ
  rw [Finset.mem_singleton] at hδ'
  subst hδ'
  exact phi4CarrierGap_outer_saturated

/-- **body-653b-2b (Step 2) — the inner forest is external-leg saturated.** -/
theorem phi4CarrierGapInnerForest_saturated :
    ResolvedForestExternalLegSaturated phi4CarrierGapInnerForest := by
  intro δ hδ
  have hδ' : δ ∈ ({phi4CarrierGapInner} :
      Finset (ResolvedFeynmanSubgraph phi4CarrierGapOuter.boundaryCompletedResolvedGraph)) := hδ
  rw [Finset.mem_singleton] at hδ'
  subst hδ'
  exact phi4CarrierGap_inner_saturated

/-! ## Step 2b — the ambient gates (support + id-uniqueness) -/

/-- **body-653b-2b — the ambient is ambient-supported** (all 12 edges endpoint-supported, no legs). -/
theorem phi4CarrierGapAmbient_ambientSupported :
    ResolvedAmbientSupported phi4CarrierGapAmbient := by
  refine ⟨?_, ?_⟩
  · intro e he
    fin_cases he <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-653b-2b — the ambient has unique edge ids** (edgeIds `0..11` all distinct). -/
theorem phi4CarrierGapAmbient_edgeIdsUnique : phi4CarrierGapAmbient.EdgeIdsUnique := by
  intro e₁ h₁ e₂ h₂ hid
  fin_cases h₁ <;> fin_cases h₂ <;> revert hid <;> decide

/-- **body-653b-2b — the ambient has unique leg ids** (no external legs — trivially). -/
theorem phi4CarrierGapAmbient_legIdsUnique : phi4CarrierGapAmbient.LegIdsUnique := by
  intro ℓ₁ h₁ ℓ₂ h₂ hid
  exact absurd h₁ (Multiset.notMem_zero ℓ₁)

/-- **body-653b-2b — the boundary-completed outer ambient is ambient-supported.** -/
theorem phi4CarrierGapInnerAmbient_supported :
    ResolvedAmbientSupported phi4CarrierGapOuter.boundaryCompletedResolvedGraph := by
  refine ⟨?_, ?_⟩
  · intro e he
    rw [boundaryCompletedResolvedGraph_internalEdges] at he
    simp only [boundaryCompletedResolvedGraph_vertices]
    fin_cases he <;> exact ⟨by decide, by decide⟩
  · intro ℓ hℓ
    rw [boundaryCompletedResolvedGraph_externalLegs,
      phi4CarrierGapOuter_boundaryCompletedResolvedExternalLegs] at hℓ
    exact absurd hℓ (Multiset.notMem_zero ℓ)

/-- **body-653b-2b — the boundary-completed outer ambient has unique edge ids** (inherited from the
ambient's edge-id uniqueness — the internal edges are the ambient's). -/
theorem phi4CarrierGapInnerAmbient_edgeIdsUnique :
    phi4CarrierGapOuter.boundaryCompletedResolvedGraph.EdgeIdsUnique :=
  boundaryCompletedResolvedGraph_edgeIdsUnique phi4CarrierGapOuter phi4CarrierGapAmbient_edgeIdsUnique

/-- **body-653b-2b — the boundary-completed outer ambient has unique leg ids** (empty legs). -/
theorem phi4CarrierGapInnerAmbient_legIdsUnique :
    phi4CarrierGapOuter.boundaryCompletedResolvedGraph.LegIdsUnique := by
  intro ℓ₁ h₁ ℓ₂ h₂ hid
  rw [boundaryCompletedResolvedGraph_externalLegs,
    phi4CarrierGapOuter_boundaryCompletedResolvedExternalLegs] at h₁
  exact absurd h₁ (Multiset.notMem_zero ℓ₁)

/-! ## Step 3 — both W″ memberships -/

/-- **body-653b-2b (Step 3) — the outer forest lands in W″.** -/
theorem phi4CarrierGapOuterForest_mem_wDoublePrime :
    phi4CarrierGapOuterForest ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient :=
  (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily phi4CarrierGapAmbient phi4CarrierGapOuterForest).mpr
    ⟨phi4CarrierGapAmbient_ambientSupported,
     phi4CarrierGapAmbient_isConnectedDivergentFor,
     phi4CarrierGapAmbient_edgeIdsUnique,
     phi4CarrierGapAmbient_legIdsUnique,
     phi4CarrierGapOuterForest_isProperForest,
     phi4CarrierGapOuterForest_saturated⟩

/-- **body-653b-2b (Step 3) — the inner forest lands in W″** (on the boundary-completed outer ambient). -/
theorem phi4CarrierGapInnerForest_mem_wDoublePrime :
    phi4CarrierGapInnerForest ∈ phi4WDoublePrimeIndex phi4CarrierGapOuter.boundaryCompletedResolvedGraph :=
  (mem_resolvedLegSaturatedIndexFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily phi4CarrierGapOuter.boundaryCompletedResolvedGraph
    phi4CarrierGapInnerForest).mpr
    ⟨phi4CarrierGapInnerAmbient_supported,
     phi4CarrierGapOuter_boundaryCompleted_isConnectedDivergentFor,
     phi4CarrierGapInnerAmbient_edgeIdsUnique,
     phi4CarrierGapInnerAmbient_legIdsUnique,
     phi4CarrierGapInnerForest_isProperForest,
     phi4CarrierGapInnerForest_saturated⟩

/-! ## Step 4 — the `h03` fifth-axis failure -/

/-- **body-653b-2b (Step 4) — `h03` survives the doubly-inside filter of the ambient exactly once.**  Its
endpoints `0,3` are both inside `γ.vertices = {0,…,5}`, so the vertex-induced filter keeps it, and it
occurs once in the ambient. -/
theorem phi4CarrierGap_h03_filteredAmbient_count :
    (phi4CarrierGapAmbient.internalEdges.filter
      (fun e => e.source ∈ phi4CarrierGapOuter.vertices ∧ e.target ∈ phi4CarrierGapOuter.vertices)).count
      (phi4CarrierGapEdge 10 0 3) = 1 := by
  rw [Multiset.count_filter,
    if_pos (show (phi4CarrierGapEdge 10 0 3).source ∈ phi4CarrierGapOuter.vertices
      ∧ (phi4CarrierGapEdge 10 0 3).target ∈ phi4CarrierGapOuter.vertices from ⟨by decide, by decide⟩)]
  decide

/-- **body-653b-2b (Step 4) — `h03` is absent from the outer forest's internal edges.** -/
theorem phi4CarrierGap_h03_outer_count :
    phi4CarrierGapOuter.internalEdges.count (phi4CarrierGapEdge 10 0 3) = 0 := by decide

/-- **body-653b-2b (Step 4) — the outer subgraph is NOT internal-edge complete.**  The doubly-inside
ambient edge `h03` is not an internal edge of `γ` (`count 1 ≤ count 0` is false). -/
theorem phi4CarrierGapOuter_not_internalEdgeComplete :
    ¬ ResolvedInternalEdgeComplete phi4CarrierGapOuter := by
  intro h
  unfold ResolvedInternalEdgeComplete at h
  have hle := Multiset.count_le_of_le (phi4CarrierGapEdge 10 0 3) h
  rw [phi4CarrierGap_h03_filteredAmbient_count, phi4CarrierGap_h03_outer_count] at hle
  exact absurd hle (by decide)

/-- **body-653b-2b (Step 4) — the outer singleton forest is NOT forest-internal-edge complete.**  Its
only component `phi4CarrierGapOuter` fails edge-completeness. -/
theorem phi4CarrierGapOuterForest_not_internalEdgeComplete :
    ¬ ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily phi4CarrierGapOuterForest := by
  intro h
  refine phi4CarrierGapOuter_not_internalEdgeComplete (h phi4CarrierGapOuter ?_)
  show phi4CarrierGapOuter ∈ (singletonResolvedAdmissibleSubgraph phi4CarrierGapOuter
    phi4CarrierGapOuter_forget_isConnectedDivergent).elements
  rw [singletonResolvedAdmissibleSubgraph_elements]
  exact Finset.mem_singleton_self _

/-- **body-653b-2b (Step 4) — the outer forest is NOT in W‴.**  W‴ membership demands forest-internal-edge
completeness (the seventh conjunct), which fails at `h03`. -/
theorem phi4CarrierGapOuterForest_not_mem_wTriplePrime :
    phi4CarrierGapOuterForest ∉ phi4WTriplePrimeIndex phi4CarrierGapAmbient := by
  intro hmem
  have h := (mem_phi4WTriplePrimeIndex phi4CarrierGapAmbient phi4CarrierGapOuterForest).mp hmem
  exact phi4CarrierGapOuterForest_not_internalEdgeComplete h.2.2.2.2.2.2

/-! ## Step 5 — the strictness crown -/

/-- **body-653b-2b (Step 5) — the strict inclusion `W‴ ⊊ W″`** on the concrete ambient.  The general
inclusion is 653a; the witness `phi4CarrierGapOuterForest ∈ W″ \ W‴` makes it strict. -/
theorem phi4CarrierGap_wTriplePrime_lt_wDoublePrime :
    phi4WTriplePrimeIndex phi4CarrierGapAmbient < phi4WDoublePrimeIndex phi4CarrierGapAmbient := by
  refine lt_of_le_of_ne (phi4WTriplePrimeIndex_subset_wDoublePrime phi4CarrierGapAmbient) ?_
  intro heq
  apply phi4CarrierGapOuterForest_not_mem_wTriplePrime
  rw [heq]
  exact phi4CarrierGapOuterForest_mem_wDoublePrime

/-- **body-653b-2b (Step 5) — the strictness existential.**  There is a resolved forest in W″ but not in
W‴ (the concrete Figure-1 witness). -/
theorem exists_mem_wDoublePrime_not_mem_wTriplePrime :
    ∃ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G),
      A ∈ phi4WDoublePrimeIndex G ∧ A ∉ phi4WTriplePrimeIndex G :=
  ⟨phi4CarrierGapAmbient, phi4CarrierGapOuterForest,
    phi4CarrierGapOuterForest_mem_wDoublePrime, phi4CarrierGapOuterForest_not_mem_wTriplePrime⟩

/-! ## PAPER HEADLINE (653b-2b, Figure 1 crowned) -/

/-- **body-653b-2b (HEADLINE, Figure 1) — one concrete witness owns W″ membership, W‴ rejection, the
marginal degree drop, and the exact hidden defect.**  On the named 12-edge φ⁴ graph, the SAME forest
`phi4CarrierGapOuterForest` is in W″ but not in W‴; the inner triangle is marginal (`ω = 0`); the hidden
root boundary is EXACTLY the two omitted cross edges `{h03,h14}`; and root-relative reconstruction is NOT
divergent.  The last three conjuncts are exactly 653b-1's `phi4CarrierGap_marginal_contraction_failure`. -/
theorem phi4CarrierGap_strictness_with_marginal_defect :
    phi4CarrierGapOuterForest ∈ phi4WDoublePrimeIndex phi4CarrierGapAmbient
      ∧ phi4CarrierGapOuterForest ∉ phi4WTriplePrimeIndex phi4CarrierGapAmbient
      ∧ phi4CarrierGapInner.forget.phi4SuperficialDegree = 0
      ∧ hiddenRootBoundary phi4CarrierGapOuter phi4CarrierGapInner = hiddenCrossEdges
      ∧ ¬ (rootRelativeInner phi4CarrierGapOuter phi4CarrierGapInner).forget.IsDivergent :=
  ⟨phi4CarrierGapOuterForest_mem_wDoublePrime,
   phi4CarrierGapOuterForest_not_mem_wTriplePrime,
   phi4CarrierGap_marginal_contraction_failure.1,
   phi4CarrierGap_marginal_contraction_failure.2.1,
   phi4CarrierGap_marginal_contraction_failure.2.2⟩

end GaugeGeometry.QFT.Combinatorial
