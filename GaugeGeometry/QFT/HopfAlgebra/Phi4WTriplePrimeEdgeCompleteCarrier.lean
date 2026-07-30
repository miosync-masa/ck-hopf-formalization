import GaugeGeometry.QFT.HopfAlgebra.Phi4StableNestedCDLanding
import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeFiniteIndex

/-!
# QFT-R1-body-600 — internal-edge-complete fifth axis + hidden-boundary gate elimination

Body-599 MEASURED the deficit of the stable nested root lift: the induced boundary edges of
`R := rootRelativeInner γ δ` split (body-597) as `R.resolvedBoundaryEdges = inheritedOuter γ δ +
newRootBoundary γ δ`, and the residual `hiddenRootBoundary γ δ := newRootBoundary γ δ -
δ.resolvedBoundaryEdges` is the multiset of root-crossing edges the inner `δ` cannot see from inside
`H = γ.boundaryCompletedResolvedGraph`.  Body-599's verdict was that unconditional vanishing of this
deficit is genuinely absent from W″ membership, so the split-choice landing was left GATED by the
external axis `Phi4StableSplitChoiceBoundaryClosed`.

This body DEFINES the exact carrier that makes that measured deficit zero and DISCHARGES the gate:

```text
ResolvedInternalEdgeComplete γ  :=
  G.internalEdges.filter (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) ≤ γ.internalEdges
```

i.e. every ambient internal edge whose BOTH endpoints already land inside `γ` is already an internal
edge of `γ` (vertex-induced internal-edge completeness).  This is precisely the condition under which
the Step-2 identity

```text
R.resolvedBoundaryEdges = inheritedOuter γ δ + δ.resolvedBoundaryEdges
```

holds: an ambient internal edge with exactly one endpoint in `δ.vertices` and the other endpoint
*inside* `γ` (so NOT a `γ`-boundary edge, hence NOT inherited) contributes to `R`'s boundary with
multiplicity `count e G.internalEdges`; edge-completeness forces `count e γ.internalEdges =
count e G.internalEdges`, so it is captured verbatim by `δ.resolvedBoundaryEdges`.  Cancelling
`inheritedOuter` against the body-597 split then yields `newRootBoundary γ δ = δ.resolvedBoundaryEdges`,
i.e. `hiddenRootBoundary γ δ = 0`, i.e. `RootRelativeBoundaryClosed γ δ`.

The fifth axis is therefore NOT a new physics condition — it is the precise combinatorial carrier that
eliminates the body-599 measured deficit.  It is a HYPOTHESIS we filter/require: the fifth-axis finite
index `resolvedEdgeCompleteIndexFor` further filters the body-586 W″ index by
`ResolvedForestInternalEdgeComplete`, and its membership `iff` EXPOSES that predicate as a conjunct.
We do NOT claim W″ members are automatically edge-complete; the gate discharge is a THEOREM conditional
on the fifth axis.

## Contents

* Step 1 — `ResolvedInternalEdgeComplete` / `ResolvedForestInternalEdgeComplete` + the `count` helper.
* Step 2 — `rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete` (the exact induced-boundary
  equality; the MATHEMATICAL HEART, proved edge-by-edge on multiplicities).
* Step 3 — `resolvedInternalEdgeComplete_mapPerm_iff` (a CLEAN, instance-free `mapPerm` invariance;
  edge-completeness has no divergence content, so `filter`/`map` commute + `Multiset.map_le_map_iff`).
* Step 4 — `resolvedEdgeCompleteIndexFor` / `mem_resolvedEdgeCompleteIndexFor` (family-generic
  fifth-axis finite index) + φ⁴ specialization `phi4WTriplePrimeIndex` / `mem_phi4WTriplePrimeIndex`.
* Step 5 — `newRootBoundary_eq_delta_of_edgeComplete` / `rootRelativeBoundaryClosed_of_edgeComplete` /
  `hiddenRootBoundary_eq_zero_of_edgeComplete`.
* Step 6 — `phi4StableSplitChoiceBoundaryClosed_of_forestEdgeComplete` (automatic discharge of the
  body-599 split-choice gate) + `phi4StableSplitChoiceBoundaryClosed_of_outer_mem_index` (extraction
  of the fifth axis from index membership).

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `...ByAdmissibleForestContract` /
`IsDivergenceReflectedByAdmissibleForestContract`) in ANY declaration's type; the polluted
`resolvedExternalLegSaturated_mapPerm_iff` is NOT consumed — the Step-3 `mapPerm` iff is re-derived
CLEAN.  Multiplicity-safe throughout (`Multiset`, no `Finset` dedup).  No `selectedOuter` / `promote` /
forest_block / alpha / coassoc; no coproduct owner re-issue (that is body-601).  The only
divergence-flavored binders are the explicit `D : DivergenceMeasureFamily` /
`PermInvariantDivergenceMeasureFamily D` and the concrete φ⁴ families.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — the fifth-axis predicates -/

/-- **body-600 (Step 1) — vertex-induced internal-edge completeness.**  Every ambient internal edge
whose BOTH endpoints already land inside `γ.vertices` is already an internal edge of `γ`.  Multiplicity
exact (`Multiset` `≤`). -/
def ResolvedInternalEdgeComplete (γ : ResolvedFeynmanSubgraph G) : Prop :=
  G.internalEdges.filter (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices) ≤ γ.internalEdges

/-- **body-600 (Step 1) — forest-level internal-edge completeness.**  Every component of the resolved
admissible forest `A` is internal-edge complete. -/
def ResolvedForestInternalEdgeComplete (D : DivergenceMeasureFamily)
    (A : @ResolvedAdmissibleSubgraph D G) : Prop :=
  ∀ γ : ResolvedFeynmanSubgraph G, γ ∈ @ResolvedAdmissibleSubgraph.elements D G A
    → ResolvedInternalEdgeComplete γ

/-- **body-600 (Step 1) — `count` form of edge-completeness.**  If both endpoints of `e` lie inside
`γ.vertices`, then `count e G.internalEdges ≤ count e γ.internalEdges`.  Together with the reverse
`count_le_of_le e γ.internalEdges_le` this pins EQUALITY on doubly-inside edges. -/
theorem resolvedInternalEdgeComplete_count {γ : ResolvedFeynmanSubgraph G}
    (hEC : ResolvedInternalEdgeComplete γ) {e : ResolvedFeynmanEdge}
    (hs : e.source ∈ γ.vertices) (ht : e.target ∈ γ.vertices) :
    Multiset.count e G.internalEdges ≤ Multiset.count e γ.internalEdges := by
  unfold ResolvedInternalEdgeComplete at hEC
  have h := Multiset.count_le_of_le e hEC
  simpa only [Multiset.count_filter,
    if_pos (show e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices from ⟨hs, ht⟩)] using h

/-! ## Step 2 — the exact induced-boundary equality (MATHEMATICAL HEART) -/

/-- **body-600 (Step 2, HEART) — under edge-completeness the induced boundary of the root lift splits
exactly.**  `R.resolvedBoundaryEdges = inheritedOuter γ δ + δ.resolvedBoundaryEdges`, proved edge-by-edge
on multiplicities.  The ONLY place edge-completeness is used is the doubly-inside sub-case, where it
forces `count e G.internalEdges = count e γ.internalEdges`. -/
theorem rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (rootRelativeInner γ δ).resolvedBoundaryEdges = inheritedOuter γ δ + δ.resolvedBoundaryEdges := by
  have hsub : δ.vertices ⊆ γ.vertices := δ.vertices_subset
  have hR : (rootRelativeInner γ δ).resolvedBoundaryEdges
      = G.internalEdges.filter δ.resolvedIsBoundaryEdge := by
    unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    exact Multiset.filter_congr (fun e _ => Iff.rfl)
  have hInh : inheritedOuter γ δ
      = G.internalEdges.filter
          (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e) := by
    unfold inheritedOuter ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    rw [Multiset.filter_filter]
  have hδB : δ.resolvedBoundaryEdges = γ.internalEdges.filter δ.resolvedIsBoundaryEdge := rfl
  rw [hR, hInh, hδB]
  refine Multiset.ext.mpr (fun e => ?_)
  simp only [Multiset.count_add, Multiset.count_filter]
  by_cases hbd : δ.resolvedIsBoundaryEdge e
  · -- boundary for `δ`: exactly one endpoint of `e` is in `δ.vertices`
    simp only [if_pos hbd]
    rcases hbd with ⟨hsδ, htδ⟩ | ⟨hsδ, htδ⟩
    · -- inside endpoint is `e.source`
      have hsγ : e.source ∈ γ.vertices := hsub hsδ
      have hins : γ.resolvedInsideEndpoint e ∈ δ.vertices := by
        show (if e.source ∈ γ.vertices then e.source else e.target) ∈ δ.vertices
        rw [if_pos hsγ]; exact hsδ
      by_cases htγ : e.target ∈ γ.vertices
      · -- both endpoints inside `γ`: NOT a `γ`-boundary edge; edge-completeness gives cG = cγ
        have hnbd : ¬ γ.resolvedIsBoundaryEdge e := by
          rintro (⟨_, ht'⟩ | ⟨hs', _⟩)
          · exact ht' htγ
          · exact hs' hsγ
        rw [if_neg (fun hC => hnbd hC.2), zero_add]
        exact le_antisymm (resolvedInternalEdgeComplete_count hEC hsγ htγ)
          (Multiset.count_le_of_le e γ.internalEdges_le)
      · -- `e.target` outside `γ`: a fresh `γ`-boundary edge; `count e γ.internalEdges = 0`
        have hCe : γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e :=
          ⟨hins, Or.inl ⟨hsγ, htγ⟩⟩
        have hz : Multiset.count e γ.internalEdges = 0 :=
          Multiset.count_eq_zero.mpr (fun hmem => htγ (γ.edges_supported e hmem).2)
        rw [if_pos hCe, hz, add_zero]
    · -- inside endpoint is `e.target`
      have htγ : e.target ∈ γ.vertices := hsub htδ
      by_cases hsγ : e.source ∈ γ.vertices
      · -- both endpoints inside `γ`: NOT a `γ`-boundary edge; edge-completeness gives cG = cγ
        have hnbd : ¬ γ.resolvedIsBoundaryEdge e := by
          rintro (⟨_, ht'⟩ | ⟨hs', _⟩)
          · exact ht' htγ
          · exact hs' hsγ
        rw [if_neg (fun hC => hnbd hC.2), zero_add]
        exact le_antisymm (resolvedInternalEdgeComplete_count hEC hsγ htγ)
          (Multiset.count_le_of_le e γ.internalEdges_le)
      · -- `e.source` outside `γ`: a fresh `γ`-boundary edge; `count e γ.internalEdges = 0`
        have hins : γ.resolvedInsideEndpoint e ∈ δ.vertices := by
          show (if e.source ∈ γ.vertices then e.source else e.target) ∈ δ.vertices
          rw [if_neg hsγ]; exact htδ
        have hCe : γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e :=
          ⟨hins, Or.inr ⟨hsγ, htγ⟩⟩
        have hz : Multiset.count e γ.internalEdges = 0 :=
          Multiset.count_eq_zero.mpr (fun hmem => hsγ (γ.edges_supported e hmem).1)
        rw [if_pos hCe, hz, add_zero]
  · -- NOT a `δ`-boundary edge: all three summands vanish
    have hnC : ¬ (γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e) := by
      rintro ⟨hin, hbg⟩
      apply hbd
      show (e.source ∈ δ.vertices ∧ e.target ∉ δ.vertices) ∨
           (e.source ∉ δ.vertices ∧ e.target ∈ δ.vertices)
      rcases hbg with ⟨hsγ, htγ⟩ | ⟨hsγ, htγ⟩
      · have hval : γ.resolvedInsideEndpoint e = e.source := if_pos hsγ
        rw [hval] at hin
        exact Or.inl ⟨hin, fun hc => htγ (hsub hc)⟩
      · have hval : γ.resolvedInsideEndpoint e = e.target := if_neg hsγ
        rw [hval] at hin
        exact Or.inr ⟨fun hc => hsγ (hsub hc), hin⟩
    simp only [if_neg hbd]
    rw [add_zero, if_neg hnC]

/-! ## Step 3 — clean `mapPerm` invariance (instance-free) -/

/-- **body-600 (Step 3) — edge-completeness is invariant under vertex relabeling.**  Edge-completeness
carries NO divergence content, so this is CLEAN (no forbidden-class binder): the doubly-inside filter
commutes with `map (ResolvedFeynmanEdge.map σ)` (endpoints relabel by the injective `σ`, so membership
in the relabeled vertex image reduces via `mem_finset_image`), and `Multiset.map_le_map_iff` peels the
injective `map` off the `≤`.  Re-derived clean — NOT via the polluted
`resolvedExternalLegSaturated_mapPerm_iff`. -/
theorem resolvedInternalEdgeComplete_mapPerm_iff (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    ResolvedInternalEdgeComplete (γ.mapPerm σ) ↔ ResolvedInternalEdgeComplete γ := by
  -- CLEAN re-derivation of the edge-map injectivity (the library `ResolvedFeynmanEdge.map_injective`
  -- carries an unused `DivergenceMeasure` section-variable binder, so it is not consumed here).
  have hmapinj : Function.Injective (ResolvedFeynmanEdge.map σ) := by
    intro a b hab; cases a; cases b
    simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanEdge.mk.injEq] at hab
    obtain ⟨hid, hsrc, htgt, hsec⟩ := hab
    exact ResolvedFeynmanEdge.mk.injEq .. |>.mpr ⟨hid, σ.injective hsrc, σ.injective htgt, hsec⟩
  have hfm : (G.internalEdges.map (ResolvedFeynmanEdge.map σ)).filter
        (fun e => e.source ∈ γ.vertices.image σ ∧ e.target ∈ γ.vertices.image σ)
      = (G.internalEdges.filter (fun e => e.source ∈ γ.vertices ∧ e.target ∈ γ.vertices)).map
          (ResolvedFeynmanEdge.map σ) := by
    rw [Multiset.filter_map]
    exact congrArg (Multiset.map (ResolvedFeynmanEdge.map σ))
      (Multiset.filter_congr (fun e _ =>
        and_congr σ.injective.mem_finset_image σ.injective.mem_finset_image))
  simp only [ResolvedInternalEdgeComplete, ResolvedFeynmanGraph.mapPerm,
    ResolvedFeynmanSubgraph.mapPerm_internalEdges, ResolvedFeynmanSubgraph.mapPerm_vertices, hfm,
    Multiset.map_le_map_iff hmapinj]

/-! ## Step 4 — the fifth-axis filtered index + membership iff -/

/-- **body-600 (Step 4) — the family-generic fifth-axis finite index.**  The body-586 W″ index further
filtered by forest-level internal-edge completeness. -/
noncomputable def resolvedEdgeCompleteIndexFor (D : DivergenceMeasureFamily)
    (Inv : PermInvariantDivergenceMeasureFamily D) (G : ResolvedFeynmanGraph) :
    Finset (ResolvedAdmissibleSubgraphFor D G) :=
  (resolvedLegSaturatedIndexFor D Inv G).filter (fun A => ResolvedForestInternalEdgeComplete D A)

/-- **body-600 (Step 4) — fifth-axis membership criterion.**  A forest `A` lands in the fifth-axis index
iff the four ambient gates hold, `A` is a proper externally-leg-saturated forest, AND `A` is
forest-internal-edge complete.  The edge-completeness conjunct is EXPOSED (never claimed automatic from
W″ membership). -/
theorem mem_resolvedEdgeCompleteIndexFor (D : DivergenceMeasureFamily)
    (Inv : PermInvariantDivergenceMeasureFamily D) (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraphFor D G) :
    A ∈ resolvedEdgeCompleteIndexFor D Inv G ↔
      ResolvedAmbientSupported G
        ∧ ResolvedFeynmanGraphClass.IsConnectedDivergentFor D Inv G.toResolvedClass
        ∧ G.EdgeIdsUnique ∧ G.LegIdsUnique
        ∧ A.IsProperForest ∧ ResolvedForestExternalLegSaturated A
        ∧ ResolvedForestInternalEdgeComplete D A := by
  unfold resolvedEdgeCompleteIndexFor
  rw [Finset.mem_filter, mem_resolvedLegSaturatedIndexFor]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩; exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7⟩

/-- **body-600 (Step 4) — the φ⁴ fifth-axis (W‴) finite index.** -/
noncomputable def phi4WTriplePrimeIndex (G : ResolvedFeynmanGraph) :
    Finset (ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :=
  resolvedEdgeCompleteIndexFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily G

/-- **body-600 (Step 4) — φ⁴ fifth-axis membership criterion.** -/
theorem mem_phi4WTriplePrimeIndex (G : ResolvedFeynmanGraph)
    (A : ResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    A ∈ phi4WTriplePrimeIndex G ↔
      ResolvedAmbientSupported G
        ∧ ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily G.toResolvedClass
        ∧ G.EdgeIdsUnique ∧ G.LegIdsUnique
        ∧ @ResolvedAdmissibleSubgraph.IsProperForest phi4DivergenceMeasureFamily G A
        ∧ @ResolvedForestExternalLegSaturated phi4DivergenceMeasureFamily G A
        ∧ ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily A := by
  unfold phi4WTriplePrimeIndex
  rw [mem_resolvedEdgeCompleteIndexFor]

/-! ## Step 5 — fifth-axis membership ⇒ boundary closed -/

/-- **body-600 (Step 5) — under edge-completeness the fresh root boundary equals `δ`'s own boundary.**
Cancel `inheritedOuter` between the body-597 split and the Step-2 equality. -/
theorem newRootBoundary_eq_delta_of_edgeComplete (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hEC : ResolvedInternalEdgeComplete γ) :
    newRootBoundary γ δ = δ.resolvedBoundaryEdges := by
  have h597 : (rootRelativeInner γ δ).resolvedBoundaryEdges
      = inheritedOuter γ δ + newRootBoundary γ δ := by
    unfold newRootBoundary
    rw [add_tsub_cancel_of_le (inheritedOuter_le_R_resolvedBoundaryEdges γ δ)]
  have hEC' := rootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete γ δ hEC
  exact add_left_cancel (h597.symm.trans hEC')

/-- **body-600 (Step 5, HEADLINE) — edge-completeness discharges the body-599 boundary-closed gate.** -/
theorem rootRelativeBoundaryClosed_of_edgeComplete (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hEC : ResolvedInternalEdgeComplete γ) :
    RootRelativeBoundaryClosed γ δ :=
  (rootRelativeBoundaryClosed_iff γ δ).mpr (newRootBoundary_eq_delta_of_edgeComplete γ δ hEC)

/-- **body-600 (Step 5) — the hidden root boundary vanishes under edge-completeness.**  (This IS
`RootRelativeBoundaryClosed γ δ` unfolded.) -/
theorem hiddenRootBoundary_eq_zero_of_edgeComplete (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hEC : ResolvedInternalEdgeComplete γ) :
    hiddenRootBoundary γ δ = 0 :=
  rootRelativeBoundaryClosed_of_edgeComplete γ δ hEC

/-! ## Step 6 — automatic discharge of the body-599 split-choice gate -/

/-- **body-600 (Step 6, HEADLINE) — forest edge-completeness discharges the split-choice gate.**  If
every outer component of the filtered split choice is internal-edge complete, then the split-choice
boundary-closed gate `Phi4StableSplitChoiceBoundaryClosed` holds.  The δ-saturation binder of the gate
is IGNORED — edge-completeness of `γ` alone kills the hidden root boundary. -/
theorem phi4StableSplitChoiceBoundaryClosed_of_forestEdgeComplete
    (s : Phi4FilteredCoassocSplitChoice G)
    (hEC : ResolvedForestInternalEdgeComplete phi4DivergenceMeasureFamily s.outer) :
    Phi4StableSplitChoiceBoundaryClosed s := by
  intro γ hγ δ _hδsat
  exact rootRelativeBoundaryClosed_of_edgeComplete γ δ (hEC γ hγ)

/-- **body-600 (Step 6) — the fifth axis extracted from index membership discharges the gate.**  A split
choice whose `outer` lands in the φ⁴ fifth-axis index satisfies the split-choice boundary-closed gate;
the required `ResolvedForestInternalEdgeComplete` is pulled off the index membership `iff`. -/
theorem phi4StableSplitChoiceBoundaryClosed_of_outer_mem_index
    (s : Phi4FilteredCoassocSplitChoice G)
    (h : s.outer ∈ phi4WTriplePrimeIndex G) :
    Phi4StableSplitChoiceBoundaryClosed s :=
  phi4StableSplitChoiceBoundaryClosed_of_forestEdgeComplete s
    ((mem_phi4WTriplePrimeIndex G s.outer).mp h).2.2.2.2.2.2

end GaugeGeometry.QFT.Combinatorial
