import GaugeGeometry.QFT.HopfAlgebra.Phi4StableResolvedHopfCoproduct

/-!
# QFT-R1-body-630 — the stable-carrier LEFT-factor product (rebuilding what body-625 broke)

Body-625 proved a class-level **no-go**: the naive nested completion `δ.boundaryCompletedResolvedGraph`
re-encodes an inherited outer boundary leg EVEN locally while the root-direct route keeps it ODD, so the
per-occurrence left-factor generators disagree and the full left-factor product identity CANNOT be emitted
on the old carrier.  Body-628 answered the profile obstruction with an IDEMPOTENCE law on the stable
completion (as a DESIGN PRINCIPLE).  Body-629 built the PARALLEL stable resolved Hopf carrier
(`stableLocalBoundaryCompletedGraph`, `StableResolvedPhi4HopfGen`, `stableLeftAggregate`).

This body **rebuilds — on the STABLE carrier — the left-factor product that body-625 broke**, turning that
breakage from an "avoidance" into a design theorem: the same computation now HOLDS on the normal form.

## The TYPE correction (obeyed)

The second index sits on `stableLocalBoundaryCompletedGraph γ` (body-629's ZERO-re-encode completion), NOT
the old `γ.boundaryCompletedResolvedGraph`.  Body-628's idempotence is consumed as a DESIGN PRINCIPLE only;
we prove the STABLE-LOCAL version from scratch (it is a DIFFERENT type, so no `rw` of body-628).

## Steps

* Step 1 — the coassoc-ready stable choice: `StableLocalForestIdx γ` (a live W‴ carrier member over
  `stableLocalBoundaryCompletedGraph γ`) and the ONE new structure `StablePhi4ResolvedSplitChoice`.
* Step 2 — the stable-local root lift `stableRootRelativeInner γ δ` (a `ResolvedFeynmanSubgraph G`) and the
  LOAD-BEARING RAW graph idempotence `stableLocalBoundaryIterate_idempotent :
  stableLocalBoundaryCompletedGraph δ = stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)`.
  The exact multiset decomposition keeps inherited legs VERBATIM and adds each fresh cut leg exactly ONCE.
* Step 3 — the stable local left factor `stableLocalLeftFactor` (LEFT primitive / RIGHT unit / FOREST
  aggregate) and the FOREST component match `stableForestLeftFactor_component_eq_promoted`, lifting Step 2's
  raw equality to a generator equality through body-629's `toStableResolvedPhi4HopfGen_class_eq`.

## HALT / red lines
body-625's no-go, the OLD carrier / OLD coproduct / OLD split-choice, and every existing file are UNEDITED.
NO equality / Equiv / cast bridge between the OLD split-choice / local left factor and the new ones.  Body
-628's `stableBoundaryIterate_idempotent` is NOT `rw`-consumed (type mismatch); the stable-local version is
proved directly.  NO `HEq` / graph-data transport / strict star equality.  Right-factor product / `quot_eq`
/ summand agreement / coassoc are NOT entered.  EXACTLY ONE new `structure` (`StablePhi4ResolvedSplitChoice`);
ZERO new `class` / `instance` (only a file-local `local instance` for the φ⁴ divergence family, mirroring
body-629).  ZERO forbidden divergence classes in any declaration TYPE; ZERO `sorry` / `admit` /
`native_decide`.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family (mirrors body-629), so the
resolved admissible-subgraph / carrier plumbing elaborates against the φ⁴ family. -/
local instance instPhi4DivergenceMeasureFamily630 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the coassoc-ready stable choice -/

/-- **body-630 (Step 1) — a live W‴ inner forest index over the STABLE local completion.**  A resolved
admissible forest of `stableLocalBoundaryCompletedGraph γ` that is a fifth-axis W‴ carrier member.  The
second index lives on the stable completion (ZERO re-encode), NOT the old `boundaryCompletedResolvedGraph`. -/
def StableLocalForestIdx (γ : ResolvedFeynmanSubgraph G) : Type :=
  { B : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph γ) //
      B ∈ phi4WTriplePrimeIndex (stableLocalBoundaryCompletedGraph γ) }

/-- **body-630 (Step 1) — the stable resolved φ⁴ split choice.**  A live outer W‴ forest with, per outer
component, a `Bool ⊕ StableLocalForestIdx γ` leg (LEFT/RIGHT primitive or a live stable inner forest), plus
a global non-triviality (the split is not the all-primitive-right choice).  NO cast / Equiv to the OLD
`Phi4EdgeCompleteFilteredCoassocSplitChoice`. -/
structure StablePhi4ResolvedSplitChoice (G : ResolvedFeynmanGraph) (hSt : StableResolvedBoundaryIds G) where
  /-- The outer W‴ (edge-complete) forest. -/
  outer : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
  /-- The outer forest is a live W‴ carrier member. -/
  outer_mem : outer ∈ phi4WTriplePrimeIndex G
  /-- Per outer component, a stable local choice: a primitive `Bool` leg or a live stable inner forest. -/
  choice : (γ : {x // x ∈ @ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer}) →
    γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G outer).attach →
      Bool ⊕ StableLocalForestIdx γ.1
  /-- Global choice validity: the split lives in the non-pure region (some component is not RIGHT). -/
  choice_nontrivial : ∃ a hatt, choice a hatt ≠ Sum.inl false

/-! ## Step 2 — the stable-local root lift + the RAW idempotence (LOAD-BEARING) -/

/-- **body-630 (Step 2) — the stable-local root lift.**  Lift a nested subgraph `δ` of the STABLE local
completion `stableLocalBoundaryCompletedGraph γ` back to a subgraph of the root `G`.  Vertices / internal
edges are `δ`'s verbatim (they already live at root coordinates); external legs are the root-`G` legs
saturating `δ`'s vertices.  It reads `δ` ONLY through `δ.vertices` / `δ.internalEdges`. -/
noncomputable def stableRootRelativeInner (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) : ResolvedFeynmanSubgraph G where
  vertices := δ.vertices
  internalEdges := δ.internalEdges
  externalLegs := G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
  vertices_subset := fun _v hv => γ.vertices_subset (δ.vertices_subset hv)
  internalEdges_le := le_trans δ.internalEdges_le γ.internalEdges_le
  externalLegs_le := Multiset.filter_le _ _
  edges_supported := δ.edges_supported
  legs_supported := fun _ℓ hℓ => (Multiset.mem_filter.mp hℓ).2

@[simp] theorem stableRootRelativeInner_vertices (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).vertices = δ.vertices := rfl

@[simp] theorem stableRootRelativeInner_internalEdges (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).internalEdges = δ.internalEdges := rfl

@[simp] theorem stableRootRelativeInner_externalLegs (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) :
    (stableRootRelativeInner γ δ).externalLegs
      = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices) := rfl

/-- **body-630 (Step 2) — the inherited outer boundary edges (stable carrier).**  The root boundary edges of
`γ` whose `γ`-inside endpoint already lands inside `δ.vertices`.  These induce legs `δ` inherited verbatim —
they must NOT be recut. -/
noncomputable def stableInheritedOuter (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ)) : Multiset ResolvedFeynmanEdge :=
  γ.resolvedBoundaryEdges.filter (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices)

/-- **body-630 (Step 2, boundary split) — under edge-completeness the lift's induced boundary splits
exactly.**  `R.resolvedBoundaryEdges = stableInheritedOuter γ δ + δ.resolvedBoundaryEdges`, edge-by-edge on
multiplicities; edge-completeness enters ONLY in the doubly-inside sub-case (`count e G = count e γ`).  A
family-native re-derivation of body-600's split for the STABLE ambient (the boundary geometry reads only
`vertices` / `internalEdges`, which the stable completion shares with the old one). -/
theorem stableRootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hEC : ResolvedInternalEdgeComplete γ) :
    (stableRootRelativeInner γ δ).resolvedBoundaryEdges
      = stableInheritedOuter γ δ + δ.resolvedBoundaryEdges := by
  have hsub : δ.vertices ⊆ γ.vertices := δ.vertices_subset
  have hR : (stableRootRelativeInner γ δ).resolvedBoundaryEdges
      = G.internalEdges.filter δ.resolvedIsBoundaryEdge := by
    unfold ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    exact Multiset.filter_congr (fun e _ => Iff.rfl)
  have hInh : stableInheritedOuter γ δ
      = G.internalEdges.filter
          (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e) := by
    unfold stableInheritedOuter ResolvedFeynmanSubgraph.resolvedBoundaryEdges
    rw [Multiset.filter_filter]
  have hδB : δ.resolvedBoundaryEdges = γ.internalEdges.filter δ.resolvedIsBoundaryEdge := rfl
  rw [hR, hInh, hδB]
  refine Multiset.ext.mpr (fun e => ?_)
  simp only [Multiset.count_add, Multiset.count_filter]
  by_cases hbd : δ.resolvedIsBoundaryEdge e
  · simp only [if_pos hbd]
    rcases hbd with ⟨hsδ, htδ⟩ | ⟨hsδ, htδ⟩
    · have hsγ : e.source ∈ γ.vertices := hsub hsδ
      have hins : γ.resolvedInsideEndpoint e ∈ δ.vertices := by
        show (if e.source ∈ γ.vertices then e.source else e.target) ∈ δ.vertices
        rw [if_pos hsγ]; exact hsδ
      by_cases htγ : e.target ∈ γ.vertices
      · have hnbd : ¬ γ.resolvedIsBoundaryEdge e := by
          rintro (⟨_, ht'⟩ | ⟨hs', _⟩)
          · exact ht' htγ
          · exact hs' hsγ
        rw [if_neg (fun hC => hnbd hC.2), zero_add]
        exact le_antisymm (resolvedInternalEdgeComplete_count hEC hsγ htγ)
          (Multiset.count_le_of_le e γ.internalEdges_le)
      · have hCe : γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e :=
          ⟨hins, Or.inl ⟨hsγ, htγ⟩⟩
        have hz : Multiset.count e γ.internalEdges = 0 :=
          Multiset.count_eq_zero.mpr (fun hmem => htγ (γ.edges_supported e hmem).2)
        rw [if_pos hCe, hz, add_zero]
    · have htγ : e.target ∈ γ.vertices := hsub htδ
      by_cases hsγ : e.source ∈ γ.vertices
      · have hnbd : ¬ γ.resolvedIsBoundaryEdge e := by
          rintro (⟨_, ht'⟩ | ⟨hs', _⟩)
          · exact ht' htγ
          · exact hs' hsγ
        rw [if_neg (fun hC => hnbd hC.2), zero_add]
        exact le_antisymm (resolvedInternalEdgeComplete_count hEC hsγ htγ)
          (Multiset.count_le_of_le e γ.internalEdges_le)
      · have hins : γ.resolvedInsideEndpoint e ∈ δ.vertices := by
          show (if e.source ∈ γ.vertices then e.source else e.target) ∈ δ.vertices
          rw [if_neg hsγ]; exact htδ
        have hCe : γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e :=
          ⟨hins, Or.inr ⟨hsγ, htγ⟩⟩
        have hz : Multiset.count e γ.internalEdges = 0 :=
          Multiset.count_eq_zero.mpr (fun hmem => hsγ (γ.edges_supported e hmem).1)
        rw [if_pos hCe, hz, add_zero]
  · have hnC : ¬ (γ.resolvedInsideEndpoint e ∈ δ.vertices ∧ γ.resolvedIsBoundaryEdge e) := by
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

/-- **body-630 (Step 2) — on an inherited edge, the lift's induced leg equals `γ`'s.**  Both use the SAME
inside endpoint (the one inside `δ.vertices ⊆ γ.vertices`), the same odd `legId`, and the same sector.  A
family-native re-derivation of body-597's inherited-leg agreement for the stable carrier. -/
theorem stableBoundaryExternalLeg_agree_on_inherited (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    {e : ResolvedFeynmanEdge} (he : e ∈ stableInheritedOuter γ δ) :
    (stableRootRelativeInner γ δ).boundaryExternalLeg e = γ.boundaryExternalLeg e := by
  unfold stableInheritedOuter at he
  rw [Multiset.mem_filter] at he
  obtain ⟨_, hQ⟩ := he
  have hend : (stableRootRelativeInner γ δ).resolvedInsideEndpoint e = γ.resolvedInsideEndpoint e := by
    show (if e.source ∈ δ.vertices then e.source else e.target)
       = (if e.source ∈ γ.vertices then e.source else e.target)
    by_cases hs : e.source ∈ γ.vertices
    · rw [if_pos hs]
      have hsδ : e.source ∈ δ.vertices := by
        have h := hQ
        unfold ResolvedFeynmanSubgraph.resolvedInsideEndpoint at h
        rw [if_pos hs] at h; exact h
      rw [if_pos hsδ]
    · rw [if_neg hs]
      have hsδ : e.source ∉ δ.vertices := fun hc => hs (δ.vertices_subset hc)
      rw [if_neg hsδ]
  unfold ResolvedFeynmanSubgraph.boundaryExternalLeg
  rw [hend]

/-- **body-630 (Step 2, HEADLINE — the RAW idempotence body-625 could not have).**  Iterating the STABLE
local completion returns the ROOT normal form: a RAW `ResolvedFeynmanGraph` equality
`stableLocalBoundaryCompletedGraph δ = stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)`.
Vertices / internal edges are `δ`'s (rfl); the external legs decompose EXACTLY — the inherited legs are kept
VERBATIM (`δ.externalLegs` re-absorbs `stableInheritedOuter`'s legs via saturation) and each freshly-cut
root-boundary edge contributes its odd induced leg exactly ONCE (edge-complete boundary split).  This is the
stable-carrier analogue of body-628's idempotence, proved directly (NOT `rw`-transported: the second index
lives over `stableLocalBoundaryCompletedGraph γ`, a different type). -/
theorem stableLocalBoundaryIterate_idempotent (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ) :
    stableLocalBoundaryCompletedGraph δ
      = stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ) := by
  -- the two graphs' induced-leg functions coincide (both read only `δ.vertices`)
  have hbel : (stableRootRelativeInner γ δ).boundaryExternalLeg = δ.boundaryExternalLeg := rfl
  -- inherited-leg re-absorption of `δ.externalLegs`
  have hδdecomp : δ.externalLegs
      = (stableRootRelativeInner γ δ).externalLegs
        + (stableInheritedOuter γ δ).map γ.boundaryExternalLeg := by
    have hsub : δ.vertices ⊆ γ.vertices := δ.vertices_subset
    rw [externalLegs_eq_filter_of_saturated δ hδsat, stableLocalBoundaryCompletedGraph_externalLegs,
      Multiset.filter_add]
    congr 1
    · show γ.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
          = G.externalLegs.filter (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
      rw [externalLegs_eq_filter_of_saturated γ hγsat, Multiset.filter_filter]
      exact Multiset.filter_congr (fun ℓ _ =>
        ⟨fun h => h.1, fun h => ⟨h, hsub h⟩⟩)
    · rw [← Multiset.map_filter_of_iff γ.boundaryExternalLeg γ.resolvedBoundaryEdges
            (fun e => γ.resolvedInsideEndpoint e ∈ δ.vertices) (fun ℓ => ℓ.attachedTo ∈ δ.vertices)
            (fun _ => Iff.rfl)]
      rfl
  have hsplit : (stableRootRelativeInner γ δ).resolvedBoundaryEdges
      = stableInheritedOuter γ δ + δ.resolvedBoundaryEdges :=
    stableRootRelativeInner_resolvedBoundaryEdges_eq_of_edgeComplete γ δ hEC
  have hagree : (stableInheritedOuter γ δ).map (stableRootRelativeInner γ δ).boundaryExternalLeg
      = (stableInheritedOuter γ δ).map γ.boundaryExternalLeg :=
    Multiset.map_congr rfl (fun e he => stableBoundaryExternalLeg_agree_on_inherited γ δ he)
  unfold stableLocalBoundaryCompletedGraph
  rw [ResolvedFeynmanGraph.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  show δ.externalLegs + δ.resolvedBoundaryEdges.map δ.boundaryExternalLeg
      = (stableRootRelativeInner γ δ).externalLegs
        + (stableRootRelativeInner γ δ).resolvedBoundaryEdges.map
            (stableRootRelativeInner γ δ).boundaryExternalLeg
  rw [hδdecomp, hsplit, Multiset.map_add, hagree, hbel]
  abel

/-! ## Step 3 — the stable local left factor -/

/-- **body-630 (Step 3) — the stable local left factor.**  On `Sum.inl true` the boundary-completed stable
generator; on `Sum.inl false` the unit `1`; on `Sum.inr B` the stable left aggregate of the live inner
forest `B` over `stableLocalBoundaryCompletedGraph γ`.  Lands in `StableResolvedPhi4HopfH`.  NO cast / Equiv
to the OLD `phi4EdgeCompleteLocalLeftFactor`. -/
noncomputable def stableLocalLeftFactor {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    (Bool ⊕ StableLocalForestIdx γ) → StableResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then
        MvPolynomial.X ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt))
      else (1 : StableResolvedPhi4HopfH))
    (fun B => stableLeftAggregate B.1
      (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt))

/-- **body-630 (Step 3) — the LEFT primitive branch value.** -/
theorem stableLocalLeftFactor_inl_true {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    stableLocalLeftFactor hSt γ hCDγ (Sum.inl true)
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)) := rfl

/-- **body-630 (Step 3) — the RIGHT primitive branch value (`1`).** -/
theorem stableLocalLeftFactor_inl_false {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    stableLocalLeftFactor hSt γ hCDγ (Sum.inl false) = (1 : StableResolvedPhi4HopfH) := rfl

/-- **body-630 (Step 3) — the FOREST branch value.**  On `Sum.inr B` the stable left factor is the stable
left aggregate of the live inner forest `B`. -/
theorem stableLocalLeftFactor_inr {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget)
    (B : StableLocalForestIdx γ) :
    stableLocalLeftFactor hSt γ hCDγ (Sum.inr B)
      = stableLeftAggregate B.1
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt) := rfl

/-- **body-630 (Step 3, FOREST match — the key per-occurrence class equality) — the nested stable
completion of `δ` and the root-promoted completion agree as resolved CLASSES.**  A `congrArg` of the RAW
idempotence: the two graphs are RAW-equal, so their resolved classes coincide.  This is exactly the
per-occurrence key that body-625's no-go DENIED on the naive carrier and that the STABLE carrier now
SUPPLIES. -/
theorem stableForestLeftFactor_component_eq_promoted (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (stableLocalBoundaryCompletedGraph δ).toResolvedClass
      = (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).toResolvedClass :=
  congrArg ResolvedFeynmanGraph.toResolvedClass (stableLocalBoundaryIterate_idempotent γ δ hγsat hδsat hEC)

/-- **body-630 (Step 3, FOREST match — GENERATOR form) — the nested and root-promoted stable generators
coincide.**  The class equality lifted to a `StableResolvedPhi4HopfGen` equality through body-629's
`toStableResolvedPhi4HopfGen_class_eq` (the thin exit), hence to equal `MvPolynomial.X` generators.  This is
the algebraic realization of body-625's DENIED per-occurrence factor equality, now PROVED on the stable
carrier. -/
theorem stableForestLeftFactor_gen_eq_promoted (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph (stableLocalBoundaryCompletedGraph γ))
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated (stableLocalBoundaryCompletedGraph γ) δ)
    (hEC : ResolvedInternalEdgeComplete γ)
    (hCDδ : ∃ hWF : (stableLocalBoundaryCompletedGraph δ).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (stableLocalBoundaryCompletedGraph δ).forget
        (phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph δ).forget)
        (FeynmanSubgraph.self (stableLocalBoundaryCompletedGraph δ).forget hWF))
    (hStδ : StableResolvedBoundaryIds (stableLocalBoundaryCompletedGraph δ))
    (hCDR : ∃ hWF : (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent
        (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget
        (phi4DivergenceMeasureFamily
          (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget)
        (FeynmanSubgraph.self
          (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)).forget hWF))
    (hStR : StableResolvedBoundaryIds (stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ))) :
    (MvPolynomial.X ((stableLocalBoundaryCompletedGraph δ).toStableResolvedPhi4HopfGen hCDδ hStδ)
        : StableResolvedPhi4HopfH)
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph (stableRootRelativeInner γ δ)
          ).toStableResolvedPhi4HopfGen hCDR hStR) :=
  congrArg (fun g => (MvPolynomial.X g : StableResolvedPhi4HopfH))
    (toStableResolvedPhi4HopfGen_class_eq hCDδ hCDR hStδ hStR
      (stableForestLeftFactor_component_eq_promoted γ δ hγsat hδsat hEC))

end GaugeGeometry.QFT.Combinatorial
