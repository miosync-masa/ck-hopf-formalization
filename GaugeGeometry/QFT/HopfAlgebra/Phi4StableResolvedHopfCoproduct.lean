import GaugeGeometry.QFT.HopfAlgebra.Phi4StableBoundaryIdempotence

/-!
# QFT-R1-body-629 — the stable resolved Hopf carrier + stable resolved coproduct (parallel space)

Body-625 proved a class-level **no-go**: the naive nested completion re-encodes an inherited outer boundary
leg EVEN locally while the root-direct route keeps it ODD; the `legId` profile is a `mapPerm`-invariant, so no
relabeling reconciles them.  That witness demanded a *new physical representation space* — one whose objects
own a stable boundary-ID certificate, not merely satisfy it as a proved observable.  Body-626/627/628 realized
the stable-completion ownership and its idempotence law as a THEOREM.  This body **elevates** that law to a
TYPE the algebra owns: a PARALLEL stable resolved Hopf carrier and coproduct, living *alongside* the frozen
old carrier `ResolvedPhi4HopfGen` / `coproduct_resolved_edgeComplete_phi4`, with NO equality / Equiv / cast /
coalgebra bridge between the two.

## Steps

* Step 1 — the minimal stable certificate `StableResolvedBoundaryIds` (the ONE new `Prop` structure): unique
  edge/leg ids + the even/odd boundary disjointness `ℓ.legId ≠ boundaryLegId e`.  With its `mapPerm`-invariance
  iff, body-627's `phi4StableRigidifiedGraph` as an INHABITANT, and the two closures — under the
  inherited-verbatim / new-cut-edge-odd local completion (the third field is exactly what makes the VERBATIM
  completion leg-id-unique) and under the canonical forest-contraction right graph (retarget preserves
  edgeId/legId).  The three fields SUFFICE for both closures; no further field is surfaced.
* Step 2 — the parallel carrier: `ResolvedFeynmanGraphClass.HasStableBoundaryIds` (a `Quotient.lift` of the
  raw certificate), then `StableResolvedPhi4HopfGen` (φ⁴ connected-divergent classes that ALSO own the stable
  certificate) and `StableResolvedPhi4HopfH := MvPolynomial StableResolvedPhi4HopfGen ℚ`.  A PARALLEL new
  carrier — NOT a refinement / cast of the old `ResolvedPhi4HopfGen`.
* Step 3 — the stable left/right factors.  LEFT: `stableLocalBoundaryCompletedGraph γ` (inherited legs
  VERBATIM + fresh ODD cut legs, ZERO re-encode) with strict flat `forget` equality, WellFormed, `mapPerm`
  coherence, the stable certificate, φ⁴ CD transport, and the stable left forest aggregate + its rename
  invariance.  RIGHT: the W‴ canonical contraction geometry read off `phi4WTriplePrimeCanonicalSupply`, plus
  only the stable-certificate preservation, packaged into `StableResolvedPhi4HopfGen`.
* Step 4 — the stable resolved coproduct.  Index = the existing `phi4WTriplePrimeIndex` (unchanged),
  multiplicity-preserving: `stableForestSummand` → `stableForestSum` → (`mapPerm`-invariance) →
  (graph-class descent, `Quotient.liftOn`) → `stableCoproductGen` → `MvPolynomial.aeval`, giving
  `coproduct_resolved_stable_phi4 : StableResolvedPhi4HopfH →ₐ StableResolvedPhi4HopfH ⊗ StableResolvedPhi4HopfH`.
  The generator computation rule exposes the primitive 2 terms + the W‴ forest sum explicitly.

## HALT / red lines
OLD `ResolvedPhi4HopfGen` / `ResolvedPhi4HopfH` / `coproduct_resolved_edgeComplete_phi4` are FROZEN — unedited;
NO equality / Equiv / cast / coalgebra bridge between old and new carriers.  body-625's no-go is preserved.
coassoc / summand agreement / quot_eq are NOT entered.  NO orbit / ID-renaming quotient / dedup / `toFinset`;
no naive nested completion; no second `stableRootNormalize`; no inherited-leg re-encode (`encodeExistingLeg` on
inherited legs).  EXACTLY ONE new `structure` (the `Prop` `StableResolvedBoundaryIds`); ZERO new `class` /
`instance`.  ZERO forbidden divergence classes in any declaration TYPE (only the concrete
`phi4DivergenceMeasureFamily` / `phi4PermInvariantDivergenceMeasureFamily` family VALUES).  ZERO `sorry` /
`admit` / `native_decide`; NO public `HEq` / `cast` / graph-data `▸`.  Axiom-clean (`propext`,
`Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family, made available so the resolved
admissible-subgraph / contraction / carrier plumbing (all instance-parametrized by `[∀ H, DivergenceMeasure H]`)
elaborates against the φ⁴ family — mirroring the OLD carrier's `[∀ G, DivergenceMeasure G]` binder. -/
local instance instPhi4DivergenceMeasureFamily : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the minimal stable certificate (the ONE new Prop structure) -/

/-- **body-629 (Step 1) — the stable resolved boundary-ID certificate.**  A resolved graph OWNS this iff its
internal edges have unique ids, its external legs have unique ids, AND no external leg's `legId` collides with
the ODD boundary namespace `boundaryLegId e = 2·e.edgeId+1` of any internal edge.  The third field is the load
-bearing one: it is exactly what keeps the inherited-VERBATIM local completion leg-id-unique (the even/odd
namespace of body-589 without the EVEN re-encode). -/
structure StableResolvedBoundaryIds (G : ResolvedFeynmanGraph) : Prop where
  /-- The internal edges have pairwise-distinct `edgeId`s. -/
  edgeIdsUnique : G.EdgeIdsUnique
  /-- The external legs have pairwise-distinct `legId`s. -/
  legIdsUnique : G.LegIdsUnique
  /-- No external leg's `legId` lies in the ODD boundary namespace of any internal edge. -/
  external_boundary_disjoint :
    ∀ ℓ ∈ G.externalLegs, ∀ e ∈ G.internalEdges, ℓ.legId ≠ boundaryLegId e

/-- **body-629 (Step 1) — the stable certificate is `mapPerm`-invariant.**  Relabeling by `σ` preserves every
`edgeId` / `legId` and sends `boundaryLegId (map σ e) = boundaryLegId e`, so all three fields transport both
ways. -/
theorem stableResolvedBoundaryIds_mapPerm_iff (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    StableResolvedBoundaryIds (G.mapPerm σ) ↔ StableResolvedBoundaryIds G := by
  have hIE : (G.mapPerm σ).internalEdges = G.internalEdges.map (ResolvedFeynmanEdge.map σ) := rfl
  have hLE : (G.mapPerm σ).externalLegs = G.externalLegs.map (ResolvedExternalLeg.map σ) := rfl
  have hbid : ∀ e : ResolvedFeynmanEdge, boundaryLegId (ResolvedFeynmanEdge.map σ e) = boundaryLegId e :=
    fun _ => rfl
  have hlid : ∀ ℓ : ResolvedExternalLeg, (ResolvedExternalLeg.map σ ℓ).legId = ℓ.legId := fun _ => rfl
  constructor
  · intro h
    refine ⟨(edgeIdsUnique_mapPerm_iff G σ).mp h.edgeIdsUnique,
      (legIdsUnique_mapPerm_iff G σ).mp h.legIdsUnique, ?_⟩
    intro ℓ hℓ e he
    have hℓσ : ResolvedExternalLeg.map σ ℓ ∈ (G.mapPerm σ).externalLegs := by
      rw [hLE]; exact Multiset.mem_map_of_mem _ hℓ
    have heσ : ResolvedFeynmanEdge.map σ e ∈ (G.mapPerm σ).internalEdges := by
      rw [hIE]; exact Multiset.mem_map_of_mem _ he
    have := h.external_boundary_disjoint _ hℓσ _ heσ
    rwa [hlid, hbid] at this
  · intro h
    refine ⟨(edgeIdsUnique_mapPerm_iff G σ).mpr h.edgeIdsUnique,
      (legIdsUnique_mapPerm_iff G σ).mpr h.legIdsUnique, ?_⟩
    intro ℓ hℓ e he
    rw [hLE] at hℓ; rw [hIE] at he
    obtain ⟨ℓ₀, hℓ₀, rfl⟩ := Multiset.mem_map.mp hℓ
    obtain ⟨e₀, he₀, rfl⟩ := Multiset.mem_map.mp he
    rw [hlid, hbid]
    exact h.external_boundary_disjoint _ hℓ₀ _ he₀

/-- **body-629 (Step 1, INHABITANT) — body-627's chosen φ⁴ normalized rigidification OWNS the stable
certificate.**  Edge/leg id uniqueness are body-627's; the boundary disjointness is pure parity — the
normalizer's legs are EVEN (`existingLegId`) and the boundary namespace is ODD. -/
theorem phi4StableRigidifiedGraph_stableResolvedBoundaryIds (x : Phi4HopfGen) :
    StableResolvedBoundaryIds (phi4StableRigidifiedGraph x) := by
  refine ⟨phi4StableRigidifiedGraph_edgeIdsUnique x, phi4StableRigidifiedGraph_legIdsUnique x, ?_⟩
  intro ℓ hℓ e he
  -- the normalized root's legs are exactly the EVEN re-encodings of the rigidification's legs
  rw [show phi4StableRigidifiedGraph x
        = stableRootNormalize (phi4RigidifiedGraph x) (phi4RigidifiedGraph_forget_wellFormed x) from rfl,
    stableRootNormalize_externalLegs] at hℓ
  obtain ⟨ℓ₀, _, rfl⟩ := Multiset.mem_map.mp hℓ
  rw [encodeExistingLeg_legId]
  exact existingLegId_ne_boundaryLegId ℓ₀ e

/-! ## Step 2 — the parallel carrier -/

/-- **body-629 (Step 2) — the stable boundary-ID certificate on an id-preserving class.**  The raw certificate
descends through `ResolvedFeynmanGraphClass` because it is `mapPerm`-invariant (Step 1). -/
def ResolvedFeynmanGraphClass.HasStableBoundaryIds : ResolvedFeynmanGraphClass → Prop :=
  Quotient.lift StableResolvedBoundaryIds (by
    intro a b h
    obtain ⟨σ, rfl⟩ := h
    exact propext (stableResolvedBoundaryIds_mapPerm_iff a σ).symm)

@[simp] theorem ResolvedFeynmanGraphClass.hasStableBoundaryIds_mk (G : ResolvedFeynmanGraph) :
    ResolvedFeynmanGraphClass.HasStableBoundaryIds G.toResolvedClass ↔ StableResolvedBoundaryIds G :=
  Iff.rfl

/-- **body-629 (Step 2) — the stable resolved φ⁴ Hopf generators.**  φ⁴ family connected-divergent
id-preserving classes that ALSO own the stable boundary-ID certificate.  A PARALLEL new carrier — NOT a
refinement / cast of the old `ResolvedPhi4HopfGen`. -/
def StableResolvedPhi4HopfGen : Type :=
  { c : ResolvedFeynmanGraphClass //
    c.IsConnectedDivergentFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
      ∧ c.HasStableBoundaryIds }

/-- **body-629 (Step 2) — the stable resolved φ⁴ Hopf polynomial algebra.** -/
noncomputable abbrev StableResolvedPhi4HopfH : Type := MvPolynomial StableResolvedPhi4HopfGen ℚ

/-- **body-629 (Step 2) — a stable resolved φ⁴ generator from a resolved graph** owning both the family CD and
the stable certificate. -/
noncomputable def ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) : StableResolvedPhi4HopfGen :=
  ⟨G.toResolvedClass,
    (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass
      phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily G).mpr hCD, hSt⟩

@[simp] theorem ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    (G.toStableResolvedPhi4HopfGen hCD hSt).val = G.toResolvedClass := rfl

/-- **body-629 (Step 2) — the stable generator depends only on the class + the two certificates.**  Equal
classes give equal stable generators (both properties enter proof-irrelevantly). -/
theorem toStableResolvedPhi4HopfGen_class_eq {G₁ G₂ : ResolvedFeynmanGraph}
    (hCD₁ : ∃ hWF : G₁.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G₁.forget (phi4DivergenceMeasureFamily G₁.forget)
        (FeynmanSubgraph.self G₁.forget hWF))
    (hCD₂ : ∃ hWF : G₂.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G₂.forget (phi4DivergenceMeasureFamily G₂.forget)
        (FeynmanSubgraph.self G₂.forget hWF))
    (hSt₁ : StableResolvedBoundaryIds G₁) (hSt₂ : StableResolvedBoundaryIds G₂)
    (h : G₁.toResolvedClass = G₂.toResolvedClass) :
    G₁.toStableResolvedPhi4HopfGen hCD₁ hSt₁ = G₂.toStableResolvedPhi4HopfGen hCD₂ hSt₂ := by
  apply Subtype.ext
  rw [ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val,
    ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val]
  exact h

/-! ## Step 3 — the LEFT factor: the inherited-verbatim local boundary completion -/

/-- **body-629 (Step 3, LEFT) — the stable local boundary-completed graph.**  Same vertices / internal edges as
`γ`; external legs are the inherited legs kept VERBATIM plus the fresh ODD induced boundary legs.  `encode
ExistingLeg` is NOT applied to the inherited legs — the ZERO-re-encode completion. -/
noncomputable def stableLocalBoundaryCompletedGraph (γ : ResolvedFeynmanSubgraph G) :
    ResolvedFeynmanGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg

@[simp] theorem stableLocalBoundaryCompletedGraph_vertices (γ : ResolvedFeynmanSubgraph G) :
    (stableLocalBoundaryCompletedGraph γ).vertices = γ.vertices := rfl

@[simp] theorem stableLocalBoundaryCompletedGraph_internalEdges (γ : ResolvedFeynmanSubgraph G) :
    (stableLocalBoundaryCompletedGraph γ).internalEdges = γ.internalEdges := rfl

/-- **body-629 (Step 3, LEFT, CRUX) — the completed external legs, DEFINITIONAL form.**  Inherited legs
`γ.externalLegs` kept VERBATIM; only the freshly-cut boundary edges receive an ODD induced leg. -/
@[simp] theorem stableLocalBoundaryCompletedGraph_externalLegs (γ : ResolvedFeynmanSubgraph G) :
    (stableLocalBoundaryCompletedGraph γ).externalLegs
      = γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg := rfl

/-- **body-629 (Step 3, LEFT, LOAD-BEARING) — strict flat `forget` equality.**  The VERBATIM inherited legs and
the EVEN-re-encoded ones both forget to the same flat legs (`forget` drops the id), so the completed graph
forgets RAW-equal to body-567's flat completed graph. -/
theorem stableLocalBoundaryCompletedGraph_forget (γ : ResolvedFeynmanSubgraph G) :
    (stableLocalBoundaryCompletedGraph γ).forget = γ.forget.boundaryCompletedGraph := by
  simp only [ResolvedFeynmanGraph.forget, FeynmanSubgraph.boundaryCompletedGraph,
    stableLocalBoundaryCompletedGraph, FeynmanGraph.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  show (γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg).map ResolvedExternalLeg.forget
      = γ.forget.boundaryCompletedExternalLegs
  have h2 : (γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg).map ResolvedExternalLeg.forget
      = γ.forget.inducedBoundaryExternalLegs := by
    rw [FeynmanSubgraph.inducedBoundaryExternalLegs, Multiset.map_map, ← γ.resolvedBoundaryEdges_forget,
      Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => rfl)
  rw [Multiset.map_add, h2, FeynmanSubgraph.boundaryCompletedExternalLegs,
    ← ResolvedFeynmanSubgraph.forget_externalLegs]

/-- **body-629 (Step 3, LEFT) — the completed graph forgets to a WELL-FORMED flat graph.** -/
theorem stableLocalBoundaryCompletedGraph_forget_wellFormed (γ : ResolvedFeynmanSubgraph G) :
    (stableLocalBoundaryCompletedGraph γ).forget.WellFormed := by
  rw [stableLocalBoundaryCompletedGraph_forget]
  exact γ.forget.boundaryCompletedGraph_wellFormed

/-- **body-629 (Step 3, LEFT, CD transport) — the completed forgotten graph is connected-divergent** (`∃`-form)
from the component's `forget`-CD, via the strict `forget` equality + body-568's flat completion CD. -/
theorem stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent (γ : ResolvedFeynmanSubgraph G)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    ∃ hWF : (stableLocalBoundaryCompletedGraph γ).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (stableLocalBoundaryCompletedGraph γ).forget
        (phi4DivergenceMeasureFamily (stableLocalBoundaryCompletedGraph γ).forget)
        (FeynmanSubgraph.self (stableLocalBoundaryCompletedGraph γ).forget hWF) := by
  rw [stableLocalBoundaryCompletedGraph_forget]
  exact γ.forget.boundaryCompletedGraph_exists_self_isConnectedDivergent hγCD

/-- **body-629 (Step 3, LEFT, CLOSURE) — the stable certificate is preserved by the local completion.**  Under
the AMBIENT certificate `StableResolvedBoundaryIds G`: edge ids inherit (edges unchanged); leg ids are unique
because inherited legs are ambient-unique, the ODD induced legs are edge-id-unique, and the cross case is
exactly the ambient boundary disjointness (third field, the reason the VERBATIM completion is safe); and the
completed graph's own boundary disjointness holds because a boundary edge (one endpoint outside) is never an
internal edge (both endpoints inside). -/
theorem stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph
    (γ : ResolvedFeynmanSubgraph G) (hSt : StableResolvedBoundaryIds G) :
    StableResolvedBoundaryIds (stableLocalBoundaryCompletedGraph γ) := by
  refine ⟨?_, ?_, ?_⟩
  · -- edgeIdsUnique
    intro e₁ h₁ e₂ h₂ hid
    rw [stableLocalBoundaryCompletedGraph_internalEdges] at h₁ h₂
    exact hSt.edgeIdsUnique e₁ (Multiset.mem_of_le γ.internalEdges_le h₁)
      e₂ (Multiset.mem_of_le γ.internalEdges_le h₂) hid
  · -- legIdsUnique
    intro ℓ₁ h₁ ℓ₂ h₂ hid
    rw [stableLocalBoundaryCompletedGraph_externalLegs] at h₁ h₂
    rcases Multiset.mem_add.mp h₁ with hA₁ | hB₁ <;> rcases Multiset.mem_add.mp h₂ with hA₂ | hB₂
    · exact hSt.legIdsUnique ℓ₁ (Multiset.mem_of_le γ.externalLegs_le hA₁)
        ℓ₂ (Multiset.mem_of_le γ.externalLegs_le hA₂) hid
    · rcases Multiset.mem_map.mp hB₂ with ⟨e₂, he₂, rfl⟩
      rw [boundaryExternalLeg_legId] at hid
      exact absurd hid (hSt.external_boundary_disjoint ℓ₁ (Multiset.mem_of_le γ.externalLegs_le hA₁)
        e₂ (resolvedBoundaryEdges_mem.mp he₂).1)
    · rcases Multiset.mem_map.mp hB₁ with ⟨e₁, he₁, rfl⟩
      rw [boundaryExternalLeg_legId] at hid
      exact absurd hid.symm (hSt.external_boundary_disjoint ℓ₂ (Multiset.mem_of_le γ.externalLegs_le hA₂)
        e₁ (resolvedBoundaryEdges_mem.mp he₁).1)
    · rcases Multiset.mem_map.mp hB₁ with ⟨e₁, he₁, rfl⟩
      rcases Multiset.mem_map.mp hB₂ with ⟨e₂, he₂, rfl⟩
      rw [boundaryExternalLeg_legId, boundaryExternalLeg_legId] at hid
      rw [boundaryLegId_injOn_of_edgeIdUnique hSt.edgeIdsUnique
        (resolvedBoundaryEdges_mem.mp he₁).1 (resolvedBoundaryEdges_mem.mp he₂).1 hid]
  · -- external_boundary_disjoint
    intro ℓ hℓ e he hcontra
    rw [stableLocalBoundaryCompletedGraph_externalLegs] at hℓ
    rw [stableLocalBoundaryCompletedGraph_internalEdges] at he
    rcases Multiset.mem_add.mp hℓ with hA | hB
    · exact hSt.external_boundary_disjoint ℓ (Multiset.mem_of_le γ.externalLegs_le hA)
        e (Multiset.mem_of_le γ.internalEdges_le he) hcontra
    · rcases Multiset.mem_map.mp hB with ⟨e', he', rfl⟩
      rw [boundaryExternalLeg_legId] at hcontra
      have heq : e' = e := boundaryLegId_injOn_of_edgeIdUnique hSt.edgeIdsUnique
        (resolvedBoundaryEdges_mem.mp he').1 (Multiset.mem_of_le γ.internalEdges_le he) hcontra
      have hbd : γ.resolvedIsBoundaryEdge e' := (resolvedBoundaryEdges_mem.mp he').2
      obtain ⟨hs, ht⟩ := γ.edges_supported e he
      rw [heq] at hbd
      rcases hbd with ⟨_, hout⟩ | ⟨hout, _⟩
      · exact hout ht
      · exact hout hs

/-- **body-629 (Step 3, LEFT) — the local completion commutes with `mapPerm σ`.**  Inherited legs transport as
`γ.externalLegs.map (map σ)`; boundary edges / induced legs transport by the map/filter commute (body-589's
engine, verbatim EVEN part). -/
theorem stableLocalBoundaryCompletedGraph_mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    stableLocalBoundaryCompletedGraph (γ.mapPerm σ)
      = (stableLocalBoundaryCompletedGraph γ).mapPerm σ := by
  have hpred : ∀ e : ResolvedFeynmanEdge,
      γ.resolvedIsBoundaryEdge e ↔ (γ.mapPerm σ).resolvedIsBoundaryEdge (ResolvedFeynmanEdge.map σ e) := by
    intro e
    unfold resolvedIsBoundaryEdge
    show _ ↔ ((ResolvedFeynmanEdge.map σ e).source ∈ (γ.mapPerm σ).vertices ∧
              (ResolvedFeynmanEdge.map σ e).target ∉ (γ.mapPerm σ).vertices) ∨
             ((ResolvedFeynmanEdge.map σ e).source ∉ (γ.mapPerm σ).vertices ∧
              (ResolvedFeynmanEdge.map σ e).target ∈ (γ.mapPerm σ).vertices)
    simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanSubgraph.mapPerm_vertices,
      σ.injective.mem_finset_image]
  have hBE : (γ.mapPerm σ).resolvedBoundaryEdges
      = γ.resolvedBoundaryEdges.map (ResolvedFeynmanEdge.map σ) := by
    unfold resolvedBoundaryEdges
    symm
    exact Multiset.map_filter_of_iff (ResolvedFeynmanEdge.map σ) G.internalEdges
      γ.resolvedIsBoundaryEdge (γ.mapPerm σ).resolvedIsBoundaryEdge hpred
  have hleg : ∀ e : ResolvedFeynmanEdge,
      ResolvedExternalLeg.map σ (γ.boundaryExternalLeg e)
        = (γ.mapPerm σ).boundaryExternalLeg (ResolvedFeynmanEdge.map σ e) := by
    intro e
    unfold boundaryExternalLeg ResolvedExternalLeg.map resolvedInsideEndpoint
    simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanSubgraph.mapPerm_vertices,
      σ.injective.mem_finset_image]
    by_cases hs : e.source ∈ γ.vertices <;> simp [hs, boundaryLegId]
  have hb : (γ.mapPerm σ).resolvedBoundaryEdges.map (γ.mapPerm σ).boundaryExternalLeg
      = (γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg).map (ResolvedExternalLeg.map σ) := by
    rw [hBE, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => (hleg e).symm)
  have hcomp : (γ.mapPerm σ).externalLegs
        + (γ.mapPerm σ).resolvedBoundaryEdges.map (γ.mapPerm σ).boundaryExternalLeg
      = (γ.externalLegs + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg).map (ResolvedExternalLeg.map σ) := by
    rw [Multiset.map_add, ResolvedFeynmanSubgraph.mapPerm_externalLegs, hb]
  show stableLocalBoundaryCompletedGraph (γ.mapPerm σ) = (stableLocalBoundaryCompletedGraph γ).mapPerm σ
  exact congr (congr (congrArg ResolvedFeynmanGraph.mk rfl) rfl) hcomp

/-! ### Step 3 — the stable left forest aggregate -/

/-- **body-629 (Step 3, LEFT) — the stable resolved forest left aggregate.**  The product of the per-component
stable left generators (inherited-verbatim completions) over the forest's `.attach`; each component carries its
membership certificate.  Lands in `StableResolvedPhi4HopfH`. -/
noncomputable def stableLeftAggregate {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) (hSt : StableResolvedBoundaryIds G) :
    StableResolvedPhi4HopfH := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact ∏ γ ∈ A.elements.attach, (MvPolynomial.X
    ((stableLocalBoundaryCompletedGraph γ.1).toStableResolvedPhi4HopfGen
      (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ.1
        (A.isConnectedDivergent γ.1 γ.2))
      (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ.1 hSt)) : StableResolvedPhi4HopfH)

/-- **body-629 (Step 3, LEFT) — one stable left-component generator is rename-invariant.** -/
theorem stableComponentGen_mapPermFor
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (γ : ResolvedFeynmanSubgraph G₁)
    (hCD : @FeynmanSubgraph.IsConnectedDivergent G₁.forget (phi4DivergenceMeasureFamily G₁.forget) γ.forget)
    (hCDσ : @FeynmanSubgraph.IsConnectedDivergent G₂.forget (phi4DivergenceMeasureFamily G₂.forget)
      (mapPermRFS hσ γ).forget)
    (hSt₁ : StableResolvedBoundaryIds G₁) (hSt₂ : StableResolvedBoundaryIds G₂) :
    (stableLocalBoundaryCompletedGraph (mapPermRFS hσ γ)).toStableResolvedPhi4HopfGen
        (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent (mapPermRFS hσ γ) hCDσ)
        (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph (mapPermRFS hσ γ) hSt₂)
      = (stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCD)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt₁) := by
  apply toStableResolvedPhi4HopfGen_class_eq
  subst hσ
  show (stableLocalBoundaryCompletedGraph (γ.mapPerm σ)).toResolvedClass
    = (stableLocalBoundaryCompletedGraph γ).toResolvedClass
  rw [stableLocalBoundaryCompletedGraph_mapPerm]
  exact ResolvedFeynmanGraph.toResolvedClass_mapPerm _ _

/-- **body-629 (Step 3, LEFT, TARGET) — the stable forest left aggregate is rename-invariant.**  Componentwise
`stableComponentGen_mapPermFor` through a `Finset.prod_bij` on the two `.attach` products.  No W‴ membership
hypothesis. -/
theorem stableLeftAggregate_mapPermFor
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₁)
    (hSt₁ : StableResolvedBoundaryIds G₁) (hSt₂ : StableResolvedBoundaryIds G₂) :
    stableLeftAggregate
        (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily hσ A) hSt₂
      = stableLeftAggregate A hSt₁ := by
  classical
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  set B := mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily hσ A with hB
  have hmem : ∀ (γ : ResolvedFeynmanSubgraph G₁), γ ∈ A.elements → mapPermRFS hσ γ ∈ B.elements := by
    intro γ hγ
    rw [hB, mapPermResolvedAdmissibleSubgraphFor_elements]
    exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
  symm
  simp only [stableLeftAggregate]
  refine Finset.prod_bij
    (fun (γ : {x // x ∈ A.elements}) _ => (⟨mapPermRFS hσ γ.1, hmem γ.1 γ.2⟩ :
      {x // x ∈ B.elements}))
    (fun _ _ => Finset.mem_attach _ _)
    ?_ ?_ ?_
  · intro γ₁ _ γ₂ _ heq
    have h1 : mapPermRFS hσ γ₁.1 = mapPermRFS hσ γ₂.1 := congrArg Subtype.val heq
    exact Subtype.ext (mapPermRFS_injective hσ h1)
  · intro b _
    obtain ⟨bv, hbv⟩ := b
    rw [hB, mapPermResolvedAdmissibleSubgraphFor_elements] at hbv
    rcases Finset.mem_image.mp hbv with ⟨γ, hγ, hγeq⟩
    exact ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, Subtype.ext hγeq⟩
  · intro γ _
    exact congrArg (fun g => (MvPolynomial.X g : StableResolvedPhi4HopfH))
      (stableComponentGen_mapPermFor hσ γ.1 (A.isConnectedDivergent γ.1 γ.2)
        (B.isConnectedDivergent (mapPermRFS hσ γ.1) (hmem γ.1 γ.2)) hSt₁ hSt₂).symm

/-! ### Step 3 — the RIGHT factor: the contraction stable generator -/

/-- **body-629 (Step 3, RIGHT, CLOSURE) — the stable certificate is preserved by the forest contraction.**  The
resolved star-contraction retargets endpoints only; every `edgeId` / `legId` is kept, and the complement edges
lie among `G`'s internal edges — so all three fields transport from the ambient `StableResolvedBoundaryIds G`. -/
theorem stableResolvedBoundaryIds_contractWithStars {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (hSt : StableResolvedBoundaryIds G) :
    StableResolvedBoundaryIds (A.contractWithStars starOf) := by
  have hcompl : ∀ e ∈ A.complementEdges, e ∈ G.internalEdges :=
    fun e he => Multiset.mem_of_le (Multiset.sub_le_self _ _) he
  refine ⟨?_, ?_, ?_⟩
  · -- edgeIdsUnique
    intro e₁ h₁ e₂ h₂ hid
    rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at h₁ h₂
    obtain ⟨d₁, hd₁, rfl⟩ := Multiset.mem_map.mp h₁
    obtain ⟨d₂, hd₂, rfl⟩ := Multiset.mem_map.mp h₂
    have : d₁ = d₂ := hSt.edgeIdsUnique d₁ (hcompl d₁ hd₁) d₂ (hcompl d₂ hd₂) (by
      simpa [ResolvedAdmissibleSubgraph.retargetEdge] using hid)
    rw [this]
  · -- legIdsUnique
    intro ℓ₁ h₁ ℓ₂ h₂ hid
    rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at h₁ h₂
    obtain ⟨m₁, hm₁, rfl⟩ := Multiset.mem_map.mp h₁
    obtain ⟨m₂, hm₂, rfl⟩ := Multiset.mem_map.mp h₂
    have : m₁ = m₂ := hSt.legIdsUnique m₁ hm₁ m₂ hm₂ (by
      simpa [ResolvedAdmissibleSubgraph.retargetExternalLeg] using hid)
    rw [this]
  · -- external_boundary_disjoint
    intro ℓ hℓ e he hcontra
    rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs] at hℓ
    rw [ResolvedAdmissibleSubgraph.contractWithStars_internalEdges] at he
    obtain ⟨m, hm, rfl⟩ := Multiset.mem_map.mp hℓ
    obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp he
    apply hSt.external_boundary_disjoint m hm d (hcompl d hd)
    simpa [ResolvedAdmissibleSubgraph.retargetExternalLeg, ResolvedAdmissibleSubgraph.retargetEdge,
      boundaryLegId] using hcontra

/-- **body-629 (Step 3, RIGHT) — the stable resolved forest right term.**  The single stable generator of the
star-contraction `A.contractWithStars starOf`, packaged into `StableResolvedPhi4HopfGen` (family CD from the W‴
supply, stable certificate from the contraction closure). -/
noncomputable def stableForestRightTerm {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hCD : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A.contractWithStars starOf).toResolvedClass)
    (hSt : StableResolvedBoundaryIds (A.contractWithStars starOf)) : StableResolvedPhi4HopfH :=
  MvPolynomial.X ((A.contractWithStars starOf).toStableResolvedPhi4HopfGen
    ((ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A.contractWithStars starOf)).mp hCD) hSt)

/-- **body-629 (Step 3, RIGHT) — the stable right term depends only on the contracted class.** -/
theorem stableForestRightTerm_class_eq {G₁ G₂ : ResolvedFeynmanGraph}
    (A₁ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₁)
    (A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₂)
    (s₁ : ResolvedFeynmanSubgraph G₁ → VertexId) (s₂ : ResolvedFeynmanSubgraph G₂ → VertexId)
    (hCD₁ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A₁.contractWithStars s₁).toResolvedClass)
    (hCD₂ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A₂.contractWithStars s₂).toResolvedClass)
    (hSt₁ : StableResolvedBoundaryIds (A₁.contractWithStars s₁))
    (hSt₂ : StableResolvedBoundaryIds (A₂.contractWithStars s₂))
    (hcls : (A₁.contractWithStars s₁).toResolvedClass = (A₂.contractWithStars s₂).toResolvedClass) :
    stableForestRightTerm A₁ s₁ hCD₁ hSt₁ = stableForestRightTerm A₂ s₂ hCD₂ hSt₂ := by
  unfold stableForestRightTerm
  exact congrArg MvPolynomial.X (toStableResolvedPhi4HopfGen_class_eq _ _ _ _ hcls)

/-- **body-629 (Step 3, RIGHT) — the contracted class equality underlying the OLD W″ right-term rename
invariance.**  Extracted by `MvPolynomial.X` injectivity from `resolvedForestRightTermFor` equality; reuses
the frozen supply's proven geometry without re-deriving the correcting permutation. -/
theorem contractClass_eq_of_rightTermFor_eq {G₁ G₂ : ResolvedFeynmanGraph}
    (A₁ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₁)
    (A₂ : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₂)
    (s₁ : ResolvedFeynmanSubgraph G₁ → VertexId) (s₂ : ResolvedFeynmanSubgraph G₂ → VertexId)
    (hCD₁ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A₁.contractWithStars s₁).toResolvedClass)
    (hCD₂ : ResolvedFeynmanGraphClass.IsConnectedDivergentFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (A₂.contractWithStars s₂).toResolvedClass)
    (h : resolvedForestRightTermFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
          A₁ s₁ hCD₁
        = resolvedForestRightTermFor phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
          A₂ s₂ hCD₂) :
    (A₁.contractWithStars s₁).toResolvedClass = (A₂.contractWithStars s₂).toResolvedClass := by
  unfold resolvedForestRightTermFor at h
  have hg := MvPolynomial.X_injective h
  have hval := congrArg Subtype.val hg
  rwa [ResolvedFeynmanGraph.toResolvedHopfGenFor_val, ResolvedFeynmanGraph.toResolvedHopfGenFor_val] at hval

/-! ## Step 4 — the stable resolved coproduct -/

/-- **body-629 (Step 4) — one stable forest summand for a live W‴ carrier member `A`.**  The stable left
aggregate ⊗ the stable right (contraction) term.  Multiplicity-preserving. -/
noncomputable def stableForestSummand {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier}) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  stableLeftAggregate A.1 hSt ⊗ₜ[ℚ]
    stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
      (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
      (stableResolvedBoundaryIds_contractWithStars A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)

/-- **body-629 (Step 4) — the stable W‴ forest sum for a graph owning the stable certificate.**  The sum of
`stableForestSummand` over the fifth-axis (edge-complete) W‴ carrier `phi4WTriplePrimeIndex G`. -/
noncomputable def stableForestSum (G : ResolvedFeynmanGraph) (hSt : StableResolvedBoundaryIds G) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  ∑ A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier.attach, stableForestSummand hSt A

/-- **body-629 (Step 4, load-bearing) — the stable W‴ forest sum is rename-invariant.**  A faithful stable-
carrier re-key of the frozen `summandSupply_sum_mapPerm`: the carrier bijection is the resolved forest
relabeling (`carrier_mapPerm`), the left factors match by `stableLeftAggregate_mapPermFor`, and the right
factors match by extracting the contracted-class equality from the frozen supply's `rightTerm_mapPerm`. -/
theorem stableForestSum_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (hSt : StableResolvedBoundaryIds G) (hStσ : StableResolvedBoundaryIds (G.mapPerm σ)) :
    stableForestSum (G.mapPerm σ) hStσ = stableForestSum G hSt := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  symm
  have hmem : ∀ A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index G).carrier},
      mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1
        ∈ (phi4WTriplePrimeCanonicalSupply.index (G.mapPerm σ)).carrier := by
    intro A
    rw [phi4WTriplePrimeCanonicalSupply.carrier_mapPerm G σ]
    exact Finset.mem_image.mpr ⟨A.1, A.2, rfl⟩
  refine Finset.sum_bij
    (fun A _ => (⟨mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1, hmem A⟩ :
      {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily (G.mapPerm σ)
        // A ∈ (phi4WTriplePrimeCanonicalSupply.index (G.mapPerm σ)).carrier}))
    (fun _ _ => Finset.mem_attach _ _) ?_ ?_ ?_
  · -- injective
    intro a₁ _ a₂ _ heq
    have h1 : mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) a₁.1
        = mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) a₂.1 :=
      congrArg Subtype.val heq
    exact Subtype.ext (mapPermResolvedAdmissibleSubgraphFor_injective phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) h1)
  · -- surjective
    intro b _
    obtain ⟨bv, hbv⟩ := b
    rw [phi4WTriplePrimeCanonicalSupply.carrier_mapPerm G σ] at hbv
    obtain ⟨A, hA, hAeq⟩ := Finset.mem_image.mp hbv
    exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, Subtype.ext hAeq⟩
  · -- summand equality
    intro A _
    have hleft : stableLeftAggregate A.1 hSt
        = stableLeftAggregate (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1) hStσ :=
      (stableLeftAggregate_mapPermFor (rfl : G.mapPerm σ = G.mapPerm σ) A.1 hSt hStσ).symm
    have hclsOld := phi4WTriplePrimeCanonicalSupply.rightTerm_mapPerm G σ A.1 A.2 (hmem A)
    have hcls := contractClass_eq_of_rightTermFor_eq A.1
      (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1)
      (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
      (phi4WTriplePrimeCanonicalSupply.starOf (G.mapPerm σ)
        (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1))
      (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
      (phi4WTriplePrimeCanonicalSupply.hCD (G.mapPerm σ) _ (hmem A)) hclsOld
    have hright : stableForestRightTerm A.1 (phi4WTriplePrimeCanonicalSupply.starOf G A.1)
          (phi4WTriplePrimeCanonicalSupply.hCD G A.1 A.2)
          (stableResolvedBoundaryIds_contractWithStars A.1
            (phi4WTriplePrimeCanonicalSupply.starOf G A.1) hSt)
        = stableForestRightTerm (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
            phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1)
            (phi4WTriplePrimeCanonicalSupply.starOf (G.mapPerm σ) _)
            (phi4WTriplePrimeCanonicalSupply.hCD (G.mapPerm σ) _ (hmem A))
            (stableResolvedBoundaryIds_contractWithStars _
              (phi4WTriplePrimeCanonicalSupply.starOf (G.mapPerm σ) _) hStσ) :=
      stableForestRightTerm_class_eq _ _ _ _ _ _ _ _ hcls
    show stableForestSummand hSt A
      = stableForestSummand hStσ ⟨mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1, hmem A⟩
    unfold stableForestSummand
    rw [hleft, hright]

/-- **body-629 (Step 4) — the totalized stable forest sum.**  `0` off the certificate, the real forest sum on
it — the `dite` making the descent through `ResolvedFeynmanGraphClass` total. -/
noncomputable def stableForestSumTotal (G : ResolvedFeynmanGraph) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  if h : StableResolvedBoundaryIds G then stableForestSum G h else 0

/-- **body-629 (Step 4) — the totalized forest sum is `mapPerm`-invariant** (the certificate predicate is
`mapPerm`-invariant, and on it the forest sum is invariant by `stableForestSum_mapPerm`). -/
theorem stableForestSumTotal_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    stableForestSumTotal (G.mapPerm σ) = stableForestSumTotal G := by
  unfold stableForestSumTotal
  by_cases h : StableResolvedBoundaryIds G
  · rw [dif_pos h, dif_pos ((stableResolvedBoundaryIds_mapPerm_iff G σ).mpr h)]
    exact stableForestSum_mapPerm G σ h ((stableResolvedBoundaryIds_mapPerm_iff G σ).mpr h)
  · rw [dif_neg h, dif_neg (fun hc => h ((stableResolvedBoundaryIds_mapPerm_iff G σ).mp hc))]

/-- **body-629 (Step 4) — the stable forest sum descended through the resolved graph class** (well defined by
`stableForestSumTotal_mapPerm`). -/
noncomputable def stableForestSumClass (c : ResolvedFeynmanGraphClass) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  Quotient.liftOn c stableForestSumTotal (by
    intro a b h
    obtain ⟨σ, rfl⟩ := h
    exact (stableForestSumTotal_mapPerm a σ).symm)

@[simp] theorem stableForestSumClass_mk (G : ResolvedFeynmanGraph) :
    stableForestSumClass G.toResolvedClass = stableForestSumTotal G := rfl

/-- **body-629 (Step 4) — the stable resolved coproduct on a stable generator.**  The primitive part
(`X x ⊗ 1 + 1 ⊗ X x`, on `x` directly) plus the descended stable W‴ forest sum. -/
noncomputable def stableCoproductGen (x : StableResolvedPhi4HopfGen) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  (MvPolynomial.X x ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH)
      + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X x)
    + stableForestSumClass x.1

/-- **body-629 (Step 4, HEADLINE) — the stable resolved φ⁴ coproduct** `Δᵣˢ :
StableResolvedPhi4HopfH →ₐ StableResolvedPhi4HopfH ⊗ StableResolvedPhi4HopfH`, the `MvPolynomial.aeval`
extension of `stableCoproductGen`.  A PARALLEL coproduct on the stable carrier — NO equality / restriction /
cast / coalgebra bridge to the frozen old `coproduct_resolved_edgeComplete_phi4`. -/
noncomputable def coproduct_resolved_stable_phi4 :
    StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  MvPolynomial.aeval stableCoproductGen

@[simp] theorem coproduct_resolved_stable_phi4_X (x : StableResolvedPhi4HopfGen) :
    coproduct_resolved_stable_phi4 (MvPolynomial.X x) = stableCoproductGen x := by
  simp [coproduct_resolved_stable_phi4]

/-- **body-629 (Step 4) — `Δᵣˢ` preserves the unit. -/
theorem coproduct_resolved_stable_phi4_one : coproduct_resolved_stable_phi4 1 = 1 := map_one _

/-- **body-629 (Step 4) — `Δᵣˢ` is multiplicative. -/
theorem coproduct_resolved_stable_phi4_mul (a b : StableResolvedPhi4HopfH) :
    coproduct_resolved_stable_phi4 (a * b)
      = coproduct_resolved_stable_phi4 a * coproduct_resolved_stable_phi4 b :=
  map_mul _ _ _

/-- **body-629 (Step 4, GENERATOR COMPUTATION RULE) — `Δᵣˢ` on a stable resolved-graph generator.**  The
primitive 2 terms plus the W‴ forest sum, made EXPLICIT: for a graph `G` owning the family CD and the stable
certificate, the coproduct of its generator is `X x ⊗ 1 + 1 ⊗ X x + stableForestSum G hSt`. -/
theorem coproduct_resolved_stable_phi4_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF))
    (hSt : StableResolvedBoundaryIds G) :
    coproduct_resolved_stable_phi4 (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
      = (MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt) ⊗ₜ[ℚ] (1 : StableResolvedPhi4HopfH)
          + (1 : StableResolvedPhi4HopfH) ⊗ₜ[ℚ] MvPolynomial.X (G.toStableResolvedPhi4HopfGen hCD hSt))
        + stableForestSum G hSt := by
  rw [coproduct_resolved_stable_phi4_X]
  unfold stableCoproductGen
  congr 1
  show stableForestSumClass G.toResolvedClass = stableForestSum G hSt
  rw [stableForestSumClass_mk]
  unfold stableForestSumTotal
  rw [dif_pos hSt]

end GaugeGeometry.QFT.Combinatorial
