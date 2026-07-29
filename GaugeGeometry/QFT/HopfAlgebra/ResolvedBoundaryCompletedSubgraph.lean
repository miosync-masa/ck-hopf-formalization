import GaugeGeometry.QFT.HopfAlgebra.Phi4WDoublePrimeFullSupply
import GaugeGeometry.QFT.Combinatorial.BoundaryCompletedSubgraph

/-!
# QFT-R1-body-589 — resolved boundary-ID completion + left component generator

Body-567's **reserved seat**.  The flat boundary completion (body-567) deliberately left origin
traceability *not provided* — flat `ExternalLeg`s collapse, so a cut leg cannot be traced back to the
edge that induced it.  Here the resolved `edgeId`/`legId` make traceability a **theorem**, via an
**even/odd `legId` namespace** that keeps existing-leg-derived and cut-edge-derived legs collision-free:

```text
existingLegId ℓ := ⟨2 * ℓ.legId.id⟩        -- EVEN  : faithful embedding of the existing leg
boundaryLegId  e := ⟨2 * e.edgeId.id + 1⟩   -- ODD   : the induced / cut leg
```

Even and odd are disjoint, so the two leg families never collide, and `LegIdsUnique` on the completed
graph follows from ambient `LegIdsUnique` (existing legs) + `EdgeIdsUnique` (induced legs) + parity.

## Contents

* Step 1 `resolvedIsBoundaryEdge` / `resolvedBoundaryEdges` / `resolvedInsideEndpoint` + the load-bearing
  `resolvedBoundaryEdges_forget` (exact multiplicity, via the general flat collapse + a map/filter commute).
* Step 2 `existingLegId` / `boundaryLegId` / `encodeExistingLeg` / `boundaryExternalLeg` + forget matches,
  mapPerm coherence, even/odd disjointness, per-family injectivity.
* Step 3 `boundaryCompletedResolvedExternalLegs` + card / support / `LegIdsUnique` + **traceability**.
* Step 4 `boundaryCompletedResolvedGraph` + `EdgeIdsUnique`/`LegIdsUnique` + the **strict forget equality**.
* Step 5 `boundaryCompletedResolvedGraph_mapPerm` + the family-CD packaging.
* Step 6 `ResolvedFeynmanSubgraph.toResolvedPhi4HopfGenBoundaryCompleted` + value anchor + mapPerm invariance.

Per the HALT: no forest product / coproduct / coassoc / Measure / E / rep*; no W″ closure migration; zero
new `class`/`structure`/`instance`; the leg encoding is the even/odd namespace (never a bare
`legId := edgeId`); the target generator is `ResolvedPhi4HopfGen` (not flat `Phi4HopfGen`); multiplicity is
kept (`Multiset`, no `Finset`/dedup on boundary legs).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Generic multiset engines (self-contained, count-based) -/

/-- **General flat collapse.**  For any flat subgraph `δ`, its boundary edges (defined by filtering the
*complement* `H.internalEdges - δ.internalEdges`) equal the filter over *all* of `H.internalEdges`: no
internal edge of `δ` is a boundary edge (both endpoints lie inside `δ`), so the subtraction is inert under
the boundary filter. -/
theorem FeynmanSubgraph.boundaryEdges_eq_filter_internalEdges {H : FeynmanGraph}
    (δ : FeynmanSubgraph H) :
    δ.boundaryEdges = H.internalEdges.filter δ.IsBoundaryEdge := by
  unfold FeynmanSubgraph.boundaryEdges FeynmanSubgraph.complementEdges
  rw [Multiset.ext]
  intro e'
  by_cases hp : δ.IsBoundaryEdge e'
  · rw [Multiset.count_filter_of_pos hp, Multiset.count_filter_of_pos hp, Multiset.count_sub]
    have hz : Multiset.count e' δ.internalEdges = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      obtain ⟨hs, ht⟩ := δ.edges_supported e' hmem
      rcases hp with ⟨_, hout⟩ | ⟨hout, _⟩
      · exact hout ht
      · exact hout hs
    omega
  · rw [Multiset.count_filter_of_neg hp, Multiset.count_filter_of_neg hp]

/-- **Map/filter commute (predicate transport).**  If `q a ↔ p (g a)` pointwise, filtering by `q` then
mapping equals mapping then filtering by `p`.  Count-based, so decidability instances are absorbed. -/
theorem Multiset.map_filter_of_iff {α β : Type*} [DecidableEq β]
    (g : α → β) (s : Multiset α)
    (q : α → Prop) [DecidablePred q] (p : β → Prop) [DecidablePred p]
    (h : ∀ a, q a ↔ p (g a)) :
    (s.filter q).map g = (s.map g).filter p := by
  rw [Multiset.ext]
  intro b
  rw [Multiset.count_map, Multiset.count_filter, Multiset.count_map, Multiset.filter_filter]
  by_cases hb : p b
  · rw [if_pos hb]
    congr 1
    apply Multiset.filter_congr
    intro a _
    constructor
    · rintro ⟨hba, _⟩; exact hba
    · intro hba; exact ⟨hba, (h a).mpr (hba ▸ hb)⟩
  · rw [if_neg hb, Multiset.card_eq_zero, Multiset.filter_eq_nil]
    rintro a _ ⟨rfl, hqa⟩
    exact hb ((h a).mp hqa)

namespace ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — resolved boundary edges -/

/-- A resolved internal edge is a *boundary edge* for `γ` iff exactly one endpoint lies in `γ.vertices`
(the resolved mirror of the flat `IsBoundaryEdge`). -/
def resolvedIsBoundaryEdge (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) : Prop :=
  (e.source ∈ γ.vertices ∧ e.target ∉ γ.vertices) ∨
  (e.source ∉ γ.vertices ∧ e.target ∈ γ.vertices)

/-- The resolved boundary predicate is the flat boundary predicate on the forgotten edge (`rfl`:
`γ.forget.vertices` and `e.forget` endpoints reduce to `γ.vertices`, `e` endpoints). -/
theorem resolvedIsBoundaryEdge_iff_forget (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    γ.resolvedIsBoundaryEdge e ↔ γ.forget.IsBoundaryEdge e.forget := Iff.rfl

/-- The resolved boundary edges of `γ` (with multiplicity): every internal edge of the ambient `G` that is
a boundary edge for `γ`.  Filtering over all of `G.internalEdges` is legitimate because `γ`'s own edges are
never boundary (both endpoints inside). -/
noncomputable def resolvedBoundaryEdges (γ : ResolvedFeynmanSubgraph G) : Multiset ResolvedFeynmanEdge :=
  G.internalEdges.filter γ.resolvedIsBoundaryEdge

/-- The endpoint of a boundary edge that lies inside `γ` (mirrors the flat `boundaryInsideVertex`). -/
def resolvedInsideEndpoint (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) : VertexId :=
  if e.source ∈ γ.vertices then e.source else e.target

/-- The inside endpoint agrees with the flat one on `forget` (`rfl`). -/
theorem resolvedInsideEndpoint_forget (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    γ.resolvedInsideEndpoint e = γ.forget.boundaryInsideVertex e.forget := rfl

/-- The inside endpoint of a boundary edge lies in `γ.vertices`. -/
theorem resolvedInsideEndpoint_mem (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge)
    (h : γ.resolvedIsBoundaryEdge e) : γ.resolvedInsideEndpoint e ∈ γ.vertices := by
  unfold resolvedInsideEndpoint
  by_cases hs : e.source ∈ γ.vertices
  · rw [if_pos hs]; exact hs
  · rw [if_neg hs]
    rcases h with ⟨hs', _⟩ | ⟨_, ht⟩
    · exact absurd hs' hs
    · exact ht

@[simp] theorem resolvedBoundaryEdges_mem {γ : ResolvedFeynmanSubgraph G} {e : ResolvedFeynmanEdge} :
    e ∈ γ.resolvedBoundaryEdges ↔ e ∈ G.internalEdges ∧ γ.resolvedIsBoundaryEdge e := by
  unfold resolvedBoundaryEdges; rw [Multiset.mem_filter]

/-- **body-589 (Step 1, LOAD-BEARING) — resolved boundary edges forget exactly to the flat ones.**  The
map/filter commute lands the resolved filter as a flat filter over `G.forget.internalEdges`, and the general
flat collapse rewrites the flat boundary edges (over the complement) to that same filter.  Exact
multiplicity — no `Finset`/dedup. -/
theorem resolvedBoundaryEdges_forget (γ : ResolvedFeynmanSubgraph G) :
    γ.resolvedBoundaryEdges.map ResolvedFeynmanEdge.forget = γ.forget.boundaryEdges := by
  rw [FeynmanSubgraph.boundaryEdges_eq_filter_internalEdges]
  unfold resolvedBoundaryEdges
  exact Multiset.map_filter_of_iff ResolvedFeynmanEdge.forget G.internalEdges
    γ.resolvedIsBoundaryEdge γ.forget.IsBoundaryEdge
    (fun e => γ.resolvedIsBoundaryEdge_iff_forget e)

/-! ## Step 2 — collision-free even/odd leg-ID encoding -/

/-- The EVEN `legId` namespace: faithful identity-preserving embedding of an existing leg. -/
def existingLegId (ℓ : ResolvedExternalLeg) : ResolvedLegId := ⟨2 * ℓ.legId.id⟩

/-- The ODD `legId` namespace: the induced / cut leg of a boundary edge. -/
def boundaryLegId (e : ResolvedFeynmanEdge) : ResolvedLegId := ⟨2 * e.edgeId.id + 1⟩

/-- Even and odd `legId`s never collide. -/
theorem existingLegId_ne_boundaryLegId (ℓ : ResolvedExternalLeg) (e : ResolvedFeynmanEdge) :
    existingLegId ℓ ≠ boundaryLegId e := by
  unfold existingLegId boundaryLegId
  intro h
  have : 2 * ℓ.legId.id = 2 * e.edgeId.id + 1 := congrArg ResolvedLegId.id h
  omega

/-- Re-encode an existing leg into the EVEN namespace (identity-carrying, endpoints untouched). -/
def encodeExistingLeg (ℓ : ResolvedExternalLeg) : ResolvedExternalLeg where
  legId := existingLegId ℓ
  attachedTo := ℓ.attachedTo
  sector := ℓ.sector

/-- The induced boundary leg of `e`: attached to the inside endpoint, ODD `legId`, edge's own sector. -/
def boundaryExternalLeg (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) : ResolvedExternalLeg where
  legId := boundaryLegId e
  attachedTo := γ.resolvedInsideEndpoint e
  sector := e.sector

@[simp] theorem encodeExistingLeg_legId (ℓ : ResolvedExternalLeg) :
    (encodeExistingLeg ℓ).legId = existingLegId ℓ := rfl

@[simp] theorem boundaryExternalLeg_legId (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    (γ.boundaryExternalLeg e).legId = boundaryLegId e := rfl

/-- The re-encoded existing leg forgets to the same flat leg (the id is dropped). -/
@[simp] theorem encodeExistingLeg_forget (ℓ : ResolvedExternalLeg) :
    (encodeExistingLeg ℓ).forget = ℓ.forget := rfl

/-- The induced boundary leg forgets to body-567's flat induced leg (inside endpoint + sector agree). -/
@[simp] theorem boundaryExternalLeg_forget (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    (γ.boundaryExternalLeg e).forget = γ.forget.boundaryExternalLeg e.forget := rfl

/-- Even-namespace encoding commutes with `ResolvedExternalLeg.map σ` (ids preserved by `map`). -/
theorem encodeExistingLeg_map (σ : Equiv.Perm VertexId) (ℓ : ResolvedExternalLeg) :
    encodeExistingLeg (ResolvedExternalLeg.map σ ℓ) =
      ResolvedExternalLeg.map σ (encodeExistingLeg ℓ) := rfl

/-- Even-namespace encoding is injective (parity + ambient leg-id uniqueness feeds this via `.id`). -/
theorem existingLegId_injOn_of_legIdUnique
    (hLeg : G.LegIdsUnique) {ℓ₁ ℓ₂ : ResolvedExternalLeg}
    (h₁ : ℓ₁ ∈ G.externalLegs) (h₂ : ℓ₂ ∈ G.externalLegs)
    (h : existingLegId ℓ₁ = existingLegId ℓ₂) : ℓ₁ = ℓ₂ := by
  apply hLeg ℓ₁ h₁ ℓ₂ h₂
  have h2 : 2 * ℓ₁.legId.id = 2 * ℓ₂.legId.id := congrArg ResolvedLegId.id h
  have hid : ℓ₁.legId.id = ℓ₂.legId.id := by omega
  exact congrArg ResolvedLegId.mk hid

/-- Odd-namespace encoding is injective (parity + ambient edge-id uniqueness). -/
theorem boundaryLegId_injOn_of_edgeIdUnique
    (hEdge : G.EdgeIdsUnique) {e₁ e₂ : ResolvedFeynmanEdge}
    (h₁ : e₁ ∈ G.internalEdges) (h₂ : e₂ ∈ G.internalEdges)
    (h : boundaryLegId e₁ = boundaryLegId e₂) : e₁ = e₂ := by
  apply hEdge e₁ h₁ e₂ h₂
  have h2 : 2 * e₁.edgeId.id + 1 = 2 * e₂.edgeId.id + 1 := congrArg ResolvedLegId.id h
  have hid : e₁.edgeId.id = e₂.edgeId.id := by omega
  exact congrArg ResolvedEdgeId.mk hid

/-! ## Step 3 — the completed leg multiset -/

/-- The boundary-completed resolved external legs: the (EVEN-)re-encoded ambient legs plus the (ODD-)induced
boundary legs.  Multiplicity kept (`Multiset.map` + `+`). -/
noncomputable def boundaryCompletedResolvedExternalLegs (γ : ResolvedFeynmanSubgraph G) :
    Multiset ResolvedExternalLeg :=
  γ.externalLegs.map encodeExistingLeg + γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg

@[simp] theorem boundaryCompletedResolvedExternalLegs_card (γ : ResolvedFeynmanSubgraph G) :
    (γ.boundaryCompletedResolvedExternalLegs).card
      = γ.externalLegs.card + γ.resolvedBoundaryEdges.card := by
  unfold boundaryCompletedResolvedExternalLegs
  rw [Multiset.card_add, Multiset.card_map, Multiset.card_map]

/-- **body-589 (Step 3) — completed legs forget to body-567's completed legs.**  The EVEN legs forget to the
ambient legs; the ODD legs forget to the flat induced legs (Step 1 + `boundaryExternalLeg_forget`). -/
theorem boundaryCompletedResolvedExternalLegs_forget (γ : ResolvedFeynmanSubgraph G) :
    (γ.boundaryCompletedResolvedExternalLegs).map ResolvedExternalLeg.forget
      = γ.forget.boundaryCompletedExternalLegs := by
  unfold boundaryCompletedResolvedExternalLegs FeynmanSubgraph.boundaryCompletedExternalLegs
    FeynmanSubgraph.inducedBoundaryExternalLegs
  rw [Multiset.map_add]
  congr 1
  · rw [Multiset.map_map]
    rw [ResolvedFeynmanSubgraph.forget_externalLegs]
    exact Multiset.map_congr rfl (fun ℓ _ => rfl)
  · rw [Multiset.map_map, ← γ.resolvedBoundaryEdges_forget, Multiset.map_map]
    exact Multiset.map_congr rfl (fun e _ => rfl)

/-- Every completed leg is supported on `γ.vertices` (EVEN via `γ.legs_supported`, ODD via the inside
endpoint). -/
theorem boundaryCompletedResolvedExternalLegs_supported (γ : ResolvedFeynmanSubgraph G) :
    ∀ ℓ ∈ γ.boundaryCompletedResolvedExternalLegs, ℓ.attachedTo ∈ γ.vertices := by
  intro ℓ hℓ
  unfold boundaryCompletedResolvedExternalLegs at hℓ
  rcases Multiset.mem_add.mp hℓ with h | h
  · rcases Multiset.mem_map.mp h with ⟨m, hm, rfl⟩
    exact γ.legs_supported m hm
  · rcases Multiset.mem_map.mp h with ⟨e, he, rfl⟩
    have hbe : γ.resolvedIsBoundaryEdge e := (resolvedBoundaryEdges_mem.mp he).2
    exact γ.resolvedInsideEndpoint_mem e hbe

/-- **body-589 (Step 3, HEADLINE) — cut-leg origin traceability.**  A leg in the induced (ODD) family comes
from a *unique* boundary edge: its ODD `legId` recovers the edge via `e.edgeId.id = (ℓ.legId.id - 1)/2`, and
`EdgeIdsUnique` promotes uniqueness of the id to uniqueness of the edge.  This is exactly the traceability
that flat `ExternalLeg` cannot provide (body-567's `NOT PROVIDED`). -/
theorem boundaryExternalLeg_traceable
    (γ : ResolvedFeynmanSubgraph G) (hEdge : G.EdgeIdsUnique)
    {ℓ : ResolvedExternalLeg} (hℓ : ℓ ∈ γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg) :
    ∃! e, e ∈ γ.resolvedBoundaryEdges ∧ γ.boundaryExternalLeg e = ℓ := by
  rcases Multiset.mem_map.mp hℓ with ⟨e, he, rfl⟩
  refine ⟨e, ⟨he, rfl⟩, ?_⟩
  rintro e' ⟨he', hval⟩
  have hleg : boundaryLegId e' = boundaryLegId e :=
    congrArg ResolvedExternalLeg.legId hval
  exact boundaryLegId_injOn_of_edgeIdUnique hEdge
    (resolvedBoundaryEdges_mem.mp he').1 (resolvedBoundaryEdges_mem.mp he).1 hleg

/-- **body-589 (Step 3) — the completed leg multiset has unique `legId`s.**  EVEN×EVEN via ambient
`LegIdsUnique`, ODD×ODD via ambient `EdgeIdsUnique`, EVEN×ODD via parity. -/
theorem boundaryCompletedResolvedExternalLegs_legIdsUnique
    (γ : ResolvedFeynmanSubgraph G) (hLeg : G.LegIdsUnique) (hEdge : G.EdgeIdsUnique) :
    ∀ ℓ₁ ∈ γ.boundaryCompletedResolvedExternalLegs, ∀ ℓ₂ ∈ γ.boundaryCompletedResolvedExternalLegs,
      ℓ₁.legId = ℓ₂.legId → ℓ₁ = ℓ₂ := by
  intro ℓ₁ h₁ ℓ₂ h₂ hid
  unfold boundaryCompletedResolvedExternalLegs at h₁ h₂
  rcases Multiset.mem_add.mp h₁ with hA₁ | hB₁ <;> rcases Multiset.mem_add.mp h₂ with hA₂ | hB₂
  · -- EVEN × EVEN
    rcases Multiset.mem_map.mp hA₁ with ⟨m₁, hm₁, rfl⟩
    rcases Multiset.mem_map.mp hA₂ with ⟨m₂, hm₂, rfl⟩
    have hme : existingLegId m₁ = existingLegId m₂ := hid
    have := existingLegId_injOn_of_legIdUnique hLeg
      (Multiset.mem_of_le γ.externalLegs_le hm₁) (Multiset.mem_of_le γ.externalLegs_le hm₂) hme
    rw [this]
  · -- EVEN × ODD (parity contradiction)
    rcases Multiset.mem_map.mp hA₁ with ⟨m₁, _, rfl⟩
    rcases Multiset.mem_map.mp hB₂ with ⟨e₂, _, rfl⟩
    exact absurd hid (existingLegId_ne_boundaryLegId m₁ e₂)
  · -- ODD × EVEN (parity contradiction)
    rcases Multiset.mem_map.mp hB₁ with ⟨e₁, _, rfl⟩
    rcases Multiset.mem_map.mp hA₂ with ⟨m₂, _, rfl⟩
    exact absurd hid.symm (existingLegId_ne_boundaryLegId m₂ e₁)
  · -- ODD × ODD
    rcases Multiset.mem_map.mp hB₁ with ⟨e₁, he₁, rfl⟩
    rcases Multiset.mem_map.mp hB₂ with ⟨e₂, he₂, rfl⟩
    have hee : boundaryLegId e₁ = boundaryLegId e₂ := hid
    have := boundaryLegId_injOn_of_edgeIdUnique hEdge
      (resolvedBoundaryEdges_mem.mp he₁).1 (resolvedBoundaryEdges_mem.mp he₂).1 hee
    rw [this]

/-! ## Step 4 — the boundary-completed resolved graph -/

/-- **body-589 (Step 4) — the boundary-completed resolved graph.**  Same vertices / internal edges as `γ`;
external legs are the completed (EVEN + ODD) leg multiset. -/
noncomputable def boundaryCompletedResolvedGraph (γ : ResolvedFeynmanSubgraph G) : ResolvedFeynmanGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.boundaryCompletedResolvedExternalLegs

@[simp] theorem boundaryCompletedResolvedGraph_vertices (γ : ResolvedFeynmanSubgraph G) :
    γ.boundaryCompletedResolvedGraph.vertices = γ.vertices := rfl

@[simp] theorem boundaryCompletedResolvedGraph_internalEdges (γ : ResolvedFeynmanSubgraph G) :
    γ.boundaryCompletedResolvedGraph.internalEdges = γ.internalEdges := rfl

@[simp] theorem boundaryCompletedResolvedGraph_externalLegs (γ : ResolvedFeynmanSubgraph G) :
    γ.boundaryCompletedResolvedGraph.externalLegs = γ.boundaryCompletedResolvedExternalLegs := rfl

/-- `EdgeIdsUnique` is inherited (internal edges unchanged from ambient `G`). -/
theorem boundaryCompletedResolvedGraph_edgeIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (hEdge : G.EdgeIdsUnique) : γ.boundaryCompletedResolvedGraph.EdgeIdsUnique := by
  intro e₁ h₁ e₂ h₂ hid
  rw [boundaryCompletedResolvedGraph_internalEdges] at h₁ h₂
  exact hEdge e₁ (Multiset.mem_of_le γ.internalEdges_le h₁)
    e₂ (Multiset.mem_of_le γ.internalEdges_le h₂) hid

/-- `LegIdsUnique` is derived from the even/odd encoding (Step 3). -/
theorem boundaryCompletedResolvedGraph_legIdsUnique (γ : ResolvedFeynmanSubgraph G)
    (hLeg : G.LegIdsUnique) (hEdge : G.EdgeIdsUnique) :
    γ.boundaryCompletedResolvedGraph.LegIdsUnique :=
  γ.boundaryCompletedResolvedExternalLegs_legIdsUnique hLeg hEdge

/-- **body-589 (Step 4, LOAD-BEARING) — strict forget equality.**  The forgotten resolved completed graph
is *raw-equal* (all three fields) to body-567's flat completed graph.  Not a class equality. -/
theorem boundaryCompletedResolvedGraph_forget (γ : ResolvedFeynmanSubgraph G) :
    γ.boundaryCompletedResolvedGraph.forget = γ.forget.boundaryCompletedGraph := by
  simp only [ResolvedFeynmanGraph.forget, FeynmanSubgraph.boundaryCompletedGraph,
    boundaryCompletedResolvedGraph, FeynmanGraph.mk.injEq]
  exact ⟨rfl, rfl, γ.boundaryCompletedResolvedExternalLegs_forget⟩

/-- The forgotten completed graph is well-formed (via the strict forget equality + body-567). -/
theorem boundaryCompletedResolvedGraph_forget_wellFormed (γ : ResolvedFeynmanSubgraph G) :
    γ.boundaryCompletedResolvedGraph.forget.WellFormed := by
  rw [boundaryCompletedResolvedGraph_forget]
  exact γ.forget.boundaryCompletedGraph_wellFormed

/-! ## Step 5 — rename coherence + family CD packaging -/

/-- **body-589 (Step 5) — boundary completion commutes with the resolved relabeling `mapPerm σ`.**  Ids are
`mapPerm`-invariant, and the even/odd encoding commutes with `ResolvedExternalLeg.map σ`.  Boundary edges
transport by the map/filter commute (the boundary predicate is `mapPerm`-stable, `σ` injective). -/
theorem boundaryCompletedResolvedGraph_mapPerm (σ : Equiv.Perm VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    (γ.mapPerm σ).boundaryCompletedResolvedGraph
      = (γ.boundaryCompletedResolvedGraph).mapPerm σ := by
  -- resolvedIsBoundaryEdge is stable under mapPerm (σ injective)
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
  -- boundary edges transport exactly
  have hBE : (γ.mapPerm σ).resolvedBoundaryEdges
      = γ.resolvedBoundaryEdges.map (ResolvedFeynmanEdge.map σ) := by
    unfold resolvedBoundaryEdges
    symm
    exact Multiset.map_filter_of_iff (ResolvedFeynmanEdge.map σ) G.internalEdges
      γ.resolvedIsBoundaryEdge (γ.mapPerm σ).resolvedIsBoundaryEdge hpred
  -- boundaryExternalLeg commutes with map σ
  have hleg : ∀ e : ResolvedFeynmanEdge,
      ResolvedExternalLeg.map σ (γ.boundaryExternalLeg e)
        = (γ.mapPerm σ).boundaryExternalLeg (ResolvedFeynmanEdge.map σ e) := by
    intro e
    unfold boundaryExternalLeg ResolvedExternalLeg.map resolvedInsideEndpoint
    simp only [ResolvedFeynmanEdge.map, ResolvedFeynmanSubgraph.mapPerm_vertices,
      σ.injective.mem_finset_image]
    by_cases hs : e.source ∈ γ.vertices <;> simp [hs, boundaryLegId]
  -- the completed leg multiset transports
  have hcomp : (γ.mapPerm σ).boundaryCompletedResolvedExternalLegs
      = (γ.boundaryCompletedResolvedExternalLegs).map (ResolvedExternalLeg.map σ) := by
    unfold boundaryCompletedResolvedExternalLegs
    rw [Multiset.map_add]
    congr 1
    · rw [ResolvedFeynmanSubgraph.mapPerm_externalLegs, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl (fun ℓ _ => (encodeExistingLeg_map σ ℓ).symm)
    · rw [hBE, Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl (fun e _ => (hleg e).symm)
  simp only [boundaryCompletedResolvedGraph, ResolvedFeynmanGraph.mapPerm,
    ResolvedFeynmanGraph.mk.injEq]
  exact ⟨rfl, rfl, hcomp⟩

/-! ## Step 6 — resolved left-component φ⁴ generator -/

/-- **body-589 (Step 6) — the boundary-completed graph as a φ⁴ resolved generator.**  Takes the family-CD
witness on the *completed* forgotten graph (component CD is an input, degree recovery is body-567's) and
produces a `ResolvedPhi4HopfGen`.  This is body-567's reserved left factor, now resolved. -/
noncomputable def toResolvedPhi4HopfGenBoundaryCompleted
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    ResolvedPhi4HopfGen :=
  γ.boundaryCompletedResolvedGraph.toResolvedPhi4HopfGen hCD

@[simp] theorem toResolvedPhi4HopfGenBoundaryCompleted_val
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD).val
      = γ.boundaryCompletedResolvedGraph.toResolvedClass := rfl

end ResolvedFeynmanSubgraph

end GaugeGeometry.QFT.Combinatorial
