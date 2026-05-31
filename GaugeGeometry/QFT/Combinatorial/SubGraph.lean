import GaugeGeometry.QFT.Combinatorial.FeynmanGraphs
import GaugeGeometry.QFT.Combinatorial.SupportGraph

/-!
# Feynman subgraphs

A *Feynman subgraph* of a labeled combinatorial Feynman graph `G` consists
of a finite vertex subset together with `Multiset`-inclusion certificates
for its internal edges and its original external legs, plus the usual
support conditions.

## Boundary edges

In BPHZ / forest-formula style renormalization, a subgraph `γ ⊂ G` has
*two* kinds of external structure:

* the original external legs of `G` that land on `γ.vertices`,
* the internal edges of `G` whose endpoints straddle the boundary of `γ`
  (one endpoint inside `γ.vertices`, the other outside).

We keep these conceptually separate:

* `externalLegs` on the structure records only the first kind,
* `boundaryEdges` is a derived function that produces the second kind.

This matches the QFT convention that `γ`'s propagators include its own
internal lines but *exclude* boundary-crossing lines of `G`; boundary
lines are treated as additional external legs of `γ` from the renormali-
zation viewpoint.
-/

namespace GaugeGeometry.QFT.Combinatorial

/--
A labeled subgraph of a Feynman graph `G`.

Fields:
* `vertices` — a subset of `G.vertices`,
* `internalEdges` — a `Multiset`-submultiset of `G.internalEdges`, all of whose
  endpoints lie in `vertices`,
* `externalLegs` — a `Multiset`-submultiset of `G.externalLegs`, all of whose
  attachment points lie in `vertices`.

Boundary-crossing edges of `G` are *not* recorded here; they are computed
separately via `boundaryEdges`.
-/
structure FeynmanSubgraph (G : FeynmanGraph) where
  vertices : Finset VertexId
  internalEdges : Multiset FeynmanEdge
  externalLegs : Multiset ExternalLeg
  vertices_subset : vertices ⊆ G.vertices
  internalEdges_le : internalEdges ≤ G.internalEdges
  externalLegs_le : externalLegs ≤ G.externalLegs
  edges_supported : ∀ e ∈ internalEdges, e.SupportedOn vertices
  legs_supported : ∀ ℓ ∈ externalLegs, ℓ.SupportedOn vertices

/-- Subgraphs are compared via their carrier fields; proof-valued fields
are ignored by proof irrelevance. -/
instance (G : FeynmanGraph) : DecidableEq (FeynmanSubgraph G) := by
  classical
  intro γ₁ γ₂
  by_cases hV : γ₁.vertices = γ₂.vertices
  · by_cases hI : γ₁.internalEdges = γ₂.internalEdges
    · by_cases hE : γ₁.externalLegs = γ₂.externalLegs
      · refine isTrue ?_
        cases γ₁; cases γ₂
        cases hV; cases hI; cases hE
        rfl
      · refine isFalse ?_
        intro h; apply hE; rw [h]
    · refine isFalse ?_
      intro h; apply hI; rw [h]
  · refine isFalse ?_
    intro h; apply hV; rw [h]

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/--
The subgraph obtained from a Feynman graph by taking all of it.
Useful as a trivial base case.
-/
def self (G : FeynmanGraph) (hG : G.WellFormed) : FeynmanSubgraph G where
  vertices := G.vertices
  internalEdges := G.internalEdges
  externalLegs := G.externalLegs
  vertices_subset := Finset.Subset.refl _
  internalEdges_le := le_refl _
  externalLegs_le := le_refl _
  edges_supported := hG.1
  legs_supported := hG.2

/--
The empty subgraph: no vertices, no edges, no legs.
This is always a valid subgraph of any `G`.
-/
def empty (G : FeynmanGraph) : FeynmanSubgraph G where
  vertices := ∅
  internalEdges := 0
  externalLegs := 0
  vertices_subset := Finset.empty_subset _
  internalEdges_le := Multiset.zero_le _
  externalLegs_le := Multiset.zero_le _
  edges_supported := by intro e he; simp at he
  legs_supported := by intro ℓ hℓ; simp at hℓ

/--
Internal edges of `G` *not* included in the subgraph `γ`, counted as a
multiset: `G.internalEdges - γ.internalEdges`.
-/
def complementEdges (γ : FeynmanSubgraph G) : Multiset FeynmanEdge :=
  G.internalEdges - γ.internalEdges

/--
An edge of `G` is a *boundary-crossing* edge for `γ` if it lies outside
`γ.internalEdges` (in the multiset sense) and has exactly one endpoint
in `γ.vertices`.

The "exactly one endpoint inside" condition is the QFT-standard way of
saying "this line becomes an external leg from `γ`'s point of view".
-/
def IsBoundaryEdge (γ : FeynmanSubgraph G) (e : FeynmanEdge) : Prop :=
  (e.source ∈ γ.vertices ∧ e.target ∉ γ.vertices) ∨
  (e.source ∉ γ.vertices ∧ e.target ∈ γ.vertices)

instance (γ : FeynmanSubgraph G) (e : FeynmanEdge) :
    Decidable (γ.IsBoundaryEdge e) := by
  unfold IsBoundaryEdge
  exact inferInstance

/--
Boundary-crossing edges of `G` with respect to `γ`, as a multiset.
These play the role of *additional external legs* of `γ` induced by the
ambient graph.
-/
def boundaryEdges (γ : FeynmanSubgraph G) : Multiset FeynmanEdge :=
  γ.complementEdges.filter γ.IsBoundaryEdge

/-- Number of vertices of the subgraph. -/
def vertexCount (γ : FeynmanSubgraph G) : Nat := γ.vertices.card

/-- Number of internal edges of the subgraph, counted with multiplicity. -/
def internalEdgeCount (γ : FeynmanSubgraph G) : Nat := γ.internalEdges.card

/-- Number of ambient external legs attached to the subgraph. -/
def externalLegCount (γ : FeynmanSubgraph G) : Nat := γ.externalLegs.card

/-- Number of boundary-crossing edges. -/
def boundaryEdgeCount (γ : FeynmanSubgraph G) : Nat := γ.boundaryEdges.card

/--
Euler-type loop number of a subgraph, taken in `Int` for the same reason
as `FeynmanGraph.loopNumber`:
`L(γ) = E(γ) - V(γ) + 1`.
-/
def loopNumber (γ : FeynmanSubgraph G) : Int :=
  (γ.internalEdgeCount : Int) - (γ.vertexCount : Int) + 1

/--
The **induced Feynman graph** of a subgraph `γ`: reinterpret `γ`'s
carrier fields (`vertices`, `internalEdges`, `externalLegs`) directly
as a `FeynmanGraph`. Boundary-crossing edges of the ambient `G` are
*not* included here — they are recovered via `boundaryEdges` when
needed.

This lets connectivity predicates defined on `FeynmanGraph`
(`IsSupportConnected`, `IsOnePI`, etc.) apply to subgraphs without
duplication.
-/
def toFeynmanGraph (γ : FeynmanSubgraph G) : FeynmanGraph where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.externalLegs

@[simp] theorem toFeynmanGraph_vertices (γ : FeynmanSubgraph G) :
    γ.toFeynmanGraph.vertices = γ.vertices := rfl

@[simp] theorem toFeynmanGraph_internalEdges (γ : FeynmanSubgraph G) :
    γ.toFeynmanGraph.internalEdges = γ.internalEdges := rfl

@[simp] theorem toFeynmanGraph_externalLegs (γ : FeynmanSubgraph G) :
    γ.toFeynmanGraph.externalLegs = γ.externalLegs := rfl

/--
The induced graph of a subgraph is always well-formed: the
`edges_supported` and `legs_supported` fields of `FeynmanSubgraph`
supply exactly the required conditions.
-/
theorem toFeynmanGraph_wellFormed (γ : FeynmanSubgraph G) :
    γ.toFeynmanGraph.WellFormed :=
  ⟨γ.edges_supported, γ.legs_supported⟩

/-!
### H1.5 — Contraction

Contraction of a subgraph `γ ⊆ G` replaces `γ` with a single fresh
vertex `star_γ`:

- `vertices := (G.vertices \ γ.vertices) ∪ {star_γ}`
- `internalEdges := (G.internalEdges - γ.internalEdges)` each retargeted
  so that endpoints in `γ.vertices` are redirected to `star_γ`. Edges
  fully inside `γ` are removed (already excluded by the multiset
  difference); boundary edges and external edges of `G` are kept.
- `externalLegs := G.externalLegs` each retargeted the same way.

The fresh vertex is produced by `FeynmanGraph.freshVertex G.vertices`
(H1.1), which guarantees `star_γ ∉ G.vertices ⊇ γ.vertices`.
-/

/--
The fresh contracted vertex associated to a subgraph: a `VertexId` not
appearing in the ambient graph `G.vertices` (and in particular not in
`γ.vertices`).
-/
def contractedVertex (_ : FeynmanSubgraph G) : VertexId :=
  FeynmanGraph.freshVertex G.vertices

theorem contractedVertex_not_mem_G (γ : FeynmanSubgraph G) :
    γ.contractedVertex ∉ G.vertices :=
  FeynmanGraph.freshVertex_not_mem G.vertices

theorem contractedVertex_not_mem_γ (γ : FeynmanSubgraph G) :
    γ.contractedVertex ∉ γ.vertices := by
  intro h
  exact γ.contractedVertex_not_mem_G (γ.vertices_subset h)

/--
H1.5' — **Contraction of a subgraph with an explicit star vertex.**

The generalized form of `contract` that takes the fresh vertex
`star` as a parameter. This is the primitive used by the
`contract_chain` identity (H1.17), which requires the two-step
contraction and the one-step contraction to use *the same* star
vertex in order for the underlying `FeynmanGraph` structures to
agree literally (not just up to isomorphism).

The default `contract` below specializes `star := freshVertex
G.vertices`, matching the HOPF_DECOMPOSITION.md signature.
-/
def contractWith (γ : FeynmanSubgraph G) (star : VertexId) : FeynmanGraph where
  vertices := (G.vertices \ γ.vertices) ∪ {star}
  internalEdges :=
    γ.complementEdges.map (FeynmanEdge.retarget γ.vertices star)
  externalLegs :=
    G.externalLegs.map (ExternalLeg.retarget γ.vertices star)

@[simp] theorem contractWith_vertices (γ : FeynmanSubgraph G) (star : VertexId) :
    (γ.contractWith star).vertices =
      (G.vertices \ γ.vertices) ∪ {star} := rfl

@[simp] theorem contractWith_internalEdges (γ : FeynmanSubgraph G)
    (star : VertexId) :
    (γ.contractWith star).internalEdges =
      γ.complementEdges.map (FeynmanEdge.retarget γ.vertices star) := rfl

@[simp] theorem contractWith_externalLegs (γ : FeynmanSubgraph G)
    (star : VertexId) :
    (γ.contractWith star).externalLegs =
      G.externalLegs.map (ExternalLeg.retarget γ.vertices star) := rfl

/--
H1.5 — **Contraction of a subgraph** `γ ⊆ G`.

Produces a fresh `FeynmanGraph` on the vertex set
`(G.vertices \ γ.vertices) ∪ {star_γ}` whose internal edges are the
complement `G.internalEdges - γ.internalEdges` with endpoints in `γ`
redirected to `star_γ`, and whose external legs are those of `G`
similarly retargeted.

This is `contractWith γ γ.contractedVertex`.
-/
def contract (γ : FeynmanSubgraph G) : FeynmanGraph :=
  γ.contractWith γ.contractedVertex

@[simp] theorem contract_eq_contractWith (γ : FeynmanSubgraph G) :
    γ.contract = γ.contractWith γ.contractedVertex := rfl

@[simp] theorem contract_vertices (γ : FeynmanSubgraph G) :
    γ.contract.vertices =
      (G.vertices \ γ.vertices) ∪ {γ.contractedVertex} := rfl

@[simp] theorem contract_internalEdges (γ : FeynmanSubgraph G) :
    γ.contract.internalEdges =
      γ.complementEdges.map
        (FeynmanEdge.retarget γ.vertices γ.contractedVertex) := rfl

@[simp] theorem contract_externalLegs (γ : FeynmanSubgraph G) :
    γ.contract.externalLegs =
      G.externalLegs.map
        (ExternalLeg.retarget γ.vertices γ.contractedVertex) := rfl

/--
H1.6 — **Vertex set of the contracted graph**, matching the design-note
name. Equivalent to `contract_vertices`; re-exported to preserve the
HOPF_DECOMPOSITION.md numbering.
-/
theorem contract_vertices_eq (γ : FeynmanSubgraph G) :
    γ.contract.vertices =
      (G.vertices \ γ.vertices) ∪ {γ.contractedVertex} :=
  γ.contract_vertices

/--
H1.7 — **Internal edges of the contracted graph** as a `Multiset`,
matching the design-note name. Equivalent to `contract_internalEdges`;
re-exported to preserve the HOPF_DECOMPOSITION.md numbering.
-/
theorem contract_internalEdges_eq (γ : FeynmanSubgraph G) :
    γ.contract.internalEdges =
      γ.complementEdges.map
        (FeynmanEdge.retarget γ.vertices γ.contractedVertex) :=
  γ.contract_internalEdges


/--
H1.8 — **Vertex count of the contracted graph**.

The contracted graph has `G.vertexCount - γ.vertexCount + 1` vertices:
the `γ.vertexCount` vertices of `γ` are collapsed to a single fresh
vertex `star_γ`, while the remaining `G.vertices \ γ.vertices` are
kept.

Note: The design note HOPF_DECOMPOSITION.md asks for a `γ.IsNonempty`
hypothesis, but this hypothesis is not needed for the arithmetic
itself — subsumed by `γ.vertices ⊆ G.vertices`. We drop the hypothesis
here and reintroduce it downstream only where genuinely needed
(e.g. for `IsProper` arguments in H1.15).
-/
theorem vertexCount_contract (γ : FeynmanSubgraph G) :
    γ.contract.vertexCount = (G.vertexCount - γ.vertexCount) + 1 := by
  unfold FeynmanGraph.vertexCount vertexCount
  rw [contract_vertices]
  -- `star_γ ∉ G.vertices \ γ.vertices` because it is not even in `G.vertices`.
  have hstar_not_mem : γ.contractedVertex ∉ G.vertices \ γ.vertices := by
    intro h
    exact γ.contractedVertex_not_mem_G (Finset.mem_sdiff.mp h).1
  -- Disjoint union: `|A ∪ {star}| = |A| + 1`.
  rw [Finset.card_union_of_disjoint
        (Finset.disjoint_singleton_right.mpr hstar_not_mem)]
  rw [Finset.card_sdiff_of_subset γ.vertices_subset]
  simp

/--
H1.9 — **Internal-edge count of the contracted graph**.

The boundary edges are kept (just retargeted); only edges fully
inside `γ` are removed. This is exactly the cardinality of
`γ.complementEdges = G.internalEdges - γ.internalEdges`, since
`Multiset.map` preserves cardinality.
-/
theorem internalEdgeCount_contract (γ : FeynmanSubgraph G) :
    γ.contract.internalEdgeCount =
      (G.internalEdges - γ.internalEdges).card := by
  unfold FeynmanGraph.internalEdgeCount
  rw [contract_internalEdges, Multiset.card_map]
  rfl

/--
H1.10 — **External-leg count of the contracted graph**.

External legs are retargeted, not removed: their count is preserved.
-/
theorem externalLegCount_contract (γ : FeynmanSubgraph G) :
    γ.contract.externalLegCount = G.externalLegCount := by
  unfold FeynmanGraph.externalLegCount
  rw [contract_externalLegs, Multiset.card_map]

/--
H1.11 — **Well-formedness is preserved under contraction**.

Every retargeted endpoint lands either in `G.vertices \ γ.vertices`
(when its original lay outside `γ`) or in `{star_γ}` (when it lay
inside). In either case it lies in the contracted vertex set
`(G.vertices \ γ.vertices) ∪ {star_γ}`.
-/
theorem wellFormed_contract {γ : FeynmanSubgraph G} (hG : G.WellFormed) :
    γ.contract.WellFormed := by
  refine ⟨?_, ?_⟩
  · -- Internal edges
    intro e' he'
    rw [contract_internalEdges] at he'
    rcases Multiset.mem_map.mp he' with ⟨e, hecompl, rfl⟩
    have heG : e ∈ G.internalEdges := by
      have hle : γ.complementEdges ≤ G.internalEdges := by
        unfold complementEdges; exact Multiset.sub_le_self _ _
      exact Multiset.mem_of_le hle hecompl
    have hsupp : e.SupportedOn G.vertices := hG.1 e heG
    simp [FeynmanEdge.SupportedOn] at hsupp
    obtain ⟨hs, ht⟩ := hsupp
    refine ⟨?_, ?_⟩
    · rw [contract_vertices]
      simp only [FeynmanEdge.retarget_source]
      by_cases hsγ : e.source ∈ γ.vertices
      · simp [hsγ]
      · simp only [if_neg hsγ]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs, hsγ⟩)
    · rw [contract_vertices]
      simp only [FeynmanEdge.retarget_target]
      by_cases htγ : e.target ∈ γ.vertices
      · simp [htγ]
      · simp only [if_neg htγ]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht, htγ⟩)
  · -- External legs
    intro ℓ' hℓ'
    rw [contract_externalLegs] at hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓG, rfl⟩
    have hsupp : ℓ.SupportedOn G.vertices := hG.2 ℓ hℓG
    simp [ExternalLeg.SupportedOn] at hsupp
    rw [contract_vertices]
    simp only [ExternalLeg.SupportedOn, ExternalLeg.retarget_attachedTo]
    by_cases hℓγ : ℓ.attachedTo ∈ γ.vertices
    · simp [hℓγ]
    · simp only [if_neg hℓγ]
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsupp, hℓγ⟩)

/-!
### H1.12 / H1.13 / H1.14 — Loop-number additivity under contraction

The Euler loop number of the contracted graph decomposes into
`G.loopNumber - γ.loopNumber` plus a formal *boundary correction*
term, which ultimately vanishes because the subgraph's internal edges
sit inside `G`'s internal edges in the multiset sense — boundary edges
are not *subtracted twice*, they are *retargeted and kept*.

We introduce `boundaryCorrection` as a named quantity (H1.12) to make
the decomposition explicit, then prove it vanishes (H1.13), and finally
combine the two for the clean additivity (H1.14). This three-step
decomposition mirrors the `complementEdges / boundaryEdges / retarget`
thinking required for the H1.17 `contract_chain` proof.
-/

/--
Boundary correction to the naive loop-number subtraction
`G.loopNumber - γ.loopNumber` under contraction. Defined as

`boundaryCorrection γ := (G.internalEdges - γ.internalEdges).card
                          - (G.internalEdgeCount - γ.internalEdgeCount)`

(in `Int`). H1.13 shows this is always zero, because
`γ.internalEdges ≤ G.internalEdges` by construction.
-/
def boundaryCorrection (γ : FeynmanSubgraph G) : Int :=
  ((G.internalEdges - γ.internalEdges).card : Int) -
    ((G.internalEdgeCount : Int) - (γ.internalEdgeCount : Int))

/--
H1.12 — **Loop-number decomposition under contraction** (raw form).

Directly from the count formulas `vertexCount_contract` and
`internalEdgeCount_contract`, the contracted graph's loop number
equals `G.loopNumber - γ.loopNumber` plus the formal boundary
correction introduced above. The correction is shown to vanish in
H1.13, yielding the clean form H1.14.

Note: the `γ.IsConnected` hypothesis listed in HOPF_DECOMPOSITION.md
is not needed here — the multiset inequality `γ.internalEdges ≤
G.internalEdges` is a definitional field of `FeynmanSubgraph` and is
enough for the arithmetic. We keep the signature free of connectivity
assumptions; downstream users can strengthen as needed.
-/
theorem loopNumber_contract_decompose (γ : FeynmanSubgraph G) :
    γ.contract.loopNumber =
      G.loopNumber - γ.loopNumber + γ.boundaryCorrection := by
  unfold FeynmanGraph.loopNumber loopNumber boundaryCorrection
  have hV : γ.contract.vertexCount = (G.vertexCount - γ.vertexCount) + 1 :=
    γ.vertexCount_contract
  have hE : γ.contract.internalEdgeCount =
      (G.internalEdges - γ.internalEdges).card :=
    γ.internalEdgeCount_contract
  have hsub : γ.vertexCount ≤ G.vertexCount :=
    Finset.card_le_card γ.vertices_subset
  have hcast :
      ((G.vertexCount - γ.vertexCount : Nat) : Int) =
        (G.vertexCount : Int) - (γ.vertexCount : Int) :=
    Int.ofNat_sub hsub
  rw [hV, hE]
  rw [show ((G.vertexCount - γ.vertexCount + 1 : Nat) : Int) =
        ((G.vertexCount - γ.vertexCount : Nat) : Int) + 1 from by
        simp]
  rw [hcast]
  omega

/--
H1.13 — **The boundary correction vanishes.**

The correction term `(G.internalEdges - γ.internalEdges).card -
(G.internalEdgeCount - γ.internalEdgeCount)` is zero because
`γ.internalEdges ≤ G.internalEdges` (a definitional field of
`FeynmanSubgraph`), so multiset subtraction and cardinality commute
exactly: `(A - B).card = A.card - B.card` when `B ≤ A`.

This is where "boundary edges are kept, only retargeted" enters the
loop-number calculation: boundary edges are *in* `complementEdges`,
they are *not* subtracted twice, and the `γ.internalEdges_le`
inequality is exactly the statement that γ's internal multiset fits
inside G's.
-/
theorem boundaryCorrection_eq_zero_of_subgraph (γ : FeynmanSubgraph G) :
    γ.boundaryCorrection = 0 := by
  unfold boundaryCorrection FeynmanGraph.internalEdgeCount internalEdgeCount
  have hle : γ.internalEdges ≤ G.internalEdges := γ.internalEdges_le
  have hcard_sub : (G.internalEdges - γ.internalEdges).card =
      G.internalEdges.card - γ.internalEdges.card :=
    Multiset.card_sub hle
  have hcard_le : γ.internalEdges.card ≤ G.internalEdges.card :=
    Multiset.card_le_card hle
  have hcast :
      ((G.internalEdges.card - γ.internalEdges.card : Nat) : Int) =
        (G.internalEdges.card : Int) - (γ.internalEdges.card : Int) :=
    Int.ofNat_sub hcard_le
  rw [hcard_sub, hcast]
  omega

/--
H1.14 — **Loop-number additivity under contraction** (clean form).

Combining H1.12 and H1.13:

`loopNumber (γ.contract) = G.loopNumber - γ.loopNumber`.

The connectivity hypothesis suggested by HOPF_DECOMPOSITION.md is not
needed: the identity holds for every subgraph `γ ⊆ G` because it is
driven entirely by multiset subtraction + vertex-set subtraction, both
of which are exact thanks to the `FeynmanSubgraph` subtype invariants.
-/
theorem loopNumber_contract_eq_sub (γ : FeynmanSubgraph G) :
    γ.contract.loopNumber = G.loopNumber - γ.loopNumber := by
  rw [γ.loopNumber_contract_decompose,
      γ.boundaryCorrection_eq_zero_of_subgraph, add_zero]

/-!
### H1.16 — Connectivity is preserved under contraction

Every adjacency in `G` survives in `γ.contract`, modulo collapsing
`γ`'s vertices to the single fresh vertex `star_γ`. A walk in `G`
therefore yields a walk in `γ.contract` after projecting each visited
vertex through `contractProj γ x = if x ∈ γ.vertices then star_γ else
x`.

The only subtle step is when the `G`-walk traverses a `γ`-internal
edge: such an edge is *removed* by contraction, but both its endpoints
project to `star_γ`, so no `γ.contract`-step is needed at that stage.
-/

/--
Projection from ambient vertices of `G` to the contracted vertex set:
all vertices inside `γ.vertices` collapse to `star_γ`, others are
kept.
-/
def contractProj (γ : FeynmanSubgraph G) (x : VertexId) : VertexId :=
  if x ∈ γ.vertices then γ.contractedVertex else x

theorem contractProj_of_mem {γ : FeynmanSubgraph G} {x : VertexId}
    (hx : x ∈ γ.vertices) :
    γ.contractProj x = γ.contractedVertex := by
  unfold contractProj; simp [hx]

theorem contractProj_of_not_mem {γ : FeynmanSubgraph G} {x : VertexId}
    (hx : x ∉ γ.vertices) :
    γ.contractProj x = x := by
  unfold contractProj; simp [hx]

theorem contractProj_mem_contract_vertices
    (γ : FeynmanSubgraph G) {x : VertexId} (hx : x ∈ G.vertices) :
    γ.contractProj x ∈ γ.contract.vertices := by
  rw [contract_vertices]
  unfold contractProj
  by_cases hxγ : x ∈ γ.vertices
  · simp [hxγ]
  · simp only [if_neg hxγ]
    exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxγ⟩)

/--
Transport of a single `SupportAdj` step from `G` to `γ.contract`:
after projecting through `contractProj γ`, every `G`-adjacency gives a
`γ.contract`-reachability between the projected endpoints.

Case analysis on whether the witnessing edge lies inside `γ`:

* **Inside (`e ∈ γ.internalEdges`):** both endpoints lie in
  `γ.vertices` (by `γ.edges_supported`), so both project to
  `star_γ` and reachability is reflexive.
* **Outside (`e ∉ γ.internalEdges`):** `e ∈ γ.complementEdges`, so
  its retarget `e.retarget γ.vertices star_γ` sits in
  `γ.contract.internalEdges`. Its endpoints are the projected
  endpoints. Either they coincide (refl) or they are distinct
  (one `SupportAdj` step).
-/
theorem contract_step_supportReachable
    (γ : FeynmanSubgraph G) {u v : VertexId} (h : G.SupportAdj u v) :
    γ.contract.SupportReachable (γ.contractProj u) (γ.contractProj v) := by
  obtain ⟨_hne, e, heG, hend⟩ := h
  by_cases heγ : e ∈ γ.internalEdges
  · -- Inside γ: both endpoints in γ.vertices, projections coincide.
    have hsupp : e.SupportedOn γ.vertices := γ.edges_supported e heγ
    simp [FeynmanEdge.SupportedOn] at hsupp
    obtain ⟨hsγ, htγ⟩ := hsupp
    have huγ : u ∈ γ.vertices := by
      rcases hend with ⟨hs, _⟩ | ⟨_, ht⟩
      · exact hs ▸ hsγ
      · exact ht ▸ htγ
    have hvγ : v ∈ γ.vertices := by
      rcases hend with ⟨_, ht⟩ | ⟨hs, _⟩
      · exact ht ▸ htγ
      · exact hs ▸ hsγ
    rw [contractProj_of_mem huγ, contractProj_of_mem hvγ]
    exact FeynmanGraph.SupportReachable.refl _ _
  · -- Outside γ: retargeted edge lives in contract.internalEdges.
    have hecompl : e ∈ γ.complementEdges := by
      unfold complementEdges
      rw [Multiset.mem_sub]
      -- `γ.count e = 0` because `e ∉ γ.internalEdges`, and `0 < G.count e` from membership.
      have hγcount : γ.internalEdges.count e = 0 :=
        Multiset.count_eq_zero.mpr heγ
      have hGcount : 0 < G.internalEdges.count e :=
        Multiset.count_pos.mpr heG
      omega
    have hretarget :
        (e.retarget γ.vertices γ.contractedVertex) ∈ γ.contract.internalEdges := by
      rw [contract_internalEdges]
      exact Multiset.mem_map.mpr ⟨e, hecompl, rfl⟩
    -- The retargeted edge's endpoints are precisely the projected u, v.
    have hsrc : (e.retarget γ.vertices γ.contractedVertex).source =
        if e.source ∈ γ.vertices then γ.contractedVertex else e.source := rfl
    have htgt : (e.retarget γ.vertices γ.contractedVertex).target =
        if e.target ∈ γ.vertices then γ.contractedVertex else e.target := rfl
    -- Split on whether projected u and v coincide.
    by_cases hprojEq : γ.contractProj u = γ.contractProj v
    · rw [hprojEq]; exact FeynmanGraph.SupportReachable.refl _ _
    · -- Build a single SupportAdj step in γ.contract.
      refine SimpleGraph.Adj.reachable (G := γ.contract.toSimpleGraph) ?_
      rw [FeynmanGraph.toSimpleGraph_adj]
      refine ⟨hprojEq, e.retarget γ.vertices γ.contractedVertex, hretarget, ?_⟩
      rcases hend with ⟨hseq, hteq⟩ | ⟨hseq, hteq⟩
      · -- e.source = u, e.target = v
        left
        refine ⟨?_, ?_⟩
        · rw [hsrc]; unfold contractProj; rw [hseq]
        · rw [htgt]; unfold contractProj; rw [hteq]
      · -- e.source = v, e.target = u
        right
        refine ⟨?_, ?_⟩
        · rw [hsrc]; unfold contractProj; rw [hseq]
        · rw [htgt]; unfold contractProj; rw [hteq]

/--
Transport of a reflexive-transitive `SupportReachable` chain from `G`
to `γ.contract`: the projected endpoints remain reachable. This is
the `Relation.ReflTransGen` induction lifting Step C along every walk
in `G`.
-/
theorem contract_path_supportReachable
    (γ : FeynmanSubgraph G) {u v : VertexId} (h : G.SupportReachable u v) :
    γ.contract.SupportReachable (γ.contractProj u) (γ.contractProj v) := by
  unfold FeynmanGraph.SupportReachable at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact FeynmanGraph.SupportReachable.refl _ _
  | @tail x y _ hxy ih =>
    have hstep : G.SupportAdj x y := by
      rw [← FeynmanGraph.toSimpleGraph_adj]; exact hxy
    have hstep_reach := γ.contract_step_supportReachable hstep
    exact ih.trans hstep_reach


/--
H0.7 — **Subgraph connectedness**: `γ` is connected when its induced
Feynman graph is support-connected.
-/
def IsConnected (γ : FeynmanSubgraph G) : Prop :=
  γ.toFeynmanGraph.IsSupportConnected

@[simp] theorem isConnected_def (γ : FeynmanSubgraph G) :
    γ.IsConnected ↔ γ.toFeynmanGraph.IsSupportConnected := Iff.rfl

/--
H0.8 — **Subgraph 1PI predicate**: `γ` is 1PI when its induced
Feynman graph is 1PI (support-connected and bridge-free).
-/
def IsOnePI (γ : FeynmanSubgraph G) : Prop :=
  γ.toFeynmanGraph.IsOnePI

@[simp] theorem isOnePI_def (γ : FeynmanSubgraph G) :
    γ.IsOnePI ↔ γ.toFeynmanGraph.IsOnePI := Iff.rfl

theorem IsOnePI.isConnected {γ : FeynmanSubgraph G} (h : γ.IsOnePI) :
    γ.IsConnected := h.isSupportConnected

/--
A subgraph is *proper* if it is strictly smaller than `G`: either it
omits at least one vertex, or it omits at least one internal edge (in
the multiset sense).
-/
def IsProper (γ : FeynmanSubgraph G) : Prop :=
  γ.vertices ⊂ G.vertices ∨ γ.internalEdges < G.internalEdges

/--
A subgraph is *nontrivial* if it contains at least one vertex.
Useful as a nonemptiness hypothesis for divergence-style conditions.
-/
def IsNonempty (γ : FeynmanSubgraph G) : Prop :=
  0 < γ.vertexCount

/--
H1.15 — **Loop number strictly decreases under contraction of a
loopful subgraph.**

If `γ` is loopful (`0 < γ.loopNumber`), then
`γ.contract.loopNumber < G.loopNumber`. This is the key termination
fact for the well-founded recursion driving the Connes–Kreimer
coproduct (H4.3).

The `IsProper` and `IsConnected` hypotheses listed in
HOPF_DECOMPOSITION.md are not needed for this arithmetic consequence
of H1.14: `γ.contract.loopNumber = G.loopNumber - γ.loopNumber` and
`0 < γ.loopNumber` give the strict inequality directly. We keep both
hypotheses in the signature to match the design note, so downstream
callers who already have them ready can cite H1.15 verbatim.
-/
theorem loopNumber_contract_lt_of_proper_connected_loopful
    {γ : FeynmanSubgraph G}
    (_hProper : γ.IsProper) (_hConn : γ.IsConnected)
    (hLoopful : 0 < γ.loopNumber) :
    γ.contract.loopNumber < G.loopNumber := by
  have h := γ.loopNumber_contract_eq_sub
  omega

/--
H1.16 — **Connectivity is preserved under contraction**.

If the ambient graph `G` is support-connected and the subgraph `γ` is
nonempty, then the contracted graph `γ.contract` is also
support-connected.

Note on hypotheses: HOPF_DECOMPOSITION.md asks for `G.IsConnected ∧
γ.IsConnected`. We use `G.IsSupportConnected` (strictly stronger than
`IsConnected` for multigraphs with self-loops, but the natural notion
at the topology layer) and we *add* `γ.IsNonempty`. The nonemptiness
hypothesis is genuinely needed: if `γ.vertices = ∅`, then
`γ.contract` equals `G` plus an isolated fresh vertex `star_γ`, which
is not support-connected whenever `G` has any vertex at all. The
`γ.IsConnected` hypothesis from the design note is *not* used here —
we can prove the theorem from `G`-connectivity alone — but we keep a
parameter for it to match the design-note interface, and record the
redundancy for future tightening.
-/
theorem IsConnected_contract_of_IsConnected
    {γ : FeynmanSubgraph G}
    (hG : G.IsSupportConnected) (_hγconn : γ.IsConnected)
    (hγne : γ.IsNonempty) :
    γ.contract.IsSupportConnected := by
  -- Extract a witness vertex `w₀ ∈ γ.vertices` to serve as the preimage of star.
  have hne : γ.vertices.Nonempty := Finset.card_pos.mp hγne
  obtain ⟨w₀, hw₀⟩ := hne
  have hw₀G : w₀ ∈ G.vertices := γ.vertices_subset hw₀
  -- Every vertex of `γ.contract` has a preimage in `G.vertices`
  -- under `contractProj γ`.
  have preimage : ∀ x, x ∈ γ.contract.vertices →
      ∃ x₀ ∈ G.vertices, γ.contractProj x₀ = x := by
    intro x hx
    rw [contract_vertices] at hx
    rcases Finset.mem_union.mp hx with hsdiff | hstar
    · rcases Finset.mem_sdiff.mp hsdiff with ⟨hG', hγ'⟩
      exact ⟨x, hG', contractProj_of_not_mem hγ'⟩
    · rw [Finset.mem_singleton] at hstar
      exact ⟨w₀, hw₀G, by rw [contractProj_of_mem hw₀]; exact hstar.symm⟩
  -- Given two `γ.contract`-vertices, lift to `G`-reachability and project.
  intro u' v' hu' hv'
  obtain ⟨u, huG, rfl⟩ := preimage u' hu'
  obtain ⟨v, hvG, rfl⟩ := preimage v' hv'
  exact γ.contract_path_supportReachable (hG huG hvG)

/-!
### Inclusion order on subgraphs

We put the natural pointwise ordering: `γ₁ ≤ γ₂` iff the vertex set,
internal-edge multiset, and external-leg multiset all include.
-/

/--
Pointwise inclusion order: `γ₁ ≤ γ₂` iff all three fields include.
-/
instance : LE (FeynmanSubgraph G) where
  le γ₁ γ₂ :=
    γ₁.vertices ⊆ γ₂.vertices ∧
    γ₁.internalEdges ≤ γ₂.internalEdges ∧
    γ₁.externalLegs ≤ γ₂.externalLegs

theorem le_def {γ₁ γ₂ : FeynmanSubgraph G} :
    γ₁ ≤ γ₂ ↔
      γ₁.vertices ⊆ γ₂.vertices ∧
      γ₁.internalEdges ≤ γ₂.internalEdges ∧
      γ₁.externalLegs ≤ γ₂.externalLegs := Iff.rfl

theorem le_refl' (γ : FeynmanSubgraph G) : γ ≤ γ :=
  ⟨Finset.Subset.refl _, le_refl _, le_refl _⟩

theorem le_trans' {γ₁ γ₂ γ₃ : FeynmanSubgraph G}
    (h₁₂ : γ₁ ≤ γ₂) (h₂₃ : γ₂ ≤ γ₃) : γ₁ ≤ γ₃ :=
  ⟨Finset.Subset.trans h₁₂.1 h₂₃.1,
   le_trans h₁₂.2.1 h₂₃.2.1,
   le_trans h₁₂.2.2 h₂₃.2.2⟩

/--
`empty G ≤ γ` for any subgraph `γ`.
-/
theorem empty_le (γ : FeynmanSubgraph G) : empty G ≤ γ := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.empty_subset _
  · exact Multiset.zero_le _
  · exact Multiset.zero_le _

/-!
### Monotonicity of counts under inclusion
-/

theorem vertexCount_le_of_le {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁ ≤ γ₂) :
    γ₁.vertexCount ≤ γ₂.vertexCount :=
  Finset.card_le_card h.1

theorem internalEdgeCount_le_of_le {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁ ≤ γ₂) :
    γ₁.internalEdgeCount ≤ γ₂.internalEdgeCount :=
  Multiset.card_le_card h.2.1

theorem externalLegCount_le_of_le {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁ ≤ γ₂) :
    γ₁.externalLegCount ≤ γ₂.externalLegCount :=
  Multiset.card_le_card h.2.2

/-!
### H1.17 prep — `contractRestrict`: representing `γ₁ ≤ γ₂ ≤ G` inside
`γ₁.contractWith star`

Given nested subgraphs `γ₁ ≤ γ₂` of `G` and a star vertex `star` used
in `γ₁.contractWith star`, we represent `γ₂` as a subgraph of
`γ₁.contractWith star`. This is the restriction map used by H1.17
(`contract_chain`) — the two-step contraction first collapses `γ₁`,
then the image `γ₂/γ₁` inside the quotient graph.

Design choices:

* Vertices: `(γ₂.vertices \ γ₁.vertices) ∪ {star}`. The `star`
  replaces `γ₁.vertices` (which has been collapsed) and the
  remaining `γ₂ \ γ₁` survives verbatim.
* Internal edges: `(γ₂.internalEdges - γ₁.internalEdges)` retargeted
  through `γ₁.vertices ↦ star`. Edges entirely inside `γ₁` are
  already gone from `γ₁.contractWith star`; the rest of `γ₂`
  survives as retargeted edges.
* External legs: `γ₂.externalLegs` retargeted the same way.
-/

/--
H1.17-prep — restriction of `γ₂` to a subgraph of `γ₁.contractWith star`.

Requires: `γ₁ ≤ γ₂` (nested subgraphs). No direct hypothesis on `star`
is needed here; compatibility with `γ₂.vertices` is automatic in
callers because `star = γ₁.contractedVertex ∉ G.vertices ⊇
γ₂.vertices`.
-/
def contractRestrict {γ₁ γ₂ : FeynmanSubgraph G}
    (_hle : γ₁ ≤ γ₂) (star : VertexId) :
    FeynmanSubgraph (γ₁.contractWith star) where
  vertices := (γ₂.vertices \ γ₁.vertices) ∪ {star}
  internalEdges :=
    (γ₂.internalEdges - γ₁.internalEdges).map
      (FeynmanEdge.retarget γ₁.vertices star)
  externalLegs :=
    γ₂.externalLegs.map (ExternalLeg.retarget γ₁.vertices star)
  vertices_subset := by
    rw [contractWith_vertices]
    intro v hv
    rcases Finset.mem_union.mp hv with hsdiff | hstar
    · rcases Finset.mem_sdiff.mp hsdiff with ⟨hv₂, hv₁⟩
      exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨γ₂.vertices_subset hv₂, hv₁⟩)
    · exact Finset.mem_union_right _ hstar
  internalEdges_le := by
    rw [contractWith_internalEdges]
    refine Multiset.map_le_map ?_
    -- (γ₂.I - γ₁.I) ≤ (G.I - γ₁.I) because γ₂.I ≤ G.I (γ₂'s subtype field).
    unfold complementEdges
    exact Multiset.sub_le_sub_right γ₂.internalEdges_le
  externalLegs_le := by
    rw [contractWith_externalLegs]
    exact Multiset.map_le_map γ₂.externalLegs_le
  edges_supported := by
    intro e' he'
    rcases Multiset.mem_map.mp he' with ⟨e, hesub, rfl⟩
    have he₂ : e ∈ γ₂.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) hesub
    have hsupp : e.SupportedOn γ₂.vertices := γ₂.edges_supported e he₂
    simp [FeynmanEdge.SupportedOn] at hsupp
    obtain ⟨hs, ht⟩ := hsupp
    refine ⟨?_, ?_⟩
    · simp only [FeynmanEdge.retarget_source]
      by_cases hsγ₁ : e.source ∈ γ₁.vertices
      · simp [hsγ₁]
      · simp only [if_neg hsγ₁]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hs, hsγ₁⟩)
    · simp only [FeynmanEdge.retarget_target]
      by_cases htγ₁ : e.target ∈ γ₁.vertices
      · simp [htγ₁]
      · simp only [if_neg htγ₁]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨ht, htγ₁⟩)
  legs_supported := by
    intro ℓ' hℓ'
    rcases Multiset.mem_map.mp hℓ' with ⟨ℓ, hℓ₂, rfl⟩
    have hsupp : ℓ.SupportedOn γ₂.vertices := γ₂.legs_supported ℓ hℓ₂
    simp [ExternalLeg.SupportedOn] at hsupp
    simp only [ExternalLeg.SupportedOn, ExternalLeg.retarget_attachedTo]
    by_cases hℓγ₁ : ℓ.attachedTo ∈ γ₁.vertices
    · simp [hℓγ₁]
    · simp only [if_neg hℓγ₁]
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsupp, hℓγ₁⟩)

/--
Basic projection: vertices of `contractRestrict`.
-/
@[simp] theorem contractRestrict_vertices
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId) :
    (contractRestrict hle star).vertices =
      (γ₂.vertices \ γ₁.vertices) ∪ {star} := rfl

@[simp] theorem contractRestrict_internalEdges
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId) :
    (contractRestrict hle star).internalEdges =
      (γ₂.internalEdges - γ₁.internalEdges).map
        (FeynmanEdge.retarget γ₁.vertices star) := rfl

@[simp] theorem contractRestrict_externalLegs
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId) :
    (contractRestrict hle star).externalLegs =
      γ₂.externalLegs.map (ExternalLeg.retarget γ₁.vertices star) := rfl

/-!
### H1.17 Step B — Vertex-set agreement

For `γ₁ ≤ γ₂ ≤ G` and a star vertex `star ∉ G.vertices`, the vertex
sets of the two-step contraction and the one-step contraction agree:

```
((γ₁.contractWith star).vertices \ (contractRestrict hle star).vertices)
  ∪ {star}
  = (G.vertices \ γ₂.vertices) ∪ {star}
  = (γ₂.contractWith star).vertices
```

The key calculation cancels the two occurrences of `γ₁.vertices`
(one introduced by the first contraction, one removed by the
restriction).
-/

/--
Step B — vertex equality for `contract_chain`.
-/
theorem contract_chain_vertices
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId)
    (hstar_notG : star ∉ G.vertices) :
    ((γ₁.contractWith star).vertices \ (contractRestrict hle star).vertices) ∪
        {star}
      = (γ₂.contractWith star).vertices := by
  rw [contractRestrict_vertices, contractWith_vertices, contractWith_vertices]
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv_diff | hv_star
    · -- v ∈ A \ B where A = (G\γ₁) ∪ {star}, B = (γ₂\γ₁) ∪ {star}
      rcases Finset.mem_sdiff.mp hv_diff with ⟨hvA, hvB⟩
      rcases Finset.mem_union.mp hvA with hv_Gγ₁ | hv_star_eq
      · -- v ∈ G \ γ₁
        rcases Finset.mem_sdiff.mp hv_Gγ₁ with ⟨hvG, hvγ₁⟩
        by_cases hvγ₂ : v ∈ γ₂.vertices
        · -- v ∈ γ₂ \ γ₁ ⊆ B, contradicting hvB
          exact absurd (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvγ₂, hvγ₁⟩)) hvB
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvG, hvγ₂⟩)
      · -- v = star
        rw [Finset.mem_singleton] at hv_star_eq
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hv_star_eq)
    · -- v ∈ {star}
      rw [Finset.mem_singleton] at hv_star
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hv_star)
  · intro hv
    rcases Finset.mem_union.mp hv with hv_Gγ₂ | hv_star
    · -- v ∈ G \ γ₂
      rcases Finset.mem_sdiff.mp hv_Gγ₂ with ⟨hvG, hvγ₂⟩
      have hvγ₁ : v ∉ γ₁.vertices := fun h => hvγ₂ (hle.1 h)
      have hv_ne_star : v ≠ star := fun hveq => hstar_notG (hveq ▸ hvG)
      -- Want: v ∈ ((G\γ₁) ∪ {star}) \ ((γ₂\γ₁) ∪ {star}) ∪ {star}
      apply Finset.mem_union_left
      refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hvG, hvγ₁⟩)
      · intro hvmem
        rcases Finset.mem_union.mp hvmem with hv_γ₂γ₁ | hv_star_eq
        · exact hvγ₂ (Finset.mem_sdiff.mp hv_γ₂γ₁).1
        · exact hv_ne_star (Finset.mem_singleton.mp hv_star_eq)
    · rw [Finset.mem_singleton] at hv_star
      exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hv_star)

/-!
### H1.17 Step C.1 — Retarget composition

When `γ₁ ⊆ γ₂` and `star` is not one of the endpoints, composing two
retargets (first through `γ₁ ↦ star`, then through
`(γ₂ \ γ₁) ∪ {star} ↦ star`) equals a single retarget through
`γ₂ ↦ star`. Case analysis on whether each endpoint lies in
`γ₁ / γ₂\γ₁ / γ₂ᶜ`.
-/
/-- Step C.1 analogue for external legs. -/
theorem ExternalLeg.retarget_comp_eq
    {γ₁ γ₂ : Finset VertexId} (hle : γ₁ ⊆ γ₂) {star : VertexId}
    (ℓ : ExternalLeg)
    (hℓ : ℓ.attachedTo ≠ star) :
    (ℓ.retarget γ₁ star).retarget ((γ₂ \ γ₁) ∪ {star}) star =
      ℓ.retarget γ₂ star := by
  apply ExternalLeg.mk.injEq _ _ _ _ |>.mpr
  refine ⟨?_, rfl⟩
  simp only [ExternalLeg.retarget_attachedTo]
  by_cases hℓγ₁ : ℓ.attachedTo ∈ γ₁
  · have hℓγ₂ : ℓ.attachedTo ∈ γ₂ := hle hℓγ₁
    have hstar_mem : star ∈ (γ₂ \ γ₁) ∪ {star} :=
      Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
    rw [if_pos hℓγ₁, if_pos hstar_mem, if_pos hℓγ₂]
  · rw [if_neg hℓγ₁]
    by_cases hℓγ₂ : ℓ.attachedTo ∈ γ₂
    · have hmem : ℓ.attachedTo ∈ (γ₂ \ γ₁) ∪ {star} :=
        Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hℓγ₂, hℓγ₁⟩)
      rw [if_pos hmem, if_pos hℓγ₂]
    · have hnotmem : ℓ.attachedTo ∉ (γ₂ \ γ₁) ∪ {star} := by
        intro h
        rcases Finset.mem_union.mp h with h1 | h2
        · exact hℓγ₂ (Finset.mem_sdiff.mp h1).1
        · exact hℓ (Finset.mem_singleton.mp h2)
      rw [if_neg hnotmem, if_neg hℓγ₂]

theorem retarget_comp_eq
    {γ₁ γ₂ : Finset VertexId} (hle : γ₁ ⊆ γ₂) {star : VertexId}
    (e : FeynmanEdge)
    (hs : e.source ≠ star) (ht : e.target ≠ star) :
    (e.retarget γ₁ star).retarget ((γ₂ \ γ₁) ∪ {star}) star =
      e.retarget γ₂ star := by
  apply FeynmanEdge.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, rfl⟩
  · -- source
    simp only [FeynmanEdge.retarget_source]
    by_cases hsγ₁ : e.source ∈ γ₁
    · -- e.source ∈ γ₁ ⊆ γ₂: inner gives star; outer keeps star since star ∈ {star}
      have hsγ₂ : e.source ∈ γ₂ := hle hsγ₁
      have hstar_mem : star ∈ (γ₂ \ γ₁) ∪ {star} :=
        Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
      rw [if_pos hsγ₁, if_pos hstar_mem, if_pos hsγ₂]
    · -- e.source ∉ γ₁: inner leaves source; outer decides
      rw [if_neg hsγ₁]
      by_cases hsγ₂ : e.source ∈ γ₂
      · -- e.source ∈ γ₂ \ γ₁: outer retargets to star
        have hmem : e.source ∈ (γ₂ \ γ₁) ∪ {star} :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hsγ₂, hsγ₁⟩)
        rw [if_pos hmem, if_pos hsγ₂]
      · -- e.source ∉ γ₂: outer leaves alone (also ∉ {star} by hs)
        have hnotmem : e.source ∉ (γ₂ \ γ₁) ∪ {star} := by
          intro h
          rcases Finset.mem_union.mp h with h1 | h2
          · exact hsγ₂ (Finset.mem_sdiff.mp h1).1
          · exact hs (Finset.mem_singleton.mp h2)
        rw [if_neg hnotmem, if_neg hsγ₂]
  · -- target (same)
    simp only [FeynmanEdge.retarget_target]
    by_cases htγ₁ : e.target ∈ γ₁
    · have htγ₂ : e.target ∈ γ₂ := hle htγ₁
      have hstar_mem : star ∈ (γ₂ \ γ₁) ∪ {star} :=
        Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl)
      rw [if_pos htγ₁, if_pos hstar_mem, if_pos htγ₂]
    · rw [if_neg htγ₁]
      by_cases htγ₂ : e.target ∈ γ₂
      · have hmem : e.target ∈ (γ₂ \ γ₁) ∪ {star} :=
          Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨htγ₂, htγ₁⟩)
        rw [if_pos hmem, if_pos htγ₂]
      · have hnotmem : e.target ∉ (γ₂ \ γ₁) ∪ {star} := by
          intro h
          rcases Finset.mem_union.mp h with h1 | h2
          · exact htγ₂ (Finset.mem_sdiff.mp h1).1
          · exact ht (Finset.mem_singleton.mp h2)
        rw [if_neg hnotmem, if_neg htγ₂]

/-!
### H1.17 Step C.2 — Multiset arithmetic helper

Local lemma: on a multiset where `f` is injective (via `InjOn` on the
support of `A`), `map` commutes with subtraction:

`(A - B).map f = A.map f - B.map f`   (when `B ≤ A`, `f` injective on `A`).

Mathlib has `Multiset.map_erase` (single-element version); we lift it
to multiset subtraction by induction on `B`.
-/

/-!
### H1.17 Step C.2 — Multiset additive decomposition

Under nesting `γ₁.I ≤ γ₂.I ≤ G.I`, the multiset `G.I - γ₁.I` decomposes
additively as

  `G.I - γ₁.I = (γ₂.I - γ₁.I) + (G.I - γ₂.I)`.

This is pure multiset arithmetic, provable elementwise via `count_sub`
+ `omega`. It is the key that lets us avoid `InjOn`-based reasoning:
after the decomposition, the 2-step contraction's `map r₂ (map r₁ (A +
B - A))` collapses to `map (r₂ ∘ r₁) B` by `add_sub_cancel_right`.
-/
private theorem internalEdges_additive_split
    (A B C : Multiset FeynmanEdge) (hAB : A ≤ B) (hBC : B ≤ C) :
    C - A = (B - A) + (C - B) := by
  ext e
  rw [Multiset.count_add, Multiset.count_sub, Multiset.count_sub,
      Multiset.count_sub]
  have h1 : A.count e ≤ B.count e := Multiset.count_le_of_le e hAB
  have h2 : B.count e ≤ C.count e := Multiset.count_le_of_le e hBC
  omega

/-!
### H1.17 Step C — InternalEdges equality

Combining the additive decomposition (Step C.2) with the retarget
composition (Step C.1), the 2-step contraction's internal edges agree
with the 1-step contraction's internal edges:

```
((γ₁.contractWith star).contractWith (contractRestrict hle star) star).internalEdges
  = (γ₂.contractWith star).internalEdges
```

The proof walks through:

1. Write `(G.I - γ₁.I) = (γ₂.I - γ₁.I) + (G.I - γ₂.I)` (Step C.2).
2. Distribute `map r₁` over `+` (`Multiset.map_add`).
3. Use `Multiset.add_sub_cancel_right` to cancel the common
   `(γ₂.I - γ₁.I).map r₁` term.
4. Apply `Multiset.map_map` to merge the two stacked `.map`s into
   `.map (r₂ ∘ r₁)`.
5. Apply `Multiset.map_congr` + `retarget_comp_eq` (Step C.1) to
   replace `r₂ ∘ r₁` with `r₂'` on the remaining `G.I - γ₂.I`.
-/
theorem contract_chain_internalEdges
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId)
    (hstar_notG : star ∉ G.vertices)
    (hG : G.WellFormed) :
    ((contractRestrict hle star).contractWith star).internalEdges
      = (γ₂.contractWith star).internalEdges := by
  -- Notation
  set r₁ := FeynmanEdge.retarget γ₁.vertices star with hr₁
  set r₂ := FeynmanEdge.retarget
      ((γ₂.vertices \ γ₁.vertices) ∪ {star}) star with hr₂
  set r₂' := FeynmanEdge.retarget γ₂.vertices star with hr₂'
  -- Unfold both contractions' internalEdges via the simp lemmas.
  rw [contractWith_internalEdges, contractWith_internalEdges]
  -- LHS: (contractRestrict hle star).complementEdges.map r₂
  -- RHS: γ₂.complementEdges.map r₂'
  -- Unfold complementEdges on both sides.
  unfold complementEdges
  -- LHS now: ((contractRestrict hle star's ambient).internalEdges
  --          - (contractRestrict hle star).internalEdges).map r₂
  -- ambient of contractRestrict is γ₁.contractWith star.
  rw [contractRestrict_internalEdges, contractWith_internalEdges]
  -- LHS now: ((G.I - γ₁.I).map r₁ - (γ₂.I - γ₁.I).map r₁).map r₂
  -- (using complementEdges unfolded on γ₁.contract side via contractWith_internalEdges).
  -- But wait: contractWith_internalEdges expanded `(γ₁.contractWith star).internalEdges`
  -- as `γ₁.complementEdges.map r₁`. Need to unfold γ₁.complementEdges too.
  show (γ₁.complementEdges.map r₁ -
         (γ₂.internalEdges - γ₁.internalEdges).map r₁).map r₂
      = (G.internalEdges - γ₂.internalEdges).map r₂'
  unfold complementEdges
  -- Now LHS = ((G.I - γ₁.I).map r₁ - (γ₂.I - γ₁.I).map r₁).map r₂
  -- RHS = (G.I - γ₂.I).map r₂'
  -- Step: additive decomposition of (G.I - γ₁.I).
  have hle_I : γ₁.internalEdges ≤ γ₂.internalEdges := hle.2.1
  have hle_GI : γ₂.internalEdges ≤ G.internalEdges := γ₂.internalEdges_le
  have hsplit :
      G.internalEdges - γ₁.internalEdges =
        (γ₂.internalEdges - γ₁.internalEdges) +
          (G.internalEdges - γ₂.internalEdges) :=
    internalEdges_additive_split _ _ _ hle_I hle_GI
  rw [hsplit, Multiset.map_add]
  -- Now: ((X + Y) - X).map r₂ where X := (γ₂.I - γ₁.I).map r₁, Y := (G.I - γ₂.I).map r₁
  rw [add_comm ((γ₂.internalEdges - γ₁.internalEdges).map r₁) _,
      Multiset.add_sub_cancel_right]
  -- Now: ((G.I - γ₂.I).map r₁).map r₂ = γ₂.complementEdges.map r₂'
  rw [Multiset.map_map]
  -- Now: (G.I - γ₂.I).map (r₂ ∘ r₁) = (G.I - γ₂.I).map r₂'
  -- Use map_congr + retarget_comp_eq on each remaining edge.
  refine Multiset.map_congr rfl ?_
  intro e he
  -- e ∈ G.I - γ₂.I ⊆ G.I, so e.source, e.target ∈ G.vertices.
  have heG : e ∈ G.internalEdges :=
    Multiset.mem_of_le (Multiset.sub_le_self _ _) he
  have hsupp : e.SupportedOn G.vertices := hG.1 e heG
  have hes : e.source ∈ G.vertices := hsupp.1
  have het : e.target ∈ G.vertices := hsupp.2
  have hs_ne : e.source ≠ star := fun h => hstar_notG (h ▸ hes)
  have ht_ne : e.target ≠ star := fun h => hstar_notG (h ▸ het)
  -- Apply retarget_comp_eq.
  show r₂ (r₁ e) = r₂' e
  simp only [hr₂, hr₁, hr₂']
  exact retarget_comp_eq hle.1 e hs_ne ht_ne

/-!
### H1.17 Step D — ExternalLegs equality

External legs don't involve multiset subtraction — they're just
mapped through twice. So the argument is just `map_map` +
`map_congr` with the ExternalLeg version of `retarget_comp_eq`.
-/
theorem contract_chain_externalLegs
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId)
    (hstar_notG : star ∉ G.vertices)
    (hG : G.WellFormed) :
    ((contractRestrict hle star).contractWith star).externalLegs
      = (γ₂.contractWith star).externalLegs := by
  set r₁ := ExternalLeg.retarget γ₁.vertices star with hr₁
  set r₂ := ExternalLeg.retarget
      ((γ₂.vertices \ γ₁.vertices) ∪ {star}) star with hr₂
  set r₂' := ExternalLeg.retarget γ₂.vertices star with hr₂'
  -- Unfold the outer contractWith's externalLegs:
  --   ((contractRestrict hle star).contractWith star).externalLegs
  --   = (γ₁.contractWith star).externalLegs.map r₂
  --   = (G.externalLegs.map r₁).map r₂  -- ambient of contractRestrict is γ₁.contractWith star
  -- On the RHS:
  --   (γ₂.contractWith star).externalLegs = G.externalLegs.map r₂'
  rw [contractWith_externalLegs, contractWith_externalLegs]
  rw [Multiset.map_map]
  -- LHS is now G.externalLegs.map (r₂ ∘ r₁); RHS is G.externalLegs.map r₂'
  refine Multiset.map_congr rfl ?_
  intro ℓ hℓ
  have hsupp : ℓ.SupportedOn G.vertices := hG.2 ℓ hℓ
  have hatt : ℓ.attachedTo ∈ G.vertices := hsupp
  have hℓ_ne : ℓ.attachedTo ≠ star := fun h => hstar_notG (h ▸ hatt)
  show r₂ (r₁ ℓ) = r₂' ℓ
  simp only [hr₂, hr₁, hr₂']
  exact ExternalLeg.retarget_comp_eq hle.1 ℓ hℓ_ne

/-!
### H1.17 — `contract_chain`

**The Connes–Kreimer nesting identity.** Given nested subgraphs
`γ₁ ≤ γ₂ ≤ G` and a common fresh vertex `star ∉ G.vertices`, the
two-step contraction equals the one-step contraction as FeynmanGraph:

```
(contractRestrict hle star).contractWith star = γ₂.contractWith star
```

(the `star` is shared between both contractions, which is why we
introduced the `contractWith` primitive parameterized by the star
vertex — see the design discussion in `contractWith`.)

This is the first irreducible theorem [ConKr] of the Connes–Kreimer
construction. It drives coassociativity (H5.8) of the coproduct by
matching the two-step subgraph sums term-by-term.

The proof reduces to three component equalities (Steps B, C, D):
vertex set, internal-edge multiset, external-leg multiset. Each
component is proven independently; the structure-level equality then
follows from `FeynmanGraph.mk.injEq`.
-/
theorem contract_chain
    {γ₁ γ₂ : FeynmanSubgraph G} (hle : γ₁ ≤ γ₂) (star : VertexId)
    (hstar_notG : star ∉ G.vertices)
    (hG : G.WellFormed) :
    (contractRestrict hle star).contractWith star = γ₂.contractWith star := by
  -- Reduce to equality on the three FeynmanGraph fields.
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- Vertices: follows from contract_chain_vertices.
    -- LHS: ((contractRestrict hle star).contractWith star).vertices
    --    = ((γ₁.contractWith star).vertices \ (contractRestrict hle star).vertices) ∪ {star}
    rw [contractWith_vertices]
    exact contract_chain_vertices hle star hstar_notG
  · -- Internal edges: Step C.
    exact contract_chain_internalEdges hle star hstar_notG hG
  · -- External legs: Step D.
    exact contract_chain_externalLegs hle star hstar_notG hG

end FeynmanSubgraph

/-!
## 2-D: Divergence measure (abstract interface)

A `DivergenceMeasure` on `G` assigns to every subgraph of `G` an `Int`-valued
*superficial degree of divergence*. In the standard QFT formula this is

  ω(γ) = d · L(γ) − 2 · I_B(γ) − I_F(γ) + ∑_v δ_v

where `d` is the spacetime dimension, `L(γ)` the loop number, `I_{B,F}` the
numbers of bosonic and fermionic internal propagators, and `δ_v` the vertex
dimensions determined by the coupling structure. Concrete instances fix
those weights; the interface here commits to none of them.

A subgraph is *divergent* when its superficial degree of divergence is
nonnegative.
-/

/--
An abstract superficial-divergence measure on subgraphs of a fixed
`FeynmanGraph`. Concrete instances — e.g. the MSSM one-loop measure at `d = 4`
— are supplied separately, either at the representation layer or, for
empirical-only inputs, under `Axioms/`.
-/
class DivergenceMeasure (G : FeynmanGraph) where
  /-- Superficial degree of divergence of a subgraph, as an integer. -/
  degree : FeynmanSubgraph G → Int

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- Superficial degree of divergence of `γ` under the ambient measure. -/
def divergenceDegree [DivergenceMeasure G] (γ : FeynmanSubgraph G) : Int :=
  DivergenceMeasure.degree γ

/--
A subgraph is *divergent* if its superficial degree of divergence is
nonnegative. This is the standard Weinberg-type criterion.
-/
def IsDivergent [DivergenceMeasure G] (γ : FeynmanSubgraph G) : Prop :=
  0 ≤ γ.divergenceDegree

@[simp] theorem isDivergent_def [DivergenceMeasure G] (γ : FeynmanSubgraph G) :
    γ.IsDivergent ↔ 0 ≤ γ.divergenceDegree := Iff.rfl

/--
A subgraph is *logarithmically divergent* if its superficial degree of
divergence is exactly zero.
-/
def IsLogDivergent [DivergenceMeasure G] (γ : FeynmanSubgraph G) : Prop :=
  γ.divergenceDegree = 0

/--
A subgraph is *power-counting convergent* if its superficial degree of
divergence is negative.
-/
def IsConvergent [DivergenceMeasure G] (γ : FeynmanSubgraph G) : Prop :=
  γ.divergenceDegree < 0

theorem not_isDivergent_iff_isConvergent
    [DivergenceMeasure G] (γ : FeynmanSubgraph G) :
    ¬ γ.IsDivergent ↔ γ.IsConvergent := by
  unfold IsDivergent IsConvergent
  omega

/--
H0.9 — **Connected-divergent subgraph**: the index predicate of the
Connes–Kreimer coproduct sum. A subgraph `γ` is connected-divergent
when it is (support-)connected, 1PI, and superficially divergent.

The 1PI clause is what restricts the sum to physically irreducible
divergent subdiagrams; the `IsConnected` clause is redundant given
`IsOnePI` (1PI ⇒ connected), but is retained separately so that later
lemmas that only need connectivity can use it directly without
unpacking 1PI.
-/
def IsConnectedDivergent [DivergenceMeasure G] (γ : FeynmanSubgraph G) : Prop :=
  γ.IsConnected ∧ γ.IsOnePI ∧ γ.IsDivergent

@[simp] theorem isConnectedDivergent_def [DivergenceMeasure G]
    (γ : FeynmanSubgraph G) :
    γ.IsConnectedDivergent ↔
      γ.IsConnected ∧ γ.IsOnePI ∧ γ.IsDivergent := Iff.rfl

theorem IsConnectedDivergent.isConnected [DivergenceMeasure G]
    {γ : FeynmanSubgraph G} (h : γ.IsConnectedDivergent) :
    γ.IsConnected := h.1

theorem IsConnectedDivergent.isOnePI [DivergenceMeasure G]
    {γ : FeynmanSubgraph G} (h : γ.IsConnectedDivergent) :
    γ.IsOnePI := h.2.1

theorem IsConnectedDivergent.isDivergent [DivergenceMeasure G]
    {γ : FeynmanSubgraph G} (h : γ.IsConnectedDivergent) :
    γ.IsDivergent := h.2.2

/--
H0.10 — **Decidability of `IsConnectedDivergent`**.

Support connectedness is a `∀∀` over natural-number vertices; the
classical `Decidable` instance suffices because
`IsConnectedDivergent` is only used as a propositional index set for
the Connes–Kreimer sum. Computability of the membership check is not
required at this layer and can be supplied later by a BFS-style
refinement.

The classical axioms here (`Classical.choice`, `propext`) are the
same ones already used by Mathlib's core, so this does not introduce
any project-specific axiom.
-/
noncomputable instance decidable_isConnectedDivergent [DivergenceMeasure G]
    (γ : FeynmanSubgraph G) : Decidable γ.IsConnectedDivergent :=
  Classical.propDecidable _

/-!
### Nesting and disjointness of subgraphs

Two subgraphs of `G` are *vertex-disjoint* if their vertex Finsets are
disjoint. Under the Version 1 labeled model, where `toSimpleGraph` already
handles self-loop removal, vertex-disjointness implies internal-edge-
disjointness as well.

Two subgraphs are *nested* if one is contained in the other under the
pointwise `≤` order.

Zimmermann's forest condition requires that any two subgraphs in the forest
are either nested or vertex-disjoint.
-/

/-- Vertex-disjointness: the two subgraphs share no vertex. -/
def Disjoint (γ₁ γ₂ : FeynmanSubgraph G) : Prop :=
  _root_.Disjoint γ₁.vertices γ₂.vertices

/-- Nestedness: one subgraph contains the other under pointwise `≤`. -/
def Nested (γ₁ γ₂ : FeynmanSubgraph G) : Prop :=
  γ₁ ≤ γ₂ ∨ γ₂ ≤ γ₁

theorem Nested.symm {γ₁ γ₂ : FeynmanSubgraph G} (h : γ₁.Nested γ₂) :
    γ₂.Nested γ₁ :=
  Or.symm h

theorem Disjoint.symm {γ₁ γ₂ : FeynmanSubgraph G}
    (h : γ₁.Disjoint γ₂) : γ₂.Disjoint γ₁ :=
  _root_.Disjoint.symm h

/--
Zimmermann's pairwise compatibility: any two subgraphs are nested or
vertex-disjoint.
-/
def NestedOrDisjoint (γ₁ γ₂ : FeynmanSubgraph G) : Prop :=
  γ₁.Nested γ₂ ∨ γ₁.Disjoint γ₂

theorem NestedOrDisjoint.symm {γ₁ γ₂ : FeynmanSubgraph G}
    (h : γ₁.NestedOrDisjoint γ₂) : γ₂.NestedOrDisjoint γ₁ := by
  rcases h with hN | hD
  · exact Or.inl hN.symm
  · exact Or.inr hD.symm

end FeynmanSubgraph

/-!
## 2-E: Forests

A *Zimmermann forest* of `G` is a finite set of divergent subgraphs that
are pairwise nested or vertex-disjoint.
-/

/--
A Zimmermann forest of `G` (under a given `DivergenceMeasure`).

Fields:
* `elements`       — the subgraphs in the forest,
* `divergent`      — every element is superficially divergent,
* `nestedOrDisjoint` — any two distinct elements are nested or vertex-disjoint.
-/
structure Forest (G : FeynmanGraph) [DivergenceMeasure G] where
  elements : Finset (FeynmanSubgraph G)
  divergent : ∀ γ ∈ elements, γ.IsDivergent
  nestedOrDisjoint :
    ∀ ⦃γ₁⦄, γ₁ ∈ elements → ∀ ⦃γ₂⦄, γ₂ ∈ elements →
      γ₁ ≠ γ₂ → γ₁.NestedOrDisjoint γ₂

namespace Forest

variable {G : FeynmanGraph} [DivergenceMeasure G]

/-- The empty forest is always a valid forest. -/
def empty (G : FeynmanGraph) [DivergenceMeasure G] : Forest G where
  elements := ∅
  divergent := by intro γ hγ; simp at hγ
  nestedOrDisjoint := by intro γ₁ h₁ _ _ _; simp at h₁

/-- Number of subgraphs in the forest. -/
def size (F : Forest G) : Nat := F.elements.card

@[simp] theorem empty_size : (empty G).size = 0 := by
  simp [size, empty]

/--
If a subgraph lies in the forest, it is superficially divergent.
(Direct restatement of the `divergent` field, provided as a lemma
for convenient use.)
-/
theorem isDivergent_of_mem (F : Forest G) {γ : FeynmanSubgraph G}
    (hγ : γ ∈ F.elements) : γ.IsDivergent :=
  F.divergent γ hγ

/-- The forest consisting of one divergent subgraph. -/
def singleton (γ : FeynmanSubgraph G) (hγ : γ.IsDivergent) : Forest G where
  elements := {γ}
  divergent := by
    intro γ' hγ'
    rw [Finset.mem_singleton] at hγ'
    exact hγ' ▸ hγ
  nestedOrDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    rw [Finset.mem_singleton] at h₁ h₂
    exact (hne (h₁.trans h₂.symm)).elim

@[simp] theorem singleton_elements (γ : FeynmanSubgraph G)
    (hγ : γ.IsDivergent) :
    (singleton γ hγ).elements = {γ} := rfl

@[simp] theorem mem_singleton_elements {γ γ' : FeynmanSubgraph G}
    {hγ : γ.IsDivergent} :
    γ' ∈ (singleton γ hγ).elements ↔ γ' = γ := by
  simp [singleton]

/--
Two forests are equal when their underlying element Finsets are equal.
The divergence/compatibility fields are proof-valued and collapse under
proof irrelevance.
-/
theorem ext {F₁ F₂ : Forest G}
    (h : F₁.elements = F₂.elements) : F₁ = F₂ := by
  cases F₁
  cases F₂
  simp_all

instance (G : FeynmanGraph) [DivergenceMeasure G] : DecidableEq (Forest G) := by
  intro F₁ F₂
  by_cases h : F₁.elements = F₂.elements
  · exact isTrue (Forest.ext h)
  · refine isFalse ?_
    intro hEq
    apply h
    rw [hEq]

/--
Insert a new subgraph `γ` into the forest `F`, given proofs that
`γ` is divergent and compatible with every current element.
If `γ` is already in `F`, the result is `F` itself (`Finset.insert`
is idempotent on members).
-/
def insert (F : Forest G) (γ : FeynmanSubgraph G)
    (hγ : γ.IsDivergent)
    (hcompat : ∀ γ' ∈ F.elements, γ' ≠ γ → γ'.NestedOrDisjoint γ) :
    Forest G where
  elements := Insert.insert γ F.elements
  divergent := by
    intro γ' hγ'
    rcases Finset.mem_insert.mp hγ' with h | h
    · exact h ▸ hγ
    · exact F.divergent γ' h
  nestedOrDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    rcases Finset.mem_insert.mp h₁ with h₁' | h₁'
    · rcases Finset.mem_insert.mp h₂ with h₂' | h₂'
      · exact (hne (h₁'.trans h₂'.symm)).elim
      · -- γ₁ = γ, γ₂ ∈ F
        have hne' : γ₂ ≠ γ₁ := fun h => hne h.symm
        have hcompat' := hcompat γ₂ h₂' (h₁' ▸ hne')
        rw [h₁']
        exact hcompat'.symm
    · rcases Finset.mem_insert.mp h₂ with h₂' | h₂'
      · -- γ₁ ∈ F, γ₂ = γ
        have hcompat' := hcompat γ₁ h₁' (h₂' ▸ hne)
        rw [h₂']
        exact hcompat'
      · exact F.nestedOrDisjoint h₁' h₂' hne

@[simp] theorem insert_elements (F : Forest G) (γ : FeynmanSubgraph G)
    (hγ : γ.IsDivergent)
    (hcompat : ∀ γ' ∈ F.elements, γ' ≠ γ → γ'.NestedOrDisjoint γ) :
    (F.insert γ hγ hcompat).elements = Insert.insert γ F.elements := by
  rfl

/--
Remove a subgraph from the forest. No compatibility check is needed:
a subset of a forest is still a forest.
-/
def erase (F : Forest G) (γ : FeynmanSubgraph G) : Forest G where
  elements := F.elements.erase γ
  divergent := by
    intro γ' hγ'
    exact F.divergent γ' (Finset.mem_of_mem_erase hγ')
  nestedOrDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    exact F.nestedOrDisjoint
      (Finset.mem_of_mem_erase h₁)
      (Finset.mem_of_mem_erase h₂) hne

@[simp] theorem erase_elements (F : Forest G) (γ : FeynmanSubgraph G) :
    (F.erase γ).elements = F.elements.erase γ := by
  rfl

/-!
### Forest ordering and maximal forests

Forests on the same `G` are ordered by inclusion of their element Finsets.
This lets us talk about *maximal forests*: forests that cannot be enlarged
by any single insertion.
-/

/-- Pointwise inclusion of forests. -/
instance : LE (Forest G) where
  le F₁ F₂ := F₁.elements ⊆ F₂.elements

theorem le_def' {F₁ F₂ : Forest G} :
    F₁ ≤ F₂ ↔ F₁.elements ⊆ F₂.elements := Iff.rfl

theorem le_refl'' (F : Forest G) : F ≤ F :=
  Finset.Subset.refl _

theorem le_trans'' {F₁ F₂ F₃ : Forest G} (h₁₂ : F₁ ≤ F₂) (h₂₃ : F₂ ≤ F₃) :
    F₁ ≤ F₃ :=
  Finset.Subset.trans h₁₂ h₂₃

/-- `Forest.empty G ≤ F` for every forest `F`. -/
theorem empty_le (F : Forest G) : Forest.empty G ≤ F := by
  rw [le_def']
  simp [empty]

/--
A forest is *maximal* if no divergent subgraph can be added while
preserving the Zimmermann compatibility condition.
-/
def IsMaximal (F : Forest G) : Prop :=
  ∀ γ : FeynmanSubgraph G, γ.IsDivergent →
    (∀ γ' ∈ F.elements, γ' ≠ γ → γ'.NestedOrDisjoint γ) →
    γ ∈ F.elements

/-!
### H0.12 — Connected-divergent forests

A *connected-divergent forest* is a forest all of whose elements are
`IsConnectedDivergent` (connected, 1PI, and superficially divergent).
This is the index set of forests used by the Connes–Kreimer coproduct.

We provide both a predicate form (`IsConnectedDivergent`) and a
restriction operation (`connectedDivergent`) that filters any forest
down to its connected-divergent elements.
-/

/--
H0.12 — Predicate: every element of the forest `F` is connected,
1PI, and superficially divergent.
-/
def IsConnectedDivergent (F : Forest G) : Prop :=
  ∀ γ ∈ F.elements, γ.IsConnectedDivergent

/-- Predicate: all distinct components of a forest are vertex-disjoint. -/
def IsPairwiseDisjoint (F : Forest G) : Prop :=
  ∀ ⦃γ₁⦄, γ₁ ∈ F.elements → ∀ ⦃γ₂⦄, γ₂ ∈ F.elements →
    γ₁ ≠ γ₂ → γ₁.Disjoint γ₂

theorem empty_isPairwiseDisjoint :
    (Forest.empty G).IsPairwiseDisjoint := by
  intro γ hγ
  simp [Forest.empty] at hγ

theorem singleton_isPairwiseDisjoint
    (γ : FeynmanSubgraph G) (hγ : γ.IsDivergent) :
    (singleton γ hγ).IsPairwiseDisjoint := by
  intro γ₁ hγ₁ γ₂ hγ₂ hne
  rw [mem_singleton_elements] at hγ₁ hγ₂
  exact (hne (hγ₁.trans hγ₂.symm)).elim

/-- In a pairwise-disjoint forest, a vertex belongs to at most one component. -/
theorem IsPairwiseDisjoint.eq_of_mem_vertices
    {F : Forest G} (hF : F.IsPairwiseDisjoint)
    {γ₁ γ₂ : FeynmanSubgraph G}
    (hγ₁ : γ₁ ∈ F.elements) (hγ₂ : γ₂ ∈ F.elements)
    {v : VertexId} (hv₁ : v ∈ γ₁.vertices) (hv₂ : v ∈ γ₂.vertices) :
    γ₁ = γ₂ := by
  by_contra hne
  have hdisjoint : γ₁.Disjoint γ₂ := hF hγ₁ hγ₂ hne
  exact (Finset.disjoint_left.mp hdisjoint hv₁) hv₂

/-- Predicate on a raw finite set of subgraphs saying it carries the data
needed to build a Zimmermann forest. -/
def IsElements (s : Finset (FeynmanSubgraph G)) : Prop :=
  (∀ γ ∈ s, γ.IsDivergent) ∧
    ∀ ⦃γ₁⦄, γ₁ ∈ s → ∀ ⦃γ₂⦄, γ₂ ∈ s →
      γ₁ ≠ γ₂ → γ₁.NestedOrDisjoint γ₂

/-- Predicate on a raw finite set of subgraphs saying it carries a
connected-divergent Zimmermann forest. -/
def IsConnectedDivergentElements (s : Finset (FeynmanSubgraph G)) : Prop :=
  (∀ γ ∈ s, γ.IsConnectedDivergent) ∧
    ∀ ⦃γ₁⦄, γ₁ ∈ s → ∀ ⦃γ₂⦄, γ₂ ∈ s →
      γ₁ ≠ γ₂ → γ₁.NestedOrDisjoint γ₂

theorem IsConnectedDivergentElements.isElements
    {s : Finset (FeynmanSubgraph G)}
    (h : IsConnectedDivergentElements (G := G) s) :
    IsElements (G := G) s := by
  refine ⟨?_, h.2⟩
  intro γ hγ
  exact (h.1 γ hγ).isDivergent

/-- Build a forest from a raw finite set satisfying the forest predicate. -/
def ofElements (s : Finset (FeynmanSubgraph G))
    (h : IsElements (G := G) s) : Forest G where
  elements := s
  divergent := h.1
  nestedOrDisjoint := h.2

@[simp] theorem ofElements_elements
    (s : Finset (FeynmanSubgraph G)) (h : IsElements (G := G) s) :
    (ofElements (G := G) s h).elements = s := rfl

/-- Build a forest from a raw connected-divergent finite set. -/
def ofConnectedDivergentElements (s : Finset (FeynmanSubgraph G))
    (h : IsConnectedDivergentElements (G := G) s) : Forest G :=
  ofElements s h.isElements

@[simp] theorem ofConnectedDivergentElements_elements
    (s : Finset (FeynmanSubgraph G))
    (h : IsConnectedDivergentElements (G := G) s) :
    (ofConnectedDivergentElements (G := G) s h).elements = s := rfl

theorem ofConnectedDivergentElements_isConnectedDivergent
    (s : Finset (FeynmanSubgraph G))
    (h : IsConnectedDivergentElements (G := G) s) :
    (ofConnectedDivergentElements (G := G) s h).IsConnectedDivergent := by
  intro γ hγ
  exact h.1 γ hγ

/--
H0.12 — Restrict a forest to its connected-divergent elements. The
result is a forest because filtering preserves pairwise
nested-or-disjoint compatibility (inherited from `F`).
-/
noncomputable def connectedDivergent (F : Forest G) : Forest G where
  elements := F.elements.filter (fun γ => γ.IsConnectedDivergent)
  divergent := by
    intro γ hγ
    have hmem := Finset.mem_filter.mp hγ
    exact F.divergent γ hmem.1
  nestedOrDisjoint := by
    intro γ₁ h₁ γ₂ h₂ hne
    have hmem₁ := (Finset.mem_filter.mp h₁).1
    have hmem₂ := (Finset.mem_filter.mp h₂).1
    exact F.nestedOrDisjoint hmem₁ hmem₂ hne

@[simp] theorem connectedDivergent_elements (F : Forest G) :
    F.connectedDivergent.elements =
      F.elements.filter (fun γ => γ.IsConnectedDivergent) := rfl

/--
The restricted forest satisfies `IsConnectedDivergent` by construction.
-/
theorem connectedDivergent_isConnectedDivergent (F : Forest G) :
    F.connectedDivergent.IsConnectedDivergent := by
  intro γ hγ
  exact (Finset.mem_filter.mp hγ).2

/-- A singleton forest is connected-divergent when its element is. -/
theorem singleton_isConnectedDivergent
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ.isDivergent).IsConnectedDivergent := by
  intro γ' hγ'
  rw [mem_singleton_elements] at hγ'
  exact hγ' ▸ hγ

/--
The restricted forest is a sub-forest of the original.
-/
theorem connectedDivergent_le (F : Forest G) :
    F.connectedDivergent ≤ F := by
  rw [le_def']
  exact Finset.filter_subset _ _

/-- Finite index of all connected-divergent forests, built by filtering
the powerset of the finite subgraph universe. This is the finite carrier
needed before replacing the conservative singleton admissible index by a
full forest index. -/
noncomputable def connectedDivergentIndex
    (G : FeynmanGraph) [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (Forest G) := by
  classical
  let raw : Finset (Finset (FeynmanSubgraph G)) :=
    (Finset.univ : Finset (FeynmanSubgraph G)).powerset.filter
      (fun s => IsConnectedDivergentElements (G := G) s)
  exact raw.attach.image fun s =>
    ofConnectedDivergentElements (G := G) s.1
      ((Finset.mem_filter.mp s.2).2)

/-- Every forest in the finite connected-divergent index is
connected-divergent. -/
theorem mem_connectedDivergentIndex_isConnectedDivergent
    (G : FeynmanGraph) [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    {F : Forest G} (hF : F ∈ connectedDivergentIndex G) :
    F.IsConnectedDivergent := by
  classical
  unfold connectedDivergentIndex at hF
  rcases Finset.mem_image.mp hF with ⟨s, _hs, hFs⟩
  rw [← hFs]
  exact ofConnectedDivergentElements_isConnectedDivergent s.1
    ((Finset.mem_filter.mp s.2).2)

/-- Every connected-divergent forest appears in the finite index. -/
theorem mem_connectedDivergentIndex_of_isConnectedDivergent
    (G : FeynmanGraph) [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (F : Forest G) (hF : F.IsConnectedDivergent) :
    F ∈ connectedDivergentIndex G := by
  classical
  unfold connectedDivergentIndex
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨F.elements, ?_⟩, by simp, ?_⟩
  · rw [Finset.mem_filter]
    refine ⟨by simp, ?_⟩
    refine ⟨hF, ?_⟩
    intro γ₁ hγ₁ γ₂ hγ₂ hne
    exact F.nestedOrDisjoint hγ₁ hγ₂ hne
  · exact Forest.ext rfl

end Forest

/-!
### Minimal admissible subgraph carrier

For the CK coproduct redesign we first use the smallest useful carrier:
a forest all of whose components are connected-divergent. Later passes can
add properness, disjoint-component union data, and product-lift API without
changing this wrapper.
-/

/-- An admissible subgraph is represented by a connected-divergent forest. -/
structure AdmissibleSubgraph (G : FeynmanGraph) [DivergenceMeasure G] where
  forest : Forest G
  isConnectedDivergent : forest.IsConnectedDivergent

namespace AdmissibleSubgraph

variable {G : FeynmanGraph} [DivergenceMeasure G]

/-- Carrier elements of an admissible subgraph. -/
def elements (A : AdmissibleSubgraph G) : Finset (FeynmanSubgraph G) :=
  A.forest.elements

@[simp] theorem elements_def (A : AdmissibleSubgraph G) :
    A.elements = A.forest.elements := rfl

/-- Vertex carrier of an admissible subgraph, obtained as the union of the
vertex carriers of its connected-divergent components. -/
def vertices (A : AdmissibleSubgraph G) : Finset VertexId :=
  A.elements.biUnion fun γ => γ.vertices

@[simp] theorem mem_vertices {A : AdmissibleSubgraph G} {v : VertexId} :
    v ∈ A.vertices ↔ ∃ γ ∈ A.elements, v ∈ γ.vertices := by
  simp [vertices]

theorem vertices_subset (A : AdmissibleSubgraph G) :
    A.vertices ⊆ G.vertices := by
  intro v hv
  rcases mem_vertices.mp hv with ⟨γ, _hγA, hvγ⟩
  exact γ.vertices_subset hvγ

/-- Multiset of component-internal edges to remove under admissible
contraction. For disjoint admissible carriers this is the disjoint sum of the
component internal-edge multisets; the proof that it embeds in
`G.internalEdges` is intentionally a later small pass. -/
def internalEdges (A : AdmissibleSubgraph G) : Multiset FeynmanEdge :=
  ∑ γ ∈ A.elements, γ.internalEdges

theorem mem_internalEdges {A : AdmissibleSubgraph G} {e : FeynmanEdge} :
    e ∈ A.internalEdges ↔ ∃ γ ∈ A.elements, e ∈ γ.internalEdges := by
  classical
  unfold internalEdges
  induction A.elements using Finset.induction_on with
  | empty =>
      simp
  | insert γ s hγs ih =>
      simp [Finset.sum_insert, hγs, ih, Multiset.mem_add]

/-- Edges of the ambient graph left after deleting the component-internal
edges of an admissible subgraph. -/
def complementEdges (A : AdmissibleSubgraph G) : Multiset FeynmanEdge :=
  G.internalEdges - A.internalEdges

theorem mem_ambientInternalEdges_of_mem_complementEdges
    (A : AdmissibleSubgraph G) {e : FeynmanEdge}
    (he : e ∈ A.complementEdges) :
    e ∈ G.internalEdges :=
  Multiset.mem_of_le (Multiset.sub_le_self _ _) he

theorem count_lt_of_mem_complementEdges
    (A : AdmissibleSubgraph G) {e : FeynmanEdge}
    (he : e ∈ A.complementEdges) :
    Multiset.count e A.internalEdges < Multiset.count e G.internalEdges := by
  unfold complementEdges at he
  rw [Multiset.mem_sub] at he
  exact he

theorem complementEdges_erase
    (A : AdmissibleSubgraph G) (e : FeynmanEdge) :
    A.complementEdges.erase e =
      G.internalEdges.erase e - A.internalEdges := by
  unfold complementEdges
  refine Multiset.ext.mpr (fun x => ?_)
  by_cases hxe : x = e
  · subst hxe
    rw [Multiset.count_erase_self, Multiset.count_sub,
      Multiset.count_sub, Multiset.count_erase_self]
    omega
  · rw [Multiset.count_erase_of_ne hxe, Multiset.count_sub,
      Multiset.count_sub, Multiset.count_erase_of_ne hxe]

/-- Pick a component containing a vertex of the admissible subgraph. This is a
choice function over the finite carrier; uniqueness is supplied separately
under `IsPairwiseDisjoint`. -/
noncomputable def componentAt (A : AdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) : FeynmanSubgraph G :=
  Classical.choose (mem_vertices.mp hv)

theorem componentAt_mem (A : AdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    A.componentAt hv ∈ A.elements :=
  (Classical.choose_spec (mem_vertices.mp hv)).1

theorem componentAt_vertex_mem (A : AdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    v ∈ (A.componentAt hv).vertices :=
  (Classical.choose_spec (mem_vertices.mp hv)).2

/-- Optional component lookup for a vertex. It returns `none` outside the
admissible vertex carrier and the chosen containing component inside it. -/
noncomputable def componentAt? (A : AdmissibleSubgraph G)
    (v : VertexId) : Option (FeynmanSubgraph G) :=
  if hv : v ∈ A.vertices then some (A.componentAt hv) else none

@[simp] theorem componentAt?_of_not_mem (A : AdmissibleSubgraph G)
    {v : VertexId} (hv : v ∉ A.vertices) :
    A.componentAt? v = none := by
  unfold componentAt?
  rw [dif_neg hv]

theorem componentAt?_of_mem (A : AdmissibleSubgraph G)
    {v : VertexId} (hv : v ∈ A.vertices) :
    A.componentAt? v = some (A.componentAt hv) := by
  unfold componentAt?
  rw [dif_pos hv]

theorem componentAt?_eq_some_mem
    {A : AdmissibleSubgraph G} {v : VertexId} {γ : FeynmanSubgraph G}
    (h : A.componentAt? v = some γ) :
    γ ∈ A.elements := by
  unfold componentAt? at h
  split_ifs at h with hv
  · injection h with hγ
    rw [← hγ]
    exact A.componentAt_mem hv

theorem componentAt?_eq_some_vertex_mem
    {A : AdmissibleSubgraph G} {v : VertexId} {γ : FeynmanSubgraph G}
    (h : A.componentAt? v = some γ) :
    v ∈ γ.vertices := by
  unfold componentAt? at h
  split_ifs at h with hv
  · injection h with hγ
    rw [← hγ]
    exact A.componentAt_vertex_mem hv

/-- Equality of admissible subgraphs is equality of their forest carriers. -/
theorem ext {A B : AdmissibleSubgraph G} (h : A.forest = B.forest) : A = B := by
  cases A
  cases B
  simp_all

instance (G : FeynmanGraph) [DivergenceMeasure G] :
    DecidableEq (AdmissibleSubgraph G) := by
  intro A B
  by_cases h : A.forest = B.forest
  · exact isTrue (ext h)
  · refine isFalse ?_
    intro hAB
    apply h
    rw [hAB]

/-- The empty admissible subgraph. -/
def empty (G : FeynmanGraph) [DivergenceMeasure G] : AdmissibleSubgraph G where
  forest := Forest.empty G
  isConnectedDivergent := by
    intro γ hγ
    simp [Forest.empty] at hγ

@[simp] theorem empty_forest :
    (empty G).forest = Forest.empty G := rfl

@[simp] theorem empty_elements :
    (empty G).elements = ∅ := rfl

@[simp] theorem empty_vertices :
    (empty G).vertices = ∅ := by
  rw [vertices, empty_elements]
  simp

@[simp] theorem empty_internalEdges :
    (empty G).internalEdges = 0 := by
  rw [internalEdges, empty_elements]
  simp

@[simp] theorem empty_complementEdges :
    (empty G).complementEdges = G.internalEdges := by
  rw [complementEdges, empty_internalEdges]
  simp

/-- Embed a single connected-divergent subgraph as an admissible subgraph. -/
def singleton (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    AdmissibleSubgraph G where
  forest := Forest.singleton γ hγ.isDivergent
  isConnectedDivergent := Forest.singleton_isConnectedDivergent γ hγ

@[simp] theorem singleton_forest (γ : FeynmanSubgraph G)
    (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).forest = Forest.singleton γ hγ.isDivergent := rfl

@[simp] theorem singleton_elements (γ : FeynmanSubgraph G)
    (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).elements = {γ} := rfl

@[simp] theorem singleton_vertices (γ : FeynmanSubgraph G)
    (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).vertices = γ.vertices := by
  rw [vertices, singleton_elements]
  simp

@[simp] theorem singleton_internalEdges (γ : FeynmanSubgraph G)
    (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).internalEdges = γ.internalEdges := by
  rw [internalEdges, singleton_elements]
  simp

@[simp] theorem singleton_complementEdges (γ : FeynmanSubgraph G)
    (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).complementEdges = γ.complementEdges := by
  rw [complementEdges, singleton_internalEdges]
  rfl

@[simp] theorem mem_singleton_elements {γ γ' : FeynmanSubgraph G}
    {hγ : γ.IsConnectedDivergent} :
    γ' ∈ (singleton γ hγ).elements ↔ γ' = γ := by
  simp [singleton, elements]

/-- Singleton admissible subgraphs remember their unique component. -/
theorem singleton_injective {γ₁ γ₂ : FeynmanSubgraph G}
    {hγ₁ : γ₁.IsConnectedDivergent} {hγ₂ : γ₂.IsConnectedDivergent}
    (h : singleton γ₁ hγ₁ = singleton γ₂ hγ₂) :
    γ₁ = γ₂ := by
  have hmem : γ₁ ∈ (singleton γ₂ hγ₂).elements := by
    rw [← h]
    simp
  exact mem_singleton_elements.mp hmem

/-- Every component of an admissible subgraph is connected-divergent. -/
theorem isConnectedDivergent_of_mem (A : AdmissibleSubgraph G)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    γ.IsConnectedDivergent :=
  A.isConnectedDivergent γ hγ

/-- Every component of an admissible subgraph is divergent. -/
theorem isDivergent_of_mem (A : AdmissibleSubgraph G)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    γ.IsDivergent :=
  (A.isConnectedDivergent_of_mem hγ).isDivergent

/-- Build an admissible subgraph from a connected-divergent forest. -/
def ofForest (F : Forest G) (hF : F.IsConnectedDivergent) :
    AdmissibleSubgraph G where
  forest := F
  isConnectedDivergent := hF

/-- Predicate: all distinct connected-divergent components are
vertex-disjoint. This is the finite carrier condition for admissible
subgraphs that are disjoint unions of connected subdivergences. -/
def IsPairwiseDisjoint (A : AdmissibleSubgraph G) : Prop :=
  A.forest.IsPairwiseDisjoint

/-- Predicate: every connected-divergent component of an admissible subgraph
has a nonempty vertex carrier. This is the precise hypothesis needed to lift
the star vertices of a forest contraction back to preimage vertices in the
ambient graph. -/
def HasNonemptyComponents (A : AdmissibleSubgraph G) : Prop :=
  ∀ γ ∈ A.elements, γ.IsNonempty

/-- Predicate: every component of an admissible subgraph has at least one
internal edge.  This is the componentwise version of the CK properness
condition for forest summands. -/
def HasPositiveInternalEdgesComponents (A : AdmissibleSubgraph G) : Prop :=
  ∀ γ ∈ A.elements, 0 < γ.internalEdges.card

/-- A singleton admissible subgraph has nonempty components as soon as its
unique component is nonempty. -/
theorem singleton_hasNonemptyComponents {γ : FeynmanSubgraph G}
    {hγ : γ.IsConnectedDivergent} (hγne : γ.IsNonempty) :
    (singleton γ hγ).HasNonemptyComponents := by
  intro γ' hγ'
  rw [mem_singleton_elements] at hγ'
  subst γ'
  exact hγne

/-- A singleton admissible subgraph has positive-edge components as soon as
its unique component has a positive internal-edge count. -/
theorem singleton_hasPositiveInternalEdgesComponents {γ : FeynmanSubgraph G}
    {hγ : γ.IsConnectedDivergent} (hγEdges : 0 < γ.internalEdges.card) :
    (singleton γ hγ).HasPositiveInternalEdgesComponents := by
  intro γ' hγ'
  rw [mem_singleton_elements] at hγ'
  subst γ'
  exact hγEdges

/-- In a disjoint admissible subgraph, the chosen component containing `v`
equals any other component containing `v`. -/
theorem componentAt_eq_of_mem_vertices
    {A : AdmissibleSubgraph G} (hA : A.IsPairwiseDisjoint)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements)
    {v : VertexId} (hv : v ∈ A.vertices) (hvγ : v ∈ γ.vertices) :
    A.componentAt hv = γ := by
  exact hA.eq_of_mem_vertices
    (A.componentAt_mem hv) hγ
    (A.componentAt_vertex_mem hv) hvγ

theorem componentAt?_eq_some_of_mem_vertices
    {A : AdmissibleSubgraph G} (hA : A.IsPairwiseDisjoint)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements)
    {v : VertexId} (hvγ : v ∈ γ.vertices) :
    A.componentAt? v = some γ := by
  have hv : v ∈ A.vertices := by
    rw [mem_vertices]
    exact ⟨γ, hγ, hvγ⟩
  rw [A.componentAt?_of_mem hv]
  rw [A.componentAt_eq_of_mem_vertices hA hγ hv hvγ]

/-- Retarget an ambient vertex through a disjoint admissible subgraph, using a
caller-supplied star vertex for each component. This deliberately postpones
the construction of fresh, pairwise-distinct stars. -/
noncomputable def retargetVertex (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) (v : VertexId) : VertexId :=
  match A.componentAt? v with
  | some γ => starOf γ
  | none => v

@[simp] theorem retargetVertex_of_not_mem
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    {v : VertexId} (hv : v ∉ A.vertices) :
    A.retargetVertex starOf v = v := by
  rw [retargetVertex, componentAt?_of_not_mem A hv]

theorem retargetVertex_of_mem_component
    {A : AdmissibleSubgraph G} (hA : A.IsPairwiseDisjoint)
    (starOf : FeynmanSubgraph G → VertexId)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements)
    {v : VertexId} (hvγ : v ∈ γ.vertices) :
    A.retargetVertex starOf v = starOf γ := by
  rw [retargetVertex, componentAt?_eq_some_of_mem_vertices hA hγ hvγ]

/-- Retarget an internal edge through a disjoint admissible subgraph, using a
caller-supplied star vertex for each component. -/
noncomputable def retargetEdge (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) (e : FeynmanEdge) :
    FeynmanEdge where
  source := A.retargetVertex starOf e.source
  target := A.retargetVertex starOf e.target
  sector := e.sector

@[simp] theorem retargetEdge_source
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (e : FeynmanEdge) :
    (A.retargetEdge starOf e).source = A.retargetVertex starOf e.source := rfl

@[simp] theorem retargetEdge_target
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (e : FeynmanEdge) :
    (A.retargetEdge starOf e).target = A.retargetVertex starOf e.target := rfl

@[simp] theorem retargetEdge_sector
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (e : FeynmanEdge) :
    (A.retargetEdge starOf e).sector = e.sector := rfl

/-- Retarget an external leg through a disjoint admissible subgraph, using a
caller-supplied star vertex for each component. -/
noncomputable def retargetExternalLeg (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) (ℓ : ExternalLeg) :
    ExternalLeg where
  attachedTo := A.retargetVertex starOf ℓ.attachedTo
  sector := ℓ.sector

@[simp] theorem retargetExternalLeg_attachedTo
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (ℓ : ExternalLeg) :
    (A.retargetExternalLeg starOf ℓ).attachedTo =
      A.retargetVertex starOf ℓ.attachedTo := rfl

@[simp] theorem retargetExternalLeg_sector
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (ℓ : ExternalLeg) :
    (A.retargetExternalLeg starOf ℓ).sector = ℓ.sector := rfl

/-- Star vertices introduced by an admissible contraction, one for each
component according to the caller-supplied assignment. -/
def starVertices (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) : Finset VertexId :=
  A.elements.image starOf

@[simp] theorem mem_starVertices
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    {v : VertexId} :
    v ∈ A.starVertices starOf ↔ ∃ γ ∈ A.elements, starOf γ = v := by
  simp [starVertices]

/-- A component-star assignment is fresh when every component is sent outside
the ambient vertex set and distinct components receive distinct stars. This is
the small predicate needed before proving graph-theoretic preservation for
forest contraction. -/
def IsFreshStarAssignment (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) : Prop :=
  (∀ γ ∈ A.elements, starOf γ ∉ G.vertices) ∧
    ∀ γ₁ ∈ A.elements, ∀ γ₂ ∈ A.elements,
      starOf γ₁ = starOf γ₂ → γ₁ = γ₂

theorem IsFreshStarAssignment.fresh
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf)
    {γ : FeynmanSubgraph G} (hγ : γ ∈ A.elements) :
    starOf γ ∉ G.vertices :=
  h.1 γ hγ

theorem IsFreshStarAssignment.eq_of_star_eq
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf)
    {γ₁ γ₂ : FeynmanSubgraph G}
    (hγ₁ : γ₁ ∈ A.elements) (hγ₂ : γ₂ ∈ A.elements)
    (hstar : starOf γ₁ = starOf γ₂) :
    γ₁ = γ₂ :=
  h.2 γ₁ hγ₁ γ₂ hγ₂ hstar

theorem IsFreshStarAssignment.star_not_mem_vertices
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf)
    {v : VertexId} (hv : v ∈ A.starVertices starOf) :
    v ∉ G.vertices := by
  rw [mem_starVertices] at hv
  rcases hv with ⟨γ, hγ, rfl⟩
  exact h.fresh hγ

theorem IsFreshStarAssignment.disjoint_vertices_starVertices
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf) :
    Disjoint G.vertices (A.starVertices starOf) := by
  rw [Finset.disjoint_left]
  intro v hvG hvStar
  exact h.star_not_mem_vertices hvStar hvG

theorem IsFreshStarAssignment.disjoint_sdiff_starVertices
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf) :
    Disjoint (G.vertices \ A.vertices) (A.starVertices starOf) := by
  rw [Finset.disjoint_left]
  intro v hvLeft hvStar
  exact h.star_not_mem_vertices hvStar (Finset.mem_sdiff.mp hvLeft).1

theorem IsFreshStarAssignment.card_starVertices
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf) :
    (A.starVertices starOf).card = A.elements.card := by
  rw [starVertices]
  exact Finset.card_image_of_injOn (by
    intro γ hγ γ' hγ' hstar
    exact h.eq_of_star_eq hγ hγ' hstar)

/-- Canonical component-star assignment for a finite admissible subgraph:
place the component stars just above the ambient vertex range, indexed by the
component's position in the finite carrier. -/
noncomputable def componentFreshStar (A : AdmissibleSubgraph G)
    (γ : FeynmanSubgraph G) : VertexId :=
  FeynmanGraph.freshVertex G.vertices + A.elements.toList.idxOf γ

theorem componentFreshStar_not_mem_vertices
    (A : AdmissibleSubgraph G) (γ : FeynmanSubgraph G) :
    A.componentFreshStar γ ∉ G.vertices := by
  intro hmem
  have hlt : A.componentFreshStar γ < FeynmanGraph.freshVertex G.vertices := by
    unfold componentFreshStar
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hmem)
  have hle : FeynmanGraph.freshVertex G.vertices ≤ A.componentFreshStar γ := by
    unfold componentFreshStar
    exact Nat.le_add_right _ _
  exact (Nat.not_lt_of_ge hle) hlt

theorem componentFreshStar_eq_of_eq
    {A : AdmissibleSubgraph G} {γ₁ γ₂ : FeynmanSubgraph G}
    (hγ₁ : γ₁ ∈ A.elements)
    (hstar : A.componentFreshStar γ₁ = A.componentFreshStar γ₂) :
    γ₁ = γ₂ := by
  unfold componentFreshStar at hstar
  have hidx :
      A.elements.toList.idxOf γ₁ = A.elements.toList.idxOf γ₂ :=
    Nat.add_left_cancel hstar
  exact (List.idxOf_inj
    (l := A.elements.toList) (x := γ₁) (y := γ₂)
    (Finset.mem_toList.mpr hγ₁)).mp hidx

theorem componentFreshStar_isFreshStarAssignment
    (A : AdmissibleSubgraph G) :
    A.IsFreshStarAssignment A.componentFreshStar := by
  constructor
  · intro γ _hγ
    exact A.componentFreshStar_not_mem_vertices γ
  · intro γ₁ hγ₁ γ₂ _hγ₂ hstar
    exact componentFreshStar_eq_of_eq hγ₁ hstar

/-- Forest-level contraction skeleton with caller-supplied component stars.
Freshness and pairwise distinctness of those stars are deliberately external
to this definition; later passes can add those hypotheses as needed. -/
noncomputable def contractWithStars (A : AdmissibleSubgraph G)
    (starOf : FeynmanSubgraph G → VertexId) : FeynmanGraph where
  vertices := (G.vertices \ A.vertices) ∪ A.starVertices starOf
  internalEdges := A.complementEdges.map (A.retargetEdge starOf)
  externalLegs := G.externalLegs.map (A.retargetExternalLeg starOf)

@[simp] theorem contractWithStars_vertices
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).vertices =
      (G.vertices \ A.vertices) ∪ A.starVertices starOf := rfl

@[simp] theorem contractWithStars_internalEdges
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).internalEdges =
      A.complementEdges.map (A.retargetEdge starOf) := rfl

theorem mem_contractWithStars_internalEdges
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    {e' : FeynmanEdge} :
    e' ∈ (A.contractWithStars starOf).internalEdges ↔
      ∃ e : FeynmanEdge,
        e ∈ A.complementEdges ∧ A.retargetEdge starOf e = e' := by
  rw [contractWithStars_internalEdges]
  exact Multiset.mem_map

theorem contractWithStars_eraseInternalEdge_internalEdges
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    {e : FeynmanEdge} (he : e ∈ A.complementEdges) :
    ((A.contractWithStars starOf).eraseInternalEdge
      (A.retargetEdge starOf e)).internalEdges =
        (G.internalEdges.erase e - A.internalEdges).map
          (A.retargetEdge starOf) := by
  rw [FeynmanGraph.eraseInternalEdge_internalEdges,
    contractWithStars_internalEdges]
  rw [← A.complementEdges_erase e]
  symm
  exact Multiset.map_erase_of_mem (A.retargetEdge starOf)
    A.complementEdges he

@[simp] theorem contractWithStars_externalLegs
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).externalLegs =
      G.externalLegs.map (A.retargetExternalLeg starOf) := rfl

theorem retargetVertex_mem_contractWithStars_vertices
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    {v : VertexId} (hvG : v ∈ G.vertices) :
    A.retargetVertex starOf v ∈ (A.contractWithStars starOf).vertices := by
  rw [contractWithStars_vertices]
  by_cases hvA : v ∈ A.vertices
  · rw [retargetVertex, componentAt?_of_mem A hvA]
    rw [Finset.mem_union]
    right
    rw [mem_starVertices]
    exact ⟨A.componentAt hvA, A.componentAt_mem hvA, rfl⟩
  · rw [retargetVertex_of_not_mem A starOf hvA]
    rw [Finset.mem_union]
    left
    exact Finset.mem_sdiff.mpr ⟨hvG, hvA⟩

theorem contractWithStars_wellFormed
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId)
    (hGwf : G.WellFormed) :
    (A.contractWithStars starOf).WellFormed := by
  constructor
  · intro e he
    rw [contractWithStars_internalEdges] at he
    rcases Multiset.mem_map.mp he with ⟨e₀, he₀, rfl⟩
    have he₀G : e₀ ∈ G.internalEdges :=
      Multiset.mem_of_le (Multiset.sub_le_self _ _) he₀
    have hsupp := hGwf.1 e₀ he₀G
    constructor
    · exact A.retargetVertex_mem_contractWithStars_vertices starOf hsupp.1
    · exact A.retargetVertex_mem_contractWithStars_vertices starOf hsupp.2
  · intro ℓ hℓ
    rw [contractWithStars_externalLegs] at hℓ
    rcases Multiset.mem_map.mp hℓ with ⟨ℓ₀, hℓ₀, rfl⟩
    have hsupp := hGwf.2 ℓ₀ hℓ₀
    exact A.retargetVertex_mem_contractWithStars_vertices starOf hsupp

theorem contractWithStars_eraseInternalEdge_step_supportReachable
    {A : AdmissibleSubgraph G} (hDisj : A.IsPairwiseDisjoint)
    (starOf : FeynmanSubgraph G → VertexId)
    {e₀ : FeynmanEdge} (he₀ : e₀ ∈ A.complementEdges)
    {u v : VertexId} (h : (G.eraseInternalEdge e₀).SupportAdj u v) :
    ((A.contractWithStars starOf).eraseInternalEdge
      (A.retargetEdge starOf e₀)).SupportReachable
        (A.retargetVertex starOf u) (A.retargetVertex starOf v) := by
  obtain ⟨_hne, e, heG, hend⟩ := h
  rw [FeynmanGraph.eraseInternalEdge_internalEdges] at heG
  by_cases heA : e ∈ A.internalEdges
  · rcases mem_internalEdges.mp heA with ⟨γ, hγ, heγ⟩
    have hsupp : e.SupportedOn γ.vertices := γ.edges_supported e heγ
    simp [FeynmanEdge.SupportedOn] at hsupp
    obtain ⟨hsγ, htγ⟩ := hsupp
    have huγ : u ∈ γ.vertices := by
      rcases hend with ⟨hs, _⟩ | ⟨_, ht⟩
      · exact hs ▸ hsγ
      · exact ht ▸ htγ
    have hvγ : v ∈ γ.vertices := by
      rcases hend with ⟨_, ht⟩ | ⟨hs, _⟩
      · exact ht ▸ htγ
      · exact hs ▸ hsγ
    rw [retargetVertex_of_mem_component hDisj starOf hγ huγ,
      retargetVertex_of_mem_component hDisj starOf hγ hvγ]
    exact FeynmanGraph.SupportReachable.refl _ _
  · have heComplErase : e ∈ G.internalEdges.erase e₀ - A.internalEdges := by
      rw [Multiset.mem_sub]
      have hAcount : A.internalEdges.count e = 0 :=
        Multiset.count_eq_zero.mpr heA
      have hGcount : 0 < (G.internalEdges.erase e₀).count e :=
        Multiset.count_pos.mpr heG
      omega
    have hretarget : A.retargetEdge starOf e ∈
        ((A.contractWithStars starOf).eraseInternalEdge
          (A.retargetEdge starOf e₀)).internalEdges := by
      rw [contractWithStars_eraseInternalEdge_internalEdges A starOf he₀]
      exact Multiset.mem_map.mpr ⟨e, heComplErase, rfl⟩
    by_cases hprojEq :
        A.retargetVertex starOf u = A.retargetVertex starOf v
    · rw [hprojEq]
      exact FeynmanGraph.SupportReachable.refl _ _
    · refine SimpleGraph.Adj.reachable
        (G := ((A.contractWithStars starOf).eraseInternalEdge
          (A.retargetEdge starOf e₀)).toSimpleGraph) ?_
      rw [FeynmanGraph.toSimpleGraph_adj]
      refine ⟨hprojEq, A.retargetEdge starOf e, hretarget, ?_⟩
      rcases hend with ⟨hseq, hteq⟩ | ⟨hseq, hteq⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [retargetEdge_source, hseq]
        · rw [retargetEdge_target, hteq]
      · right
        refine ⟨?_, ?_⟩
        · rw [retargetEdge_source, hseq]
        · rw [retargetEdge_target, hteq]

theorem contractWithStars_eraseInternalEdge_path_supportReachable
    {A : AdmissibleSubgraph G} (hDisj : A.IsPairwiseDisjoint)
    (starOf : FeynmanSubgraph G → VertexId)
    {e₀ : FeynmanEdge} (he₀ : e₀ ∈ A.complementEdges)
    {u v : VertexId} (h : (G.eraseInternalEdge e₀).SupportReachable u v) :
    ((A.contractWithStars starOf).eraseInternalEdge
      (A.retargetEdge starOf e₀)).SupportReachable
        (A.retargetVertex starOf u) (A.retargetVertex starOf v) := by
  unfold FeynmanGraph.SupportReachable at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
      exact FeynmanGraph.SupportReachable.refl _ _
  | @tail x y _ hxy ih =>
      have hstep : (G.eraseInternalEdge e₀).SupportAdj x y := by
        rw [← FeynmanGraph.toSimpleGraph_adj]
        exact hxy
      have hstep_reach :=
        contractWithStars_eraseInternalEdge_step_supportReachable
          hDisj starOf he₀ hstep
      exact ih.trans hstep_reach

theorem contractWithStars_eraseInternalEdge_isSupportConnected
    {A : AdmissibleSubgraph G}
    {e₀ : FeynmanEdge} (he₀ : e₀ ∈ A.complementEdges)
    (hGErase : (G.eraseInternalEdge e₀).IsSupportConnected)
    (hDisj : A.IsPairwiseDisjoint) (hCompNE : A.HasNonemptyComponents)
    (starOf : FeynmanSubgraph G → VertexId) :
    ((A.contractWithStars starOf).eraseInternalEdge
      (A.retargetEdge starOf e₀)).IsSupportConnected := by
  have preimage : ∀ x, x ∈
      ((A.contractWithStars starOf).eraseInternalEdge
        (A.retargetEdge starOf e₀)).vertices →
      ∃ x₀ ∈ G.vertices, A.retargetVertex starOf x₀ = x := by
    intro x hx
    rw [FeynmanGraph.eraseInternalEdge_vertices,
      contractWithStars_vertices] at hx
    rcases Finset.mem_union.mp hx with hsdiff | hstar
    · rcases Finset.mem_sdiff.mp hsdiff with ⟨hxG, hxA⟩
      exact ⟨x, hxG, retargetVertex_of_not_mem A starOf hxA⟩
    · rw [mem_starVertices] at hstar
      rcases hstar with ⟨γ, hγ, rfl⟩
      have hγne : γ.IsNonempty := hCompNE γ hγ
      have hγverts : γ.vertices.Nonempty := by
        unfold FeynmanSubgraph.IsNonempty FeynmanSubgraph.vertexCount at hγne
        exact Finset.card_pos.mp hγne
      obtain ⟨w, hwγ⟩ := hγverts
      exact ⟨w, γ.vertices_subset hwγ,
        retargetVertex_of_mem_component hDisj starOf hγ hwγ⟩
  intro u' v' hu' hv'
  obtain ⟨u, huG, rfl⟩ := preimage u' hu'
  obtain ⟨v, hvG, rfl⟩ := preimage v' hv'
  have huErase : u ∈ (G.eraseInternalEdge e₀).vertices := by
    simpa using huG
  have hvErase : v ∈ (G.eraseInternalEdge e₀).vertices := by
    simpa using hvG
  exact contractWithStars_eraseInternalEdge_path_supportReachable
    hDisj starOf he₀ (hGErase huErase hvErase)

theorem contractWithStars_step_supportReachable
    {A : AdmissibleSubgraph G} (hDisj : A.IsPairwiseDisjoint)
    (starOf : FeynmanSubgraph G → VertexId)
    {u v : VertexId} (h : G.SupportAdj u v) :
    (A.contractWithStars starOf).SupportReachable
      (A.retargetVertex starOf u) (A.retargetVertex starOf v) := by
  obtain ⟨_hne, e, heG, hend⟩ := h
  by_cases heA : e ∈ A.internalEdges
  · rcases mem_internalEdges.mp heA with ⟨γ, hγ, heγ⟩
    have hsupp : e.SupportedOn γ.vertices := γ.edges_supported e heγ
    simp [FeynmanEdge.SupportedOn] at hsupp
    obtain ⟨hsγ, htγ⟩ := hsupp
    have huγ : u ∈ γ.vertices := by
      rcases hend with ⟨hs, _⟩ | ⟨_, ht⟩
      · exact hs ▸ hsγ
      · exact ht ▸ htγ
    have hvγ : v ∈ γ.vertices := by
      rcases hend with ⟨_, ht⟩ | ⟨hs, _⟩
      · exact ht ▸ htγ
      · exact hs ▸ hsγ
    rw [retargetVertex_of_mem_component hDisj starOf hγ huγ,
      retargetVertex_of_mem_component hDisj starOf hγ hvγ]
    exact FeynmanGraph.SupportReachable.refl _ _
  · have hecompl : e ∈ A.complementEdges := by
      unfold complementEdges
      rw [Multiset.mem_sub]
      have hAcount : A.internalEdges.count e = 0 :=
        Multiset.count_eq_zero.mpr heA
      have hGcount : 0 < G.internalEdges.count e :=
        Multiset.count_pos.mpr heG
      omega
    have hretarget : A.retargetEdge starOf e ∈
        (A.contractWithStars starOf).internalEdges := by
      rw [contractWithStars_internalEdges]
      exact Multiset.mem_map.mpr ⟨e, hecompl, rfl⟩
    by_cases hprojEq :
        A.retargetVertex starOf u = A.retargetVertex starOf v
    · rw [hprojEq]
      exact FeynmanGraph.SupportReachable.refl _ _
    · refine SimpleGraph.Adj.reachable (G := (A.contractWithStars starOf).toSimpleGraph) ?_
      rw [FeynmanGraph.toSimpleGraph_adj]
      refine ⟨hprojEq, A.retargetEdge starOf e, hretarget, ?_⟩
      rcases hend with ⟨hseq, hteq⟩ | ⟨hseq, hteq⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [retargetEdge_source, hseq]
        · rw [retargetEdge_target, hteq]
      · right
        refine ⟨?_, ?_⟩
        · rw [retargetEdge_source, hseq]
        · rw [retargetEdge_target, hteq]

theorem contractWithStars_path_supportReachable
    {A : AdmissibleSubgraph G} (hDisj : A.IsPairwiseDisjoint)
    (starOf : FeynmanSubgraph G → VertexId)
    {u v : VertexId} (h : G.SupportReachable u v) :
    (A.contractWithStars starOf).SupportReachable
      (A.retargetVertex starOf u) (A.retargetVertex starOf v) := by
  unfold FeynmanGraph.SupportReachable at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl =>
      exact FeynmanGraph.SupportReachable.refl _ _
  | @tail x y _ hxy ih =>
      have hstep : G.SupportAdj x y := by
        rw [← FeynmanGraph.toSimpleGraph_adj]
        exact hxy
      have hstep_reach :=
        contractWithStars_step_supportReachable hDisj starOf hstep
      exact ih.trans hstep_reach

theorem contractWithStars_isSupportConnected
    {A : AdmissibleSubgraph G}
    (hG : G.IsSupportConnected) (hDisj : A.IsPairwiseDisjoint)
    (hCompNE : A.HasNonemptyComponents)
    (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).IsSupportConnected := by
  have preimage : ∀ x, x ∈ (A.contractWithStars starOf).vertices →
      ∃ x₀ ∈ G.vertices, A.retargetVertex starOf x₀ = x := by
    intro x hx
    rw [contractWithStars_vertices] at hx
    rcases Finset.mem_union.mp hx with hsdiff | hstar
    · rcases Finset.mem_sdiff.mp hsdiff with ⟨hxG, hxA⟩
      exact ⟨x, hxG, retargetVertex_of_not_mem A starOf hxA⟩
    · rw [mem_starVertices] at hstar
      rcases hstar with ⟨γ, hγ, rfl⟩
      have hγne : γ.IsNonempty := hCompNE γ hγ
      have hγverts : γ.vertices.Nonempty := by
        unfold FeynmanSubgraph.IsNonempty FeynmanSubgraph.vertexCount at hγne
        exact Finset.card_pos.mp hγne
      obtain ⟨w, hwγ⟩ := hγverts
      exact ⟨w, γ.vertices_subset hwγ,
        retargetVertex_of_mem_component hDisj starOf hγ hwγ⟩
  intro u' v' hu' hv'
  obtain ⟨u, huG, rfl⟩ := preimage u' hu'
  obtain ⟨v, hvG, rfl⟩ := preimage v' hv'
  exact contractWithStars_path_supportReachable hDisj starOf (hG huG hvG)

theorem contractWithStars_vertexCount
    {A : AdmissibleSubgraph G} {starOf : FeynmanSubgraph G → VertexId}
    (h : A.IsFreshStarAssignment starOf) :
    (A.contractWithStars starOf).vertexCount =
      (G.vertexCount - A.vertices.card) + A.elements.card := by
  unfold FeynmanGraph.vertexCount
  rw [contractWithStars_vertices]
  rw [Finset.card_union_of_disjoint h.disjoint_sdiff_starVertices]
  rw [Finset.card_sdiff_of_subset A.vertices_subset]
  rw [h.card_starVertices]

/-- Predicate: the admissible subgraph has at least one connected-divergent
component. This is the first lightweight filter toward the final proper
admissible coproduct index. -/
def IsNonempty (A : AdmissibleSubgraph G) : Prop :=
  A.elements.Nonempty

theorem empty_isPairwiseDisjoint :
    (empty G).IsPairwiseDisjoint := by
  exact Forest.empty_isPairwiseDisjoint

theorem singleton_isPairwiseDisjoint
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).IsPairwiseDisjoint := by
  exact Forest.singleton_isPairwiseDisjoint γ hγ.isDivergent

@[simp] theorem empty_not_isNonempty :
    ¬ (empty G).IsNonempty := by
  rw [IsNonempty, empty_elements]
  simp

theorem singleton_isNonempty
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).IsNonempty := by
  simp [IsNonempty]

theorem singleton_isFreshStarAssignment
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).IsFreshStarAssignment
      (fun _ : FeynmanSubgraph G => γ.contractedVertex) := by
  constructor
  · intro γ' hγ'
    rw [mem_singleton_elements] at hγ'
    rw [hγ']
    exact γ.contractedVertex_not_mem_G
  · intro γ₁ hγ₁ γ₂ hγ₂ _hstar
    rw [mem_singleton_elements] at hγ₁ hγ₂
    rw [hγ₁, hγ₂]

@[simp] theorem singleton_starVertices
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) :
    (singleton γ hγ).starVertices starOf = {starOf γ} := by
  rw [starVertices, singleton_elements]
  simp

/-- On a singleton admissible subgraph, component-wise vertex retargeting is
the ordinary subgraph retargeting predicate. -/
theorem singleton_retargetVertex
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) (v : VertexId) :
    (singleton γ hγ).retargetVertex starOf v =
      if v ∈ γ.vertices then starOf γ else v := by
  by_cases hv : v ∈ γ.vertices
  · rw [if_pos hv]
    exact retargetVertex_of_mem_component
      (A := singleton γ hγ) (singleton_isPairwiseDisjoint γ hγ)
      starOf (γ := γ) (by simp) hv
  · rw [if_neg hv]
    exact retargetVertex_of_not_mem (singleton γ hγ) starOf
      (by simpa using hv)

/-- On a singleton admissible subgraph, component-wise edge retargeting is the
existing `FeynmanEdge.retarget`. -/
theorem singleton_retargetEdge
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) (e : FeynmanEdge) :
    (singleton γ hγ).retargetEdge starOf e =
      e.retarget γ.vertices (starOf γ) := by
  cases e
  simp [retargetEdge, FeynmanEdge.retarget, singleton_retargetVertex]

/-- On a singleton admissible subgraph, component-wise external-leg retargeting
is the existing `ExternalLeg.retarget`. -/
theorem singleton_retargetExternalLeg
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) (ℓ : ExternalLeg) :
    (singleton γ hγ).retargetExternalLeg starOf ℓ =
      ℓ.retarget γ.vertices (starOf γ) := by
  cases ℓ
  simp [retargetExternalLeg, ExternalLeg.retarget, singleton_retargetVertex]

@[simp] theorem singleton_contractWithStars_vertices
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) :
    ((singleton γ hγ).contractWithStars starOf).vertices =
      (γ.contractWith (starOf γ)).vertices := by
  rw [contractWithStars_vertices, FeynmanSubgraph.contractWith_vertices,
    singleton_vertices, singleton_starVertices]

@[simp] theorem singleton_contractWithStars_internalEdges
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) :
    ((singleton γ hγ).contractWithStars starOf).internalEdges =
      (γ.contractWith (starOf γ)).internalEdges := by
  rw [contractWithStars_internalEdges, FeynmanSubgraph.contractWith_internalEdges,
    singleton_complementEdges]
  refine Multiset.map_congr rfl ?_
  intro e _he
  exact singleton_retargetEdge γ hγ starOf e

@[simp] theorem singleton_contractWithStars_externalLegs
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) :
    ((singleton γ hγ).contractWithStars starOf).externalLegs =
      (γ.contractWith (starOf γ)).externalLegs := by
  rw [contractWithStars_externalLegs, FeynmanSubgraph.contractWith_externalLegs]
  refine Multiset.map_congr rfl ?_
  intro ℓ _hℓ
  exact singleton_retargetExternalLeg γ hγ starOf ℓ

/-- Singleton recovery for the forest-contraction skeleton: when the
admissible subgraph has one component, `contractWithStars` is exactly the
existing one-component `contractWith`. -/
theorem singleton_contractWithStars
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent)
    (starOf : FeynmanSubgraph G → VertexId) :
    (singleton γ hγ).contractWithStars starOf =
      γ.contractWith (starOf γ) := by
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  exact ⟨singleton_contractWithStars_vertices γ hγ starOf,
    singleton_contractWithStars_internalEdges γ hγ starOf,
    singleton_contractWithStars_externalLegs γ hγ starOf⟩

/-- Singleton recovery using the existing default contracted vertex. This is
the form needed to replace the conservative admissible contraction by the
forest-contraction skeleton without changing existing summands. -/
theorem singleton_contractWithStars_contract
    (γ : FeynmanSubgraph G) (hγ : γ.IsConnectedDivergent) :
    (singleton γ hγ).contractWithStars (fun _ => γ.contractedVertex) =
      γ.contract := by
  rw [singleton_contractWithStars]
  rfl

@[simp] theorem ofForest_forest (F : Forest G)
    (hF : F.IsConnectedDivergent) :
    (ofForest F hF).forest = F := rfl

@[simp] theorem ofForest_elements (F : Forest G)
    (hF : F.IsConnectedDivergent) :
    (ofForest F hF).elements = F.elements := rfl

/-- Build an admissible subgraph from raw connected-divergent forest
elements. -/
def ofElements (s : Finset (FeynmanSubgraph G))
    (h : Forest.IsConnectedDivergentElements (G := G) s) :
    AdmissibleSubgraph G :=
  ofForest (Forest.ofConnectedDivergentElements s h)
    (Forest.ofConnectedDivergentElements_isConnectedDivergent s h)

@[simp] theorem ofElements_elements (s : Finset (FeynmanSubgraph G))
    (h : Forest.IsConnectedDivergentElements (G := G) s) :
    (ofElements (G := G) s h).elements = s := rfl

/-- Finite index of all admissible subgraphs represented by
connected-divergent forests. It is built from `Forest.connectedDivergentIndex`
so membership is independent of the proof fields of `AdmissibleSubgraph`. -/
noncomputable def connectedDivergentIndex
    (G : FeynmanGraph) [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraph G) := by
  classical
  exact (Forest.connectedDivergentIndex G).attach.image
    fun F =>
      ofForest F.1
        (Forest.mem_connectedDivergentIndex_isConnectedDivergent G F.2)

/-- Every admissible subgraph appears in the finite connected-divergent
forest index. -/
theorem mem_connectedDivergentIndex
    (G : FeynmanGraph) [DivergenceMeasure G] [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraph G) :
    A ∈ connectedDivergentIndex G := by
  classical
  unfold connectedDivergentIndex
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨A.forest,
    Forest.mem_connectedDivergentIndex_of_isConnectedDivergent
      G A.forest A.isConnectedDivergent⟩, by simp, ?_⟩
  exact AdmissibleSubgraph.ext rfl

end AdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
