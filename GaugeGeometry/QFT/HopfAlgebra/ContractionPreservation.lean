import GaugeGeometry.QFT.Combinatorial.SubGraph
import GaugeGeometry.QFT.Combinatorial.Permutation

/-!
# Contract preserves Connes–Kreimer generator predicates  [Sprint D prep]

This file establishes two preservation lemmas required by Sprint D's
`Bialgebra ℚ HopfH` instance construction:

* `contract.IsOnePI` — 1PI (bridge-freeness) is preserved under
  contraction, given `G.IsOnePI ∧ γ.IsOnePI ∧ γ.IsNonempty`.

* `contract.IsDivergent` — superficial divergence is preserved under
  contraction (via a typeclass `IsDivergencePreservedByContract`
  expressing the CK 1998 power-counting compatibility; the instance is
  supplied externally, mirroring `IsPermInvariantDivergence` from
  Sprint A Permutation.lean).

Together with the already-proved
`FeynmanSubgraph.IsConnected_contract_of_IsConnected` (Sprint A H1.16),
these close the gap needed so that `γ ∈ properConnectedDivergentSubgraphs`
implies `γ.contract.IsConnectedDivergent`, hence `γ.contract.toClass` is
a legitimate `HopfGen` element, hence `coproduct : HopfH →ₐ[ℚ] HopfH ⊗ HopfH`
with source and target types aligned.

## Multiset-count subtlety (Path-2, 2026-04-24)

`e ∈ γ.complementEdges` does NOT imply `e ∉ γ.internalEdges` — it only
says `count e γ.internalEdges < count e G.internalEdges`. We therefore
hypothesise the strict count inequality directly in `asSubOfErase` and
derive `γ.internalEdges ≤ G.internalEdges.erase e` from it.

## Tag map

* `[Comb]` `le_erase_of_count_lt` — Multiset algebra helper
* `[Graph]` `asSubOfErase` — γ re-interpreted as subgraph of `G.eraseInternalEdge e`
* `[Graph]` `contract_eraseInternalEdge_eq` — data equality of two contract outputs
* `[Graph]` `contract_isOnePI` — **main theorem 1**
* `[Algebra]` class `IsDivergencePreservedByContract` — CK power-counting compatibility
* `[Graph]` `contract_isDivergent` — **main theorem 2** (via the typeclass)
-/

namespace GaugeGeometry.QFT.Combinatorial

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-! ### Multiset algebra helpers (count-based) -/

/-- If `A ≤ B` and `count x A < count x B`, then `A ≤ B.erase x`. -/
private theorem Multiset_le_erase_of_count_lt {α : Type*} [DecidableEq α]
    {A B : Multiset α} {x : α}
    (hAB : A ≤ B) (hcount : Multiset.count x A < Multiset.count x B) :
    A ≤ B.erase x := by
  rw [Multiset.le_iff_count]
  intro y
  by_cases hyx : y = x
  · subst hyx
    rw [Multiset.count_erase_self]
    omega
  · rw [Multiset.count_erase_of_ne hyx]
    exact Multiset.count_le_of_le y hAB

/-- Multiset subtraction and erase commute in the right position:
`(A - B).erase x = (A.erase x) - B`. Unconditional on `x ∈ B`. -/
private theorem Multiset_sub_erase_comm {α : Type*} [DecidableEq α]
    (A B : Multiset α) (x : α) :
    (A - B).erase x = (A.erase x) - B := by
  refine Multiset.ext.mpr (fun y => ?_)
  by_cases hyx : y = x
  · subst hyx
    rw [Multiset.count_erase_self, Multiset.count_sub,
        Multiset.count_sub, Multiset.count_erase_self]
    omega
  · rw [Multiset.count_erase_of_ne hyx, Multiset.count_sub,
        Multiset.count_sub, Multiset.count_erase_of_ne hyx]

/-! ### Re-interpreting γ as a subgraph of `G.eraseInternalEdge e`

For `e ∈ γ.complementEdges` (i.e. γ has strictly fewer copies of `e`
than G), γ's three data fields still satisfy the submultiset conditions
with ambient `G.eraseInternalEdge e`. -/

/-- γ re-interpreted as a subgraph of `G.eraseInternalEdge e`,
provided the count of `e` in γ is strictly less than in G. -/
def asSubOfErase (γ : FeynmanSubgraph G) {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges) :
    FeynmanSubgraph (G.eraseInternalEdge e) where
  vertices := γ.vertices
  internalEdges := γ.internalEdges
  externalLegs := γ.externalLegs
  vertices_subset := γ.vertices_subset
  internalEdges_le :=
    Multiset_le_erase_of_count_lt γ.internalEdges_le h
  externalLegs_le := γ.externalLegs_le
  edges_supported := γ.edges_supported
  legs_supported := γ.legs_supported

@[simp] theorem asSubOfErase_vertices (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges) :
    (γ.asSubOfErase h).vertices = γ.vertices := rfl

@[simp] theorem asSubOfErase_internalEdges (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges) :
    (γ.asSubOfErase h).internalEdges = γ.internalEdges := rfl

@[simp] theorem asSubOfErase_externalLegs (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges) :
    (γ.asSubOfErase h).externalLegs = γ.externalLegs := rfl

/-- `asSubOfErase` preserves `IsConnected`: subgraph connectedness
depends only on γ's three data fields (the ambient only constrains,
does not appear in `toFeynmanGraph`). -/
theorem asSubOfErase_isConnected (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges)
    (hγConn : γ.IsConnected) :
    (γ.asSubOfErase h).IsConnected := by
  unfold IsConnected at hγConn ⊢
  show (γ.asSubOfErase h).toFeynmanGraph.IsSupportConnected
  have : (γ.asSubOfErase h).toFeynmanGraph = γ.toFeynmanGraph := by
    apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
    refine ⟨rfl, rfl, rfl⟩
  rw [this]; exact hγConn

theorem asSubOfErase_isNonempty (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges)
    (hγne : γ.IsNonempty) :
    (γ.asSubOfErase h).IsNonempty := by
  unfold IsNonempty vertexCount at hγne ⊢
  exact hγne

/-! ### Membership implies strict count inequality -/

/-- If `e ∈ γ.complementEdges`, then γ has strictly fewer copies of `e`
than G. -/
theorem count_lt_of_mem_complementEdges (γ : FeynmanSubgraph G)
    {e : FeynmanEdge} (he : e ∈ γ.complementEdges) :
    Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges := by
  unfold complementEdges at he
  -- e ∈ G.internalEdges - γ.internalEdges iff count γ.I e < count G.I e
  rw [Multiset.mem_sub] at he
  exact he

/-! ### Data equality of the two contract outputs

Core technical fact:
`(γ.contract).eraseInternalEdge e' = (γ.asSubOfErase h).contract`

where `e'` is the retargeted form of `e` in the contracted graph and
`h` witnesses `count e γ.I < count e G.I`. -/

/-- `asSubOfErase` has the same `contractedVertex`:
`freshVertex (G.eraseInternalEdge e).vertices = freshVertex G.vertices`
since `eraseInternalEdge` leaves vertices unchanged. -/
@[simp] theorem asSubOfErase_contractedVertex (γ : FeynmanSubgraph G)
    {e : FeynmanEdge}
    (h : Multiset.count e γ.internalEdges < Multiset.count e G.internalEdges) :
    (γ.asSubOfErase h).contractedVertex = γ.contractedVertex := by
  unfold contractedVertex
  rfl

/-- `(γ.contract).eraseInternalEdge e' = (asSubOfErase ...).contract`
as `FeynmanGraph`s, where e' is the retarget of e. -/
theorem contract_eraseInternalEdge_eq (γ : FeynmanSubgraph G)
    {e : FeynmanEdge} (he : e ∈ γ.complementEdges) :
    (γ.contract).eraseInternalEdge
        (FeynmanEdge.retarget γ.vertices γ.contractedVertex e) =
      (γ.asSubOfErase (count_lt_of_mem_complementEdges γ he)).contract := by
  set h := count_lt_of_mem_complementEdges γ he
  set e' := FeynmanEdge.retarget γ.vertices γ.contractedVertex e
  apply FeynmanGraph.mk.injEq _ _ _ _ _ _ |>.mpr
  refine ⟨?_, ?_, ?_⟩
  · -- vertices: both sides are `(G.vertices \ γ.vertices) ∪ {star}`.
    show (γ.contract).vertices = (γ.asSubOfErase h).contract.vertices
    rw [contract_vertices, contract_vertices, asSubOfErase_vertices,
      asSubOfErase_contractedVertex]
    -- RHS vertices of asSubOfErase contract:
    -- (G.eraseInternalEdge e).vertices \ γ.vertices ∪ {star}
    -- eraseInternalEdge leaves vertices unchanged
    rfl
  · -- internalEdges:
    -- LHS: (γ.complementEdges.map retarget).erase e'
    -- RHS: (asSubOfErase.complementEdges).map retarget
    --    = (G.internalEdges.erase e - γ.internalEdges).map retarget
    --    = ((G.internalEdges - γ.internalEdges).erase e).map retarget  [Multiset_sub_erase_comm]
    --    = (γ.complementEdges.erase e).map retarget
    -- The final step uses `Multiset.map_erase_of_mem` (Mathlib), which does NOT require injectivity —
    -- it only needs `e ∈ γ.complementEdges`.
    show (γ.contract.eraseInternalEdge e').internalEdges =
      (γ.asSubOfErase h).contract.internalEdges
    show (γ.complementEdges.map (FeynmanEdge.retarget γ.vertices γ.contractedVertex)).erase e' =
      ((γ.asSubOfErase h).complementEdges).map
        (FeynmanEdge.retarget (γ.asSubOfErase h).vertices
          (γ.asSubOfErase h).contractedVertex)
    rw [asSubOfErase_contractedVertex]
    show _ = ((γ.asSubOfErase h).complementEdges).map
      (FeynmanEdge.retarget γ.vertices γ.contractedVertex)
    -- asSubOfErase.complementEdges = G.internalEdges.erase e - γ.internalEdges
    have hasSub_compl : (γ.asSubOfErase h).complementEdges =
        G.internalEdges.erase e - γ.internalEdges := by
      unfold complementEdges
      show (G.eraseInternalEdge e).internalEdges -
        (γ.asSubOfErase h).internalEdges = _
      rw [FeynmanGraph.eraseInternalEdge_internalEdges, asSubOfErase_internalEdges]
    rw [hasSub_compl]
    -- Multiset_sub_erase_comm: (G.I - γ.I).erase e = (G.I.erase e) - γ.I
    have hcompl_erase : γ.complementEdges.erase e =
        G.internalEdges.erase e - γ.internalEdges := by
      unfold complementEdges
      exact Multiset_sub_erase_comm G.internalEdges γ.internalEdges e
    rw [← hcompl_erase]
    -- Apply Multiset.map_erase_of_mem: (s.erase x).map f = (s.map f).erase (f x) when x ∈ s.
    symm
    exact Multiset.map_erase_of_mem
      (FeynmanEdge.retarget γ.vertices γ.contractedVertex) γ.complementEdges he
  · -- externalLegs: both sides are G.externalLegs.map (retarget γ.vertices star)
    --   LHS: γ.contract.externalLegs (not affected by eraseInternalEdge)
    --   RHS: (asSubOfErase).contract.externalLegs
    --      = (asSubOfErase).externalLegs is γ.externalLegs (no change on asSubOfErase)
    --      wait — contract externalLegs is G.externalLegs.map retarget, not γ.externalLegs.
    --      asSubOfErase ambient is G.eraseInternalEdge e, whose externalLegs = G.externalLegs.
    show γ.contract.externalLegs = (γ.asSubOfErase h).contract.externalLegs
    rw [contract_externalLegs, contract_externalLegs,
      asSubOfErase_vertices, asSubOfErase_contractedVertex]
    rfl

/-! ### Main theorem: `contract` preserves 1PI -/

/-- **`contract.IsOnePI`** — Under `G.IsOnePI ∧ γ.IsOnePI ∧ γ.IsNonempty`,
the contracted graph `γ.contract` is also 1PI.

**Proof sketch**:
* `IsOnePI := IsSupportConnected ∧ no_bridge`.
* Part 1 (support-connectedness): Sprint A H1.16 with `G.IsSupportConnected`
  (from `G.IsOnePI`) + `γ.IsConnected` (from `γ.IsOnePI`) + `γ.IsNonempty`.
* Part 2 (no-bridge): Suppose for contradiction that some `e' ∈ γ.contract.internalEdges`
  is a bridge. Then `e' = retarget ... e` for some `e ∈ γ.complementEdges`.
  The data equality `contract_eraseInternalEdge_eq` rewrites
  `(γ.contract).eraseInternalEdge e'` as `(γ.asSubOfErase _).contract`. Since
  `(G.eraseInternalEdge e).IsSupportConnected` (from `G.IsOnePI.no_bridge e`)
  and `γ.IsConnected ∧ γ.IsNonempty` carry over to `asSubOfErase`, H1.16
  applies to show this contract is support-connected, contradicting
  `γ.contract.IsBridge e'`.
-/
theorem contract_isOnePI {γ : FeynmanSubgraph G}
    (hG : G.IsOnePI) (hγ : γ.IsOnePI) (hγne : γ.IsNonempty) :
    γ.contract.IsOnePI := by
  refine ⟨?_, ?_⟩
  · -- Support-connectedness via H1.16.
    exact IsConnected_contract_of_IsConnected
      hG.isSupportConnected hγ.isConnected hγne
  · -- No-bridge: by contradiction, assuming some e' is a bridge.
    intro e' he' hBridge
    -- e' ∈ γ.contract.internalEdges = γ.complementEdges.map retarget
    rw [contract_internalEdges] at he'
    rcases Multiset.mem_map.mp he' with ⟨e, hecompl, he'_eq⟩
    -- hBridge : (γ.contract).eraseInternalEdge e' is not support-connected.
    -- Rewrite via contract_eraseInternalEdge_eq.
    have h_lt := count_lt_of_mem_complementEdges γ hecompl
    have hGerase_conn : (G.eraseInternalEdge e).IsSupportConnected := by
      -- From G.IsOnePI.no_bridge at e (e ∈ G.internalEdges since e ∈ γ.complementEdges ⊆ G.I).
      have heG : e ∈ G.internalEdges :=
        Multiset.mem_of_le (Multiset.sub_le_self _ _) hecompl
      have hNoBridge := hG.no_bridge e heG
      -- ¬ G.IsBridge e means ¬(e ∈ G.I ∧ ¬(G.eraseInternalEdge e).IsSupportConnected).
      -- With e ∈ G.I already, the remaining clause gives IsSupportConnected.
      unfold FeynmanGraph.IsBridge at hNoBridge
      push Not at hNoBridge
      exact hNoBridge heG
    -- Apply H1.16 to asSubOfErase-packaged γ in ambient G.eraseInternalEdge e.
    have hContractErase_conn :
        (γ.asSubOfErase h_lt).contract.IsSupportConnected :=
      IsConnected_contract_of_IsConnected hGerase_conn
        (asSubOfErase_isConnected γ h_lt hγ.isConnected)
        (asSubOfErase_isNonempty γ h_lt hγne)
    -- Now transport via data equality.
    have h_eq := contract_eraseInternalEdge_eq γ hecompl
    -- hBridge.2 : ¬ (γ.contract.eraseInternalEdge e').IsSupportConnected.
    -- We have (γ.contract.eraseInternalEdge e') = (asSubOfErase).contract.
    -- So this says ¬ (asSubOfErase.contract).IsSupportConnected, contradicting hContractErase_conn.
    apply hBridge.2
    -- e' = retarget γ.vertices γ.contractedVertex e (by he'_eq).
    rw [← he'_eq]
    rw [h_eq]
    exact hContractErase_conn

end FeynmanSubgraph

/-! ### Divergence preservation under contract (Plan-D1: typeclass)

The Connes–Kreimer 1998 setup postulates that the superficial
divergence degree of a proper 1PI subgraph is preserved in the
contracted quotient graph (power-counting stability). This is a
physical/combinatorial fact whose concrete derivation depends on the
specific `DivergenceMeasure` in use; here we abstract it as a
typeclass assumption, mirroring Sprint A's
`IsPermInvariantDivergence` pattern.

Concrete MSSM-style measures that satisfy power-counting stability
yield instances of this class; the abstract formalization just
requires the class fact. Path-W's global
`[∀ G, DivergenceMeasure G]` hypothesis supplies `DivergenceMeasure`
on every `γ.contract`; this class adds the compatibility. -/

/--
**Plan-D1 typeclass** — Divergence degrees are preserved when
contracting along a 1PI divergent subgraph. If γ is 1PI + divergent,
then the full self-subgraph of `γ.contract` is also divergent under
the `DivergenceMeasure` of `γ.contract`.

Note: this class takes `DivergenceMeasure` as a `∀`-parameter family,
matching the Sprint C1/C2 Path-W pattern of global instance supply.
-/
class IsDivergencePreservedByContract
    [∀ G : FeynmanGraph, DivergenceMeasure G] : Prop where
  contract_isDivergent :
    ∀ {G : FeynmanGraph} (hGwf : G.WellFormed) {γ : FeynmanSubgraph G}
      (_hγ1PI : γ.IsOnePI) (_hγDiv : γ.IsDivergent),
      (FeynmanSubgraph.self γ.contract
        (FeynmanSubgraph.wellFormed_contract hGwf)).IsDivergent

/--
**Forest-contraction divergence preservation** — The forest-level analogue of
`IsDivergencePreservedByContract`. If the ambient graph is superficially
divergent, then contracting a disjoint admissible forest of subdivergences
with a fresh component-star assignment yields a superficially divergent
quotient graph.

This is the CK power-counting stability assumption needed after replacing the
connected-only coproduct index by an admissible forest index. Concrete
power-counting measures supply instances, just as for the one-component
contract preservation class above.
-/
class IsDivergencePreservedByAdmissibleForestContract
    [∀ G : FeynmanGraph, DivergenceMeasure G] : Prop where
  contractWithStars_isDivergent :
    ∀ {G : FeynmanGraph} (hGwf : G.WellFormed)
      (_hGDiv : (FeynmanSubgraph.self G hGwf).IsDivergent)
      (A : AdmissibleSubgraph G)
      (_hDisj : A.IsPairwiseDisjoint)
      (_hCompNE : A.HasNonemptyComponents)
      (starOf : FeynmanSubgraph G → VertexId)
      (_hFresh : A.IsFreshStarAssignment starOf)
      (hWF : (A.contractWithStars starOf).WellFormed),
        (FeynmanSubgraph.self (A.contractWithStars starOf) hWF).IsDivergent

namespace AdmissibleSubgraph

variable {G : FeynmanGraph}

/-- Re-export of forest-contraction divergence preservation with arguments in
the order used by the admissible coproduct API. -/
theorem contractWithStars_isDivergent
    [∀ G : FeynmanGraph, DivergenceMeasure G]
    [IsDivergencePreservedByAdmissibleForestContract]
    (A : AdmissibleSubgraph G) (hGwf : G.WellFormed)
    (hGDiv : (FeynmanSubgraph.self G hGwf).IsDivergent)
    (hDisj : A.IsPairwiseDisjoint)
    (hCompNE : A.HasNonemptyComponents)
    (starOf : FeynmanSubgraph G → VertexId)
    (hFresh : A.IsFreshStarAssignment starOf)
    (hWF : (A.contractWithStars starOf).WellFormed) :
    (FeynmanSubgraph.self (A.contractWithStars starOf) hWF).IsDivergent :=
  IsDivergencePreservedByAdmissibleForestContract.contractWithStars_isDivergent
    hGwf hGDiv A hDisj hCompNE starOf hFresh hWF

end AdmissibleSubgraph

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/--
**`contract.IsDivergent`** — Under the `IsDivergencePreservedByContract`
typeclass, contracting preserves the divergence predicate lifted to
the self-subgraph of the quotient graph.

This is a direct re-export of the typeclass axiom, with slightly
simplified argument packaging for downstream callers. -/
theorem contract_isDivergent
    [∀ G : FeynmanGraph, DivergenceMeasure G]
    [IsDivergencePreservedByContract]
    (hGwf : G.WellFormed) {γ : FeynmanSubgraph G}
    (hγ1PI : γ.IsOnePI) (hγDiv : γ.IsDivergent) :
    (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsDivergent :=
  IsDivergencePreservedByContract.contract_isDivergent hGwf hγ1PI hγDiv

/-! ### Combined: `contract.IsConnectedDivergent` -/

/--
`γ.contract` considered as a full self-subgraph is `IsConnectedDivergent`
(connected + 1PI + divergent), given the three preservation facts:
H1.16 (connectedness), `contract_isOnePI`, and `contract_isDivergent`.
-/
theorem contract_isConnectedDivergent
    [∀ G : FeynmanGraph, DivergenceMeasure G]
    [IsDivergencePreservedByContract]
    (hGwf : G.WellFormed) {γ : FeynmanSubgraph G}
    (hG1PI : G.IsOnePI) (hγ1PI : γ.IsOnePI)
    (hγne : γ.IsNonempty) (hγDiv : γ.IsDivergent) :
    (FeynmanSubgraph.self γ.contract
      (FeynmanSubgraph.wellFormed_contract hGwf)).IsConnectedDivergent := by
  refine ⟨?_, ?_, ?_⟩
  · -- IsConnected: H1.16 via contract_isOnePI's first component.
    show (FeynmanSubgraph.self γ.contract _).toFeynmanGraph.IsSupportConnected
    -- self's toFeynmanGraph is γ.contract itself.
    show γ.contract.IsSupportConnected
    exact IsConnected_contract_of_IsConnected hG1PI.isSupportConnected
      hγ1PI.isConnected hγne
  · -- IsOnePI at the contract level.
    show (FeynmanSubgraph.self γ.contract _).toFeynmanGraph.IsOnePI
    show γ.contract.IsOnePI
    exact contract_isOnePI hG1PI hγ1PI hγne
  · -- IsDivergent via the typeclass.
    exact contract_isDivergent hGwf hγ1PI hγDiv

end FeynmanSubgraph

/-! ### Ambient-invariance of the divergence degree (Sprint D, Path-W companion)

Path-W typeclass #4 (after `IsPermInvariantDivergence`,
`IsIsoInvariantDivergence`, `IsDivergencePreservedByContract`).

The Connes–Kreimer 1998 power-counting formula evaluates the superficial
divergence of a (sub)graph from intrinsic data (vertex/edge counts and
their dimensions); it does not depend on a choice of *ambient* graph.
For the strict CK construction (Sprint D `coproductGen_strict`) we need
to view a subgraph `γ : FeynmanSubgraph G` as a *graph in its own right*
`γ.toFeynmanGraph`, and the divergence degree of `γ` (as subgraph of `G`)
must agree with the divergence degree of the full self-subgraph
`FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed`
(as subgraph of `γ.toFeynmanGraph`).

This is the abstract intrinsic-divergence assumption of CK 1998. Concrete
power-counting measures (e.g. MSSM 1-loop) yield instances. -/

/--
**Path-W typeclass #4** — Divergence degree depends only on the intrinsic
subgraph data, not on the choice of ambient graph. For every
`γ : FeynmanSubgraph G`, the degree of `γ` (in ambient `G`) equals the
degree of `FeynmanSubgraph.self γ.toFeynmanGraph hWF` (in ambient
`γ.toFeynmanGraph`).
-/
class IsAmbientInvariantDivergence
    [∀ G : FeynmanGraph, DivergenceMeasure G] : Prop where
  degree_self_eq :
    ∀ {G : FeynmanGraph} (γ : FeynmanSubgraph G),
      DivergenceMeasure.degree
          (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed) =
        DivergenceMeasure.degree γ

namespace FeynmanSubgraph

variable {G : FeynmanGraph}

/-- **Subgraph divergence ⇒ graph-level self divergence**: the full
self-subgraph of `γ.toFeynmanGraph` is divergent under `γ.toFeynmanGraph`'s
own `DivergenceMeasure` whenever `γ` was divergent in the ambient `G`.

This is the divergence half of the subgraph-to-graph lift; the full
`IsConnectedDivergent` lift lives in `StrictGenerators.lean` (after
`FeynmanGraph.IsConnectedDivergent` becomes available). -/
theorem self_toFeynmanGraph_isDivergent
    [∀ G : FeynmanGraph, DivergenceMeasure G]
    [IsAmbientInvariantDivergence]
    {γ : FeynmanSubgraph G} (hγDiv : γ.IsDivergent) :
    (FeynmanSubgraph.self γ.toFeynmanGraph γ.toFeynmanGraph_wellFormed).IsDivergent := by
  unfold IsDivergent divergenceDegree
  rw [IsAmbientInvariantDivergence.degree_self_eq γ]
  exact hγDiv

end FeynmanSubgraph

end GaugeGeometry.QFT.Combinatorial
