import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestCarrier

/-!
# QFT-R1-body-573 — canonical φ⁴ forest quotient RIGHT generator

The left forest aggregate `AdmissibleSubgraph.toPhi4HopfH` (body-572) is paired here with the *right*
tensor factor: the canonical φ⁴ strict generator `Phi4HopfGen` of `G` contracted along an admissible
forest `A`.  The numerical divergence input is body-561's full-graph degree invariance
`ωφ4(G/A) = ωφ4(G)`; the topological well-formedness (well-formed / support-connected / 1PI) is pure
graph geometry, re-keyed to the explicit φ⁴ family so that **no** forbidden divergence class
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `IsDivergencePreservedByAdmissibleForestContract`) is ever consumed.

## The scope trap

The existing `FeynmanGraph.admissibleForestCanonicalContractGraph_wellFormed` /
`_isSupportConnected` / `_isOnePI_of_ambient_onePI` lemmas in `Coproduct.lean` sit inside a section
polluted by `variable`-injected forbidden divergence classes, so they are *unusable* in the
family-indexed φ⁴ world (those classes are uninhabitable there — body-564).  The **definitions**
`admissibleForestCanonicalContractGraph` and `admissibleForestCanonicalStarOf`, however, only need the
providable `[∀ G, DivergenceMeasure G]` (supplied by `phi4DivergenceMeasureFamily`) and
`[∀ G, Fintype (FeynmanSubgraph G)]`.  So this body **re-keys / reconstructs** each topology fact
instance-free by unfolding to the clean underlying `AdmissibleSubgraph.contractWithStars_*` lemmas
(which carry only `[DivergenceMeasure G]`).

## Contents

* Step 1 `phi4CanonicalForestStarOf`, `phi4CanonicalForestContractGraph` (+ rfl anchor).
* Step 2 `_wellFormed`, `_degree_eq_ambient` (body-561), `_isDivergent_of_ambient`.
* Step 3 `_isSupportConnected`, `_isOnePI` — instance-free topology re-key.
* Step 4 `_exists_self_isConnectedDivergent`.
* Step 5 `AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen` (+ value anchor).

The only instance binder is `[∀ G, Fintype (FeynmanSubgraph G)]`.  `letI := phi4DivergenceMeasureFamily G`
is used only locally for dot-notation.  Zero new `class` / `structure` / permanent `instance`; zero
forbidden divergence classes in any public type; no forest tensor summand / representative coproduct /
mapPerm reindex / class descent.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph} [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]

/-! ## Step 1 — the canonical φ⁴ forest-contraction graph -/

/-- **R-6c-QFT-R1-body-573 — canonical φ⁴ component-star assignment.**  The existing canonical
component-star assignment, at the explicit φ⁴ family (no blanket instance). -/
noncomputable def phi4CanonicalForestStarOf
    (G : FeynmanGraph) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    FeynmanSubgraph G → VertexId :=
  @FeynmanGraph.admissibleForestCanonicalStarOf phi4DivergenceMeasureFamily _ G A hA

/-- **R-6c-QFT-R1-body-573 — canonical φ⁴ forest-contraction graph.**  `G` contracted along the
admissible forest `A` with the canonical component-star assignment, at the explicit φ⁴ family. -/
noncomputable def phi4CanonicalForestContractGraph
    (G : FeynmanGraph) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    FeynmanGraph :=
  @FeynmanGraph.admissibleForestCanonicalContractGraph phi4DivergenceMeasureFamily _ G A hA

/-- **R-6c-QFT-R1-body-573 — the `contractWithStars` anchor.**  Exposes the canonical φ⁴ forest
contraction as the underlying `AdmissibleSubgraph.contractWithStars` (at the explicit φ⁴ measure), so
the clean `contractWithStars_*` topology lemmas apply after `rw`. -/
theorem phi4CanonicalForestContractGraph_eq_contractWithStars
    (G : FeynmanGraph) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    phi4CanonicalForestContractGraph G A hA =
      @AdmissibleSubgraph.contractWithStars G (phi4DivergenceMeasureFamily G) A
        (phi4CanonicalForestStarOf G A hA) :=
  rfl

/-! ## Step 2 — well-formedness, degree, divergence -/

/-- **R-6c-QFT-R1-body-573 — well-formedness (instance-free re-key).**  Re-key of
`AdmissibleSubgraph.contractWithStars_wellFormed` (which carries only `[DivergenceMeasure G]`). -/
theorem phi4CanonicalForestContractGraph_wellFormed
    (hGWF : G.WellFormed) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    (phi4CanonicalForestContractGraph G A hA).WellFormed := by
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  rw [phi4CanonicalForestContractGraph_eq_contractWithStars]
  exact AdmissibleSubgraph.contractWithStars_wellFormed A
    (phi4CanonicalForestStarOf G A hA) hGWF

/-- **R-6c-QFT-R1-body-573 — `ωφ4(G/A) = ωφ4(G)`.**  Full-graph φ⁴ degree invariance under the
canonical forest star-contraction (body-561). -/
theorem phi4CanonicalForestContractGraph_degree_eq_ambient
    (hGWF : G.WellFormed) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hQWF : (phi4CanonicalForestContractGraph G A hA).WellFormed) :
    (FeynmanSubgraph.self (phi4CanonicalForestContractGraph G A hA) hQWF).phi4SuperficialDegree
      = (FeynmanSubgraph.self G hGWF).phi4SuperficialDegree :=
  @FeynmanSubgraph.phi4SuperficialDegree_contractWithStars_self_eq
    G phi4DivergenceMeasureFamily hGWF A (phi4CanonicalForestStarOf G A hA) hQWF

/-- **R-6c-QFT-R1-body-573 — divergence transport.**  From ambient φ⁴-divergence of `G`, the quotient
`G/A` is φ⁴-divergent, purely from the degree equality — no `IsDivergencePreservedByAdmissibleForestContract`. -/
theorem phi4CanonicalForestContractGraph_isDivergent_of_ambient
    (hGWF : G.WellFormed) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hQWF : (phi4CanonicalForestContractGraph G A hA).WellFormed)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    @FeynmanSubgraph.IsDivergent (phi4CanonicalForestContractGraph G A hA)
      (phi4DivergenceMeasureFamily (phi4CanonicalForestContractGraph G A hA))
      (FeynmanSubgraph.self (phi4CanonicalForestContractGraph G A hA) hQWF) := by
  show (0 : Int) ≤
    (FeynmanSubgraph.self (phi4CanonicalForestContractGraph G A hA) hQWF).phi4SuperficialDegree
  rw [phi4CanonicalForestContractGraph_degree_eq_ambient hGWF A hA hQWF]
  exact hGDiv

/-! ## Step 3 — topology re-key (instance-free) -/

/-- **R-6c-QFT-R1-body-573 — support-connectedness (instance-free re-key).**  Re-key of
`AdmissibleSubgraph.contractWithStars_isSupportConnected`, fed by body-572's clean proper-disjoint
accessors. -/
theorem phi4CanonicalForestContractGraph_isSupportConnected
    (hG1PI : G.IsOnePI) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    (phi4CanonicalForestContractGraph G A hA).IsSupportConnected := by
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  rw [phi4CanonicalForestContractGraph_eq_contractWithStars]
  exact AdmissibleSubgraph.contractWithStars_isSupportConnected (A := A)
    hG1PI.isSupportConnected
    (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_isPairwiseDisjoint
      phi4DivergenceMeasureFamily G hA)
    (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_hasNonemptyComponents
      phi4DivergenceMeasureFamily G hA)
    (phi4CanonicalForestStarOf G A hA)

/-- **R-6c-QFT-R1-body-573 — 1PI (instance-free reconstruction).**  The whole no-bridge chain of the
polluted `admissibleForestCanonicalContractGraph_isOnePI_of_ambient_onePI` is reconstructed here
directly from the clean underlying lemmas: `mem_contractWithStars_internalEdges` pulls back a contracted
internal edge to an ambient complement edge, ambient 1PI supplies its non-bridgeness, and
`contractWithStars_eraseInternalEdge_isSupportConnected` transports the erased connectivity forward. -/
theorem phi4CanonicalForestContractGraph_isOnePI
    (hG1PI : G.IsOnePI) (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    (phi4CanonicalForestContractGraph G A hA).IsOnePI := by
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  refine ⟨phi4CanonicalForestContractGraph_isSupportConnected hG1PI A hA, ?_⟩
  intro e' he' hBridge
  rw [phi4CanonicalForestContractGraph_eq_contractWithStars] at he' hBridge
  obtain ⟨e, he, heq⟩ := AdmissibleSubgraph.mem_contractWithStars_internalEdges.mp he'
  have heG : e ∈ G.internalEdges := A.mem_ambientInternalEdges_of_mem_complementEdges he
  have hNoBridge : ¬ G.IsBridge e := hG1PI.no_bridge e heG
  have hGErase : (G.eraseInternalEdge e).IsSupportConnected := by
    by_contra hnot
    exact hNoBridge ⟨heG, hnot⟩
  have hRetargetErase :
      ((A.contractWithStars (phi4CanonicalForestStarOf G A hA)).eraseInternalEdge
        (A.retargetEdge (phi4CanonicalForestStarOf G A hA) e)).IsSupportConnected :=
    AdmissibleSubgraph.contractWithStars_eraseInternalEdge_isSupportConnected he hGErase
      (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_isPairwiseDisjoint
        phi4DivergenceMeasureFamily G hA)
      (FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_hasNonemptyComponents
        phi4DivergenceMeasureFamily G hA)
      (phi4CanonicalForestStarOf G A hA)
  rw [← heq] at hBridge
  exact hBridge.not_supportConnected_of_erase hRetargetErase

/-! ## Step 4 — assembled connected-divergence of the quotient -/

/-- **R-6c-QFT-R1-body-573 — the quotient is connected-divergent.**  Assembles the four facts
(well-formed / support-connected / 1PI / divergent) into the `∃`-form connected-divergence certificate
`toHopfGenFor` consumes.  Zero new physics. -/
theorem phi4CanonicalForestContractGraph_exists_self_isConnectedDivergent
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF))
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs) :
    ∃ hQWF : (phi4CanonicalForestContractGraph G A hA).WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (phi4CanonicalForestContractGraph G A hA)
        (phi4DivergenceMeasureFamily (phi4CanonicalForestContractGraph G A hA))
        (FeynmanSubgraph.self (phi4CanonicalForestContractGraph G A hA) hQWF) := by
  refine ⟨phi4CanonicalForestContractGraph_wellFormed hGWF A hA, ?_, ?_, ?_⟩
  · show (phi4CanonicalForestContractGraph G A hA).IsSupportConnected
    exact phi4CanonicalForestContractGraph_isSupportConnected hG1PI A hA
  · show (phi4CanonicalForestContractGraph G A hA).IsOnePI
    exact phi4CanonicalForestContractGraph_isOnePI hG1PI A hA
  · exact phi4CanonicalForestContractGraph_isDivergent_of_ambient hGWF A hA
      (phi4CanonicalForestContractGraph_wellFormed hGWF A hA) hGDiv

/-! ## Step 5 — the canonical φ⁴ forest quotient right generator -/

/-- **R-6c-QFT-R1-body-573 — the canonical φ⁴ forest quotient right factor `[G/A]`.**  Packages the
canonical forest contraction `G/A` as the strict φ⁴ generator `Phi4HopfGen` via body-566's
`toHopfGenFor`.  Consumes **no** forbidden divergence class. -/
noncomputable def AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    Phi4HopfGen :=
  (phi4CanonicalForestContractGraph G A hA).toHopfGenFor
    phi4DivergenceMeasureFamily phi4PermInvariantDivergenceMeasureFamily
    (phi4CanonicalForestContractGraph_exists_self_isConnectedDivergent hGWF hG1PI hGDiv A hA)

/-- **R-6c-QFT-R1-body-573 — right-factor value.**  The underlying class is
`(G/A).toClass` (`rfl`). -/
@[simp] theorem AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen_val
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    (A.canonicalForestContractToPhi4HopfGen hGWF hG1PI hA hGDiv).val =
      (phi4CanonicalForestContractGraph G A hA).toClass :=
  rfl

end GaugeGeometry.QFT.Combinatorial
