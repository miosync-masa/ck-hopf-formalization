import GaugeGeometry.QFT.HopfAlgebra.Phi4CoproductClass

/-!
# QFT-R1-body-572 — family-indexed φ⁴ forest carrier + left aggregate

`Forest G` and `AdmissibleSubgraph G` carry `[DivergenceMeasure G]` as a *type* parameter, so the old
forest API would re-introduce the "measure-family ownership loss" that body-564 removed — at the type
level.  This body returns that ownership to the type before touching any forest mathematics: it applies the
existing (pure) forest types and carrier to an explicit family member `D G`, and builds the
boundary-completed left forest aggregate.  No new structures; `rigidify ownership before summation`.

## Contents

* Step 1 `ForestFor` / `AdmissibleSubgraphFor` — the existing types at an explicit family member.
* Step 2 `properDisjointAdmissibleDivergentSubgraphsFor` — the existing proper-disjoint carrier specialized
  to `D G`, with its five accessors + `phi4…` specialization.
* Step 3 `AdmissibleSubgraph.toPhi4HopfH` — the boundary-completed left forest aggregate
  (`∏` of body-568 component generators; component boundary multiplicity preserved).
* Step 4 anchors: `empty ↦ 1`, `singleton {γ} ↦ phi4Gen (γ.toPhi4HopfGen hγ)`, component factor.

The only instance binder is `[∀ G, Fintype (FeynmanSubgraph G)]` — finite-sum infrastructure.

Per the HALT (safe-stop this body): no canonical-forest-contraction right generator; no forest summand /
representative forest coproduct / mapPerm forest reindex; no class descent / `aeval`; no counit / coassoc /
bialgebra.  Zero old `HopfH` factors; zero forbidden divergence classes; zero new `class`/`structure`/
permanent `instance`; zero raw boundary-forgetting left generators; no forest-contraction preservation
class.  (`letI := D G` is used only locally where dot-notation accessors need the measure — never a
permanent instance.)
-/

namespace GaugeGeometry.QFT.Combinatorial

variable {G : FeynmanGraph}

/-! ## Step 1 — explicit-family forest types -/

/-- The `Forest` type at an explicit divergence-measure family member (no blanket instance). -/
abbrev ForestFor (D : DivergenceMeasureFamily) (G : FeynmanGraph) : Type := @Forest G (D G)

/-- The `AdmissibleSubgraph` type at an explicit divergence-measure family member. -/
abbrev AdmissibleSubgraphFor (D : DivergenceMeasureFamily) (G : FeynmanGraph) : Type :=
  @AdmissibleSubgraph G (D G)

/-! ## Step 2 — family-indexed proper forest carrier -/

/-- **R-6c-QFT-R1-body-572 — proper-disjoint admissible carrier for an explicit family.**  The existing
pure carrier, specialized to `D G` (no blanket `[DivergenceMeasure G]`). -/
noncomputable def FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraphFor D G) :=
  @FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs G (D G) _

theorem FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphsFor
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    (A : AdmissibleSubgraphFor D G) :
    A ∈ G.properDisjointAdmissibleDivergentSubgraphsFor D ↔
      A ∈ @FeynmanGraph.nonemptyDisjointAdmissibleDivergentSubgraphs G (D G) _ ∧
        @AdmissibleSubgraph.HasNonemptyComponents G (D G) A ∧
        0 < (@AdmissibleSubgraph.internalEdges G (D G) A).card ∧
        @AdmissibleSubgraph.HasPositiveInternalEdgesComponents G (D G) A :=
  @FeynmanGraph.mem_properDisjointAdmissibleDivergentSubgraphs G (D G) _ A

theorem FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_isPairwiseDisjoint
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraphFor D G} (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphsFor D) :
    @AdmissibleSubgraph.IsPairwiseDisjoint G (D G) A :=
  @FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint G (D G) _ A hA

theorem FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_hasNonemptyComponents
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraphFor D G} (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphsFor D) :
    @AdmissibleSubgraph.HasNonemptyComponents G (D G) A :=
  @FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents G (D G) _ A hA

theorem FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_hasPositiveInternalEdgesComponents
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraphFor D G} (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphsFor D) :
    @AdmissibleSubgraph.HasPositiveInternalEdgesComponents G (D G) A :=
  @FeynmanGraph.properDisjointAdmissibleDivergentSubgraphs_hasPositiveInternalEdgesComponents G (D G) _ A hA

theorem FeynmanGraph.properDisjointAdmissibleDivergentSubgraphsFor_internalEdges_pos
    (D : DivergenceMeasureFamily) (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)]
    {A : AdmissibleSubgraphFor D G} (hA : A ∈ G.properDisjointAdmissibleDivergentSubgraphsFor D) :
    0 < (@AdmissibleSubgraph.internalEdges G (D G) A).card :=
  (((G.mem_properDisjointAdmissibleDivergentSubgraphsFor D A).mp hA).2).2.1

/-- The φ⁴ specialization of the proper-disjoint admissible carrier. -/
noncomputable def FeynmanGraph.phi4ProperDisjointAdmissibleDivergentSubgraphs
    (G : FeynmanGraph) [Fintype (FeynmanSubgraph G)] :
    Finset (AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :=
  G.properDisjointAdmissibleDivergentSubgraphsFor phi4DivergenceMeasureFamily

/-! ## Step 3 — boundary-completed left forest factor -/

/-- **R-6c-QFT-R1-body-572 — boundary-completed left forest aggregate.**  The product of the
boundary-completed (body-568) left generators of the components — `attach` carries each component's
membership certificate; component boundary multiplicity is preserved (no dedup).  Raw
`γ.toFeynmanGraph.toClass` is never used. -/
noncomputable def AdmissibleSubgraph.toPhi4HopfH
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) : Phi4HopfH :=
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  ∏ γ ∈ A.elements.attach, phi4Gen (γ.1.toPhi4HopfGen (A.isConnectedDivergent_of_mem γ.2))

/-! ## Step 4 — anchors -/

@[simp] theorem AdmissibleSubgraph.empty_toPhi4HopfH (G : FeynmanGraph) :
    (@AdmissibleSubgraph.empty G (phi4DivergenceMeasureFamily G)).toPhi4HopfH = 1 := by
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  simp only [AdmissibleSubgraph.toPhi4HopfH, AdmissibleSubgraph.empty_elements,
    Finset.attach_empty, Finset.prod_empty]

@[simp] theorem AdmissibleSubgraph.singleton_toPhi4HopfH (γ : FeynmanSubgraph G)
    (hγ : @FeynmanSubgraph.IsConnectedDivergent G (phi4DivergenceMeasureFamily G) γ) :
    (@AdmissibleSubgraph.singleton G (phi4DivergenceMeasureFamily G) γ hγ).toPhi4HopfH
      = phi4Gen (γ.toPhi4HopfGen hγ) := by
  letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
  simp only [AdmissibleSubgraph.toPhi4HopfH, AdmissibleSubgraph.singleton_elements]
  rw [Finset.prod_eq_single_of_mem ⟨γ, Finset.mem_singleton_self γ⟩ (Finset.mem_attach _ _)]
  · intro b _ hb
    exact absurd (Subtype.ext (Finset.mem_singleton.mp b.2)) hb

/-- **R-6c-QFT-R1-body-572 — the component factor.**  Each component of the forest contributes its
boundary-completed generator to the aggregate product. -/
theorem AdmissibleSubgraph.toPhi4HopfH_component_factor
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    A.toPhi4HopfH =
      letI : DivergenceMeasure G := phi4DivergenceMeasureFamily G
      ∏ γ ∈ A.elements.attach, phi4Gen (γ.1.toPhi4HopfGen (A.isConnectedDivergent_of_mem γ.2)) :=
  rfl

end GaugeGeometry.QFT.Combinatorial
