import GaugeGeometry.QFT.HopfAlgebra.ResolvedBoundaryRepairCertificate

/-!
# Resolved σ-cover spine, phase 1 (Track R-4-superfull, Step 6B)

The minimal resolved σ-cover objects needed to *state and prove* the resolved
counterpart of the flat cover-side promoted-leg lemma
(`forestQuotientForestSigmaForestCover_promotedComponent_externalLegs_le_plus`,
which in flat is a facade field, `promoted_externalLegs_le_plus`).

Per the B-i finding, the obstruction was never the inequality but the *construction*
of the σ-cover after boundary identities are forgotten.  In the resolved layer the
cover can be built so that the promoted-leg containment holds **by construction**:
we take the source-plus external legs to be the aggregate of the promoted components'
legs, and the containment is `single ≤ sum`.

This is the **external-legs-only** spine: we keep the `Plus` object as a leg multiset
(not yet a full subgraph with vertex/edge support).  Convention: legs are stored
*before* retarget, matching the flat consumer `η.externalLegs ≤ Plus.externalLegs`.

We use the vertex-set–abstracted form of `PromotedComponents`
(`…ByVertices`), so no resolved quotient-graph API is required yet.
-/

set_option linter.unusedSectionVars false

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

/-- **Resolved promoted components (vertex-abstracted).**  The outer-forest
components whose star vertex lands inside the source vertex set `δVertices` — the
resolved analogue of the flat `PromotedComponents`, with `δ` abstracted to its
vertex set (so no resolved quotient-graph type is needed yet). -/
noncomputable def resolvedPromotedComponentsByVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (δVertices : Finset VertexId) :
    Finset (ResolvedFeynmanSubgraph G) :=
  Aout.elements.filter (fun η => starOf η ∈ δVertices)

@[simp] theorem mem_resolvedPromotedComponentsByVertices
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (δVertices : Finset VertexId)
    {η : ResolvedFeynmanSubgraph G} :
    η ∈ resolvedPromotedComponentsByVertices Aout starOf δVertices ↔
      η ∈ Aout.elements ∧ starOf η ∈ δVertices := by
  classical
  unfold resolvedPromotedComponentsByVertices
  exact Finset.mem_filter

/-- **Resolved source-plus external legs (minimal external-legs spine).**  The
aggregate external legs of the promoted components — the leg multiset the `Plus`
object must dominate.  Built so promoted-leg containment is structural. -/
noncomputable def resolvedSourceExactPlusExternalLegs
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (δVertices : Finset VertexId) :
    Multiset ResolvedExternalLeg :=
  (resolvedPromotedComponentsByVertices Aout starOf δVertices).sum
    (fun η => η.externalLegs)

/-- **Resolved promoted-leg containment** (the B-i facade content, now a theorem).
A promoted component's external legs are contained in the source-plus external legs.
Structural — `single ≤ sum`; no identity-uniqueness needed. -/
theorem resolved_promotedComponent_externalLegs_le_plus
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId) (δVertices : Finset VertexId)
    {η : ResolvedFeynmanSubgraph G}
    (hη : η ∈ resolvedPromotedComponentsByVertices Aout starOf δVertices) :
    η.externalLegs ≤ resolvedSourceExactPlusExternalLegs Aout starOf δVertices :=
  Finset.single_le_sum (fun _ _ => Multiset.zero_le _) hη

/-! ## Step 6(A) — resolved insertion injOn packaging

The resolved replacement for the flat forest-branch injectivity consumer
`forestComponentForestChoiceParentRemnantBare_injOn`: a *direct wrapper* of
`parent_eq_of_remainder_eq`.

Note on `hV`: the source-vertex equality `γ₁.vertices = γ₂.vertices` **cannot** be
recovered locally from the remnant equality, because the quotient vertices are
`γ.vertices.image (Aout.retargetVertex starOf)` and `retargetVertex` collapses each
component to its star (non-injective).  In flat, the recovery comes from a separate
σ-index construction (B-forest-2a, remnant-source-vertices); here `hV` stays an
explicit premise to be supplied by the resolved σ-index later. -/

/-- Resolved parent-remnant map: the quotient/remainder of a parent subgraph through
the outer forest. Mirrors the flat `ParentRemnant`. -/
noncomputable def resolvedParentRemnant
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (γ : ResolvedFeynmanSubgraph G) :
    ResolvedFeynmanSubgraph (Aout.contractWithStars starOf) :=
  Aout.quotientRemainderSubgraph starOf γ

/-- **Resolved insertion injectivity (Finset form).**  On a set `S` of parent
subgraphs whose pairwise-equal remnants force equal source vertices (`hV`) and which
all contain `Aout`'s edges (`hA`), the parent-remnant map is injective — the resolved
replacement for the flat `forestComponentForestChoiceParentRemnantBare_injOn`, here a
direct wrapper of `parent_eq_of_remainder_eq`. -/
theorem resolvedParentRemnant_injOn_finset
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique)
    {S : Finset (ResolvedFeynmanSubgraph G)}
    (hV : ∀ γ₁ ∈ S, ∀ γ₂ ∈ S,
        resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂ →
        γ₁.vertices = γ₂.vertices)
    (hA : ∀ γ ∈ S, Aout.internalEdges ≤ γ.internalEdges)
    {γ₁ γ₂ : ResolvedFeynmanSubgraph G} (hγ₁ : γ₁ ∈ S) (hγ₂ : γ₂ ∈ S)
    (hRem : resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂) :
    γ₁ = γ₂ :=
  Aout.parent_eq_of_remainder_eq hEdgeId hLegId starOf
    (hV γ₁ hγ₁ γ₂ hγ₂ hRem) (hA γ₁ hγ₁) (hA γ₂ hγ₂) hRem

/-- **Resolved insertion injectivity (`Set.InjOn` form).** -/
theorem resolvedParentRemnant_injOn
    (Aout : ResolvedAdmissibleSubgraph G)
    (starOf : ResolvedFeynmanSubgraph G → VertexId)
    (hEdgeId : G.EdgeIdsUnique) (hLegId : G.LegIdsUnique)
    {S : Finset (ResolvedFeynmanSubgraph G)}
    (hV : ∀ γ₁ ∈ S, ∀ γ₂ ∈ S,
        resolvedParentRemnant Aout starOf γ₁ = resolvedParentRemnant Aout starOf γ₂ →
        γ₁.vertices = γ₂.vertices)
    (hA : ∀ γ ∈ S, Aout.internalEdges ≤ γ.internalEdges) :
    Set.InjOn (resolvedParentRemnant Aout starOf) ↑S := by
  intro γ₁ hγ₁ γ₂ hγ₂ hRem
  exact resolvedParentRemnant_injOn_finset Aout starOf hEdgeId hLegId hV hA
    (Finset.mem_coe.mp hγ₁) (Finset.mem_coe.mp hγ₂) hRem

end GaugeGeometry.QFT.Combinatorial
