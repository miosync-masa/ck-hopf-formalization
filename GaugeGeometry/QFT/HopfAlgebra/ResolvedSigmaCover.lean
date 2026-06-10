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

end GaugeGeometry.QFT.Combinatorial
