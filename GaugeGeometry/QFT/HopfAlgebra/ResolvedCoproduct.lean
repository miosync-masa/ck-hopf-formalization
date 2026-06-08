import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex

/-!
# Resolved coproduct summand (Track R-4-full, Phase 2c-ii)

The resolved analogue of a single CK coproduct summand for one resolved proper
forest `A`, defined through the Phase 2b/2c-i forget bridge.  We do **not** define
the full resolved coproduct sum yet, nor a resolved generator type.

**Design conclusion (Phase 2c-ii):** no `ResolvedHopfGen` is required for the
summand.  The flat summand API `admissibleForestStrictSummand` is generic over an
arbitrary `FeynmanGraph` together with an abstract right-generator assignment
`right`, and lands in the flat `HopfH ⊗ HopfH`.  So the resolved summand is simply
the flat summand of `A.forget`; the algebra carrier `HopfH` (flat generators) is
unchanged — the resolved structure is used only to discharge the boundary facades,
and resolved graphs forget to flat generators.  A resolved generator type would
only be needed for a *resolved carrier algebra*, which is not on this path.
-/

set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable {G : ResolvedFeynmanGraph}
variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
         [IsDivergencePreservedByAdmissibleForestContract]

namespace ResolvedAdmissibleSubgraph

/-- **Resolved single-forest coproduct summand, via `forget`.**  The flat strict
summand of the forgotten forest `A.forget`.  The right tensor factor is supplied
abstractly by `right` (a generator assignment over the flat proper-forest index of
`G.forget`); canonical stars are deferred to a later phase.  Lands in the flat
`HopfH ⊗ HopfH`. -/
noncomputable def strictSummandViaForget
    (A : ResolvedAdmissibleSubgraph G)
    (right : ∀ B : AdmissibleSubgraph G.forget,
      B ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs → HopfGen) :
    HopfH ⊗[ℚ] HopfH :=
  FeynmanGraph.admissibleForestStrictSummand G.forget right A.forget

/-- The resolved summand is, definitionally, the flat strict summand of the
forgotten forest — the Phase 2c-ii forget bridge for coproduct summands. -/
theorem strictSummandViaForget_eq
    (A : ResolvedAdmissibleSubgraph G)
    (right : ∀ B : AdmissibleSubgraph G.forget,
      B ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs → HopfGen) :
    A.strictSummandViaForget right =
      FeynmanGraph.admissibleForestStrictSummand G.forget right A.forget := rfl

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
