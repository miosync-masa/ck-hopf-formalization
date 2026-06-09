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

/-! ### Phase 3a — canonical star assignment via forget

The canonical star/contraction machinery for the *canonical* summand (Phase 3b)
lives on the flat side `A.forget`: the flat summand via forget consumes the flat
canonical star and the flat canonical contracted graph of `A.forget`, reusing the
existing flat canonical infrastructure.  `canonicalStarOfViaForget` is the resolved
star (the flat canonical star precomposed with `forget`), kept for the resolved
contraction; the flat-side `flatCanonicalStar` / `canonicalRightGraphViaForget` are
what Phase 3b actually uses. -/

/-- The flat canonical star assignment of the forgotten forest `A.forget`. -/
noncomputable def flatCanonicalStar (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) : FeynmanSubgraph G.forget → VertexId :=
  FeynmanGraph.admissibleForestCanonicalStarOf G.forget A.forget
    (A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hA)

/-- Resolved canonical star assignment, via `forget`: the flat canonical star
precomposed with the forgetful map on components. -/
noncomputable def canonicalStarOfViaForget (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) : ResolvedFeynmanSubgraph G → VertexId :=
  fun γ => A.flatCanonicalStar hA γ.forget

@[simp] theorem canonicalStarOfViaForget_def (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) (γ : ResolvedFeynmanSubgraph G) :
    A.canonicalStarOfViaForget hA γ = A.flatCanonicalStar hA γ.forget := rfl

/-- The flat canonical star of the forgotten forest is a fresh star assignment. -/
theorem flatCanonicalStar_isFreshStarAssignment (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) :
    A.forget.IsFreshStarAssignment (A.flatCanonicalStar hA) :=
  FeynmanGraph.admissibleForestCanonicalStarOf_isFreshStarAssignment G.forget A.forget
    (A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hA)

/-- Canonical right (contracted) graph for a resolved proper forest, via `forget`:
the flat canonical contraction of `A.forget`.  This is the right-tensor-factor
graph for the canonical summand (Phase 3b). -/
noncomputable def canonicalRightGraphViaForget (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) : FeynmanGraph :=
  FeynmanGraph.admissibleForestCanonicalContractGraph G.forget A.forget
    (A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hA)

/-- The canonical right graph is the flat canonical-star contraction of `A.forget`. -/
@[simp] theorem canonicalRightGraphViaForget_eq (A : ResolvedAdmissibleSubgraph G)
    (hA : A.IsProperForest) :
    A.canonicalRightGraphViaForget hA =
      (A.forget).contractWithStars (A.flatCanonicalStar hA) := rfl

end ResolvedAdmissibleSubgraph

/-! ## Phase 2d — resolved finite proper-forest index (Option C: finite payload)

There is no `Fintype (ResolvedFeynmanSubgraph G)` (no global resolved enumeration),
so we do not enumerate all resolved proper forests intrinsically.  Following the
project's facade/payload style, the summation index is an explicit finite payload:
a `Finset` of resolved admissible forests, each required to be proper.  Every
member forgets into the flat `forestCoproductProperForestIndex` filter (Phase 2c-i),
so the payload's forgetful image lands in the flat finite index. -/

/-- A finite index of resolved proper forests of `G` (Option C payload). -/
structure ResolvedProperForestFiniteIndex (G : ResolvedFeynmanGraph) where
  /-- The finite carrier of resolved admissible forests. -/
  carrier : Finset (ResolvedAdmissibleSubgraph G)
  /-- Every member is a proper forest. -/
  mem_proper : ∀ A ∈ carrier, A.IsProperForest

namespace ResolvedProperForestFiniteIndex

/-- Each member forgets into the flat proper-forest index filter
(`properDisjoint… ∩ {0 < complement}`) — the Phase 2c-i bridge applied pointwise. -/
theorem forget_mem_flat (I : ResolvedProperForestFiniteIndex G)
    {A : ResolvedAdmissibleSubgraph G} (hA : A ∈ I.carrier) :
    A.forget ∈ (G.forget.properDisjointAdmissibleDivergentSubgraphs).filter
      (fun B => 0 < B.complementEdges.card) :=
  A.forget_mem_properDisjoint_filter_complement (I.mem_proper A hA)

/-- **Resolved strict coproduct sum over a finite payload.**  Sum of the
per-forest summands (`strictSummandViaForget`) over the payload carrier, with a
shared abstract right-generator assignment.  Lands in the flat `HopfH ⊗ HopfH`. -/
noncomputable def strictCoproductSum (I : ResolvedProperForestFiniteIndex G)
    (right : ∀ B : AdmissibleSubgraph G.forget,
      B ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs → HopfGen) :
    HopfH ⊗[ℚ] HopfH :=
  ∑ A ∈ I.carrier, A.strictSummandViaForget right

@[simp] theorem strictCoproductSum_def (I : ResolvedProperForestFiniteIndex G)
    (right : ∀ B : AdmissibleSubgraph G.forget,
      B ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs → HopfGen) :
    I.strictCoproductSum right =
      ∑ A ∈ I.carrier, A.strictSummandViaForget right := rfl

/-- The empty payload gives the zero sum. -/
@[simp] theorem strictCoproductSum_empty
    (right : ∀ B : AdmissibleSubgraph G.forget,
      B ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs → HopfGen) :
    (⟨∅, by intro A hA; simp at hA⟩ : ResolvedProperForestFiniteIndex G).strictCoproductSum
      right = 0 := by
  simp [strictCoproductSum]

end ResolvedProperForestFiniteIndex

end GaugeGeometry.QFT.Combinatorial
