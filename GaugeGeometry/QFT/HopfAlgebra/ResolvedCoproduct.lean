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

/-! ### Phase 3b — right HopfGen via forget + canonical summand

`hCD` is the global canonical-contraction connected-divergence hypothesis over
`G.forget`, taken as a parameter exactly as in the flat
`admissibleForestStrictSummandWithCanonicalStars` interface (not discharged from
the ambient power-counting here).  The canonical right generator and summand are
then the flat canonical ones of `A.forget`. -/

/-- The canonical contracted graph of a resolved proper forest is connected
divergent — by the supplied global hypothesis `hCD`. -/
theorem canonicalRightGraphViaForget_isConnectedDivergent
    (A : ResolvedAdmissibleSubgraph G) (hA : A.IsProperForest)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    (A.canonicalRightGraphViaForget hA).IsConnectedDivergent := by
  unfold canonicalRightGraphViaForget
  rw [FeynmanGraph.admissibleForestCanonicalContractGraph_eq]
  exact hCD A.forget (A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hA)

/-- The right tensor generator for a resolved proper forest, via `forget`: the flat
canonical right HopfGen of `A.forget`. -/
noncomputable def rightHopfGenViaForget
    (A : ResolvedAdmissibleSubgraph G) (hA : A.IsProperForest)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    HopfGen :=
  FeynmanGraph.admissibleForestRightWithCanonicalStars G.forget hCD A.forget
    (A.forget_mem_properDisjointAdmissibleDivergentSubgraphs hA)

/-- The canonical strict coproduct summand of a resolved proper forest, via
`forget`: specialize `strictSummandViaForget` with the flat canonical right
assignment.  Equals the flat canonical summand of `A.forget`. -/
noncomputable def strictSummandCanonicalViaForget
    (A : ResolvedAdmissibleSubgraph G)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  A.strictSummandViaForget (FeynmanGraph.admissibleForestRightWithCanonicalStars G.forget hCD)

@[simp] theorem strictSummandCanonicalViaForget_eq
    (A : ResolvedAdmissibleSubgraph G)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    A.strictSummandCanonicalViaForget hCD =
      FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars G.forget hCD A.forget := rfl

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

/-- **Canonical resolved strict coproduct sum over a finite payload.**  Sum of the
canonical per-forest summands (`strictSummandCanonicalViaForget`) over the payload
carrier, with the shared global canonical-contraction CD hypothesis `hCD`.  Each
summand equals the flat canonical summand of `A.forget`. -/
noncomputable def strictCoproductSumCanonical (I : ResolvedProperForestFiniteIndex G)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    HopfH ⊗[ℚ] HopfH :=
  ∑ A ∈ I.carrier, A.strictSummandCanonicalViaForget hCD

@[simp] theorem strictCoproductSumCanonical_def (I : ResolvedProperForestFiniteIndex G)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    I.strictCoproductSumCanonical hCD =
      ∑ A ∈ I.carrier, A.strictSummandCanonicalViaForget hCD := rfl

end ResolvedProperForestFiniteIndex

/-! ## Phase 3c — resolved finite index cover laws

A cover wraps a finite payload with the two laws that make its forgetful image
*exactly* the flat proper-forest index: `forget_complete` (every flat proper forest
is hit) and `forget_injective` (no two payload members collapse to the same flat
forest).  Together they reindex the canonical resolved coproduct sum onto the flat
coproduct body sum. -/

/-- A finite payload of resolved proper forests whose forgetful image is exactly
the flat proper-forest index of `G.forget`. -/
structure ResolvedProperForestFiniteCover (G : ResolvedFeynmanGraph) where
  /-- The underlying finite payload. -/
  index : ResolvedProperForestFiniteIndex G
  /-- Surjectivity: every flat proper forest is the forget of some payload member. -/
  forget_complete :
    ∀ Aflat ∈ (G.forget.properDisjointAdmissibleDivergentSubgraphs).filter
        (fun A => 0 < A.complementEdges.card),
      ∃ Ares ∈ index.carrier, Ares.forget = Aflat
  /-- Injectivity: no two payload members forget to the same flat forest. -/
  forget_injective :
    ∀ A₁ ∈ index.carrier, ∀ A₂ ∈ index.carrier,
      A₁.forget = A₂.forget → A₁ = A₂

namespace ResolvedProperForestFiniteCover

/-- The forgetful image of the payload carrier is exactly the flat proper-forest
index filter. -/
theorem forget_image_eq_flatIndex (C : ResolvedProperForestFiniteCover G) :
    C.index.carrier.image (fun A => A.forget) =
      (G.forget.properDisjointAdmissibleDivergentSubgraphs).filter
        (fun A => 0 < A.complementEdges.card) := by
  apply Finset.ext
  intro Aflat
  constructor
  · intro h
    obtain ⟨Ares, hAres, rfl⟩ := Finset.mem_image.mp h
    exact C.index.forget_mem_flat hAres
  · intro h
    obtain ⟨Ares, hAres, heq⟩ := C.forget_complete Aflat h
    exact Finset.mem_image.mpr ⟨Ares, hAres, heq⟩

/-- **Cover reindex (Phase 3c headline).**  The canonical resolved coproduct sum
over the payload equals the flat coproduct body sum over the flat proper-forest
index.  Pure Finset reindexing: each summand is the flat canonical summand of
`A.forget`, the carrier forgets injectively onto the flat index. -/
theorem strictCoproductSumCanonical_eq_flat (C : ResolvedProperForestFiniteCover G)
    (hCD : ∀ B : AdmissibleSubgraph G.forget,
      ∀ hB : B ∈ G.forget.properDisjointAdmissibleDivergentSubgraphs,
        (FeynmanGraph.admissibleForestContractGraphWithStars G.forget B
          (FeynmanGraph.admissibleForestCanonicalStarOf G.forget B hB)).IsConnectedDivergent) :
    C.index.strictCoproductSumCanonical hCD =
      ∑ Aflat ∈ (G.forget.properDisjointAdmissibleDivergentSubgraphs).filter
          (fun A => 0 < A.complementEdges.card),
        FeynmanGraph.admissibleForestStrictSummandWithCanonicalStars G.forget hCD Aflat := by
  rw [ResolvedProperForestFiniteIndex.strictCoproductSumCanonical_def]
  simp only [ResolvedAdmissibleSubgraph.strictSummandCanonicalViaForget_eq]
  rw [← C.forget_image_eq_flatIndex,
    Finset.sum_image (fun A₁ h₁ A₂ h₂ h => C.forget_injective A₁ h₁ A₂ h₂ h)]

end ResolvedProperForestFiniteCover

end GaugeGeometry.QFT.Combinatorial
