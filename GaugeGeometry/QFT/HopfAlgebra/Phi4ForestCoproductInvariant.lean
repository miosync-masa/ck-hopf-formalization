import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestQuotientRename
import GaugeGeometry.QFT.HopfAlgebra.Phi4CoproductInvariant

/-!
# QFT-R1-body-581 — forest summand + representative forest coproduct invariance

Bodies 574/578/579/580 assembled the representative-level φ⁴ **forest** coproduct
`coproductGen_forest_phi4` and the finished index rename `Equiv`, the left-aggregate rename equality,
and the quotient-graph class rename equality.  This body performs the PURE ALGEBRAIC WIRING that mirrors
body-570's connected `coproductGen_phi4_mapPerm` / `coproductGen_phi4_isomorphism_invariant`, transported
to the forest world: each forest summand is rename-stable, the forest sum reindexes along body-578's
`Equiv`, and the whole representative forest coproduct is invariant under vertex renaming and graph
isomorphism.

## Contents

* Step 1 `AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen_mapPermFor` — the right generator is
  rename-stable (`Subtype.ext` + val-simp + body-580).
* Step 2 `FeynmanGraph.phi4ForestStrictSummand_mapPermFor` — each forest summand `[A] ⊗ [Γ/A]` is
  rename-stable (left = body-579, right = `congrArg phi4Gen` of Step 1).
* Step 3 `FeynmanGraph.phi4ForestStrictSum_mapPermFor` — the forest sum reindexes along body-578's
  `Equiv` (`Finset.sum_bij`).
* Step 4 `FeynmanGraph.coproductGen_forest_phi4_mapPerm` — the full representative forest coproduct is
  rename-stable (mirror of body-570 Step 4/5).
* Step 5 `FeynmanGraph.coproductGen_forest_phi4_isomorphism_invariant` — the isomorphism corollary.

Per the HALT: no correcting-permutation reconstruction, no star / retarget / graph-field expansion, no
strict canonical-star equality, no `finite_visible_star_permutation`; no `Quotient.lift` / `Quotient.out`
/ `aeval` / class descent / counit / bialgebra / coassoc / W″; ZERO new `class` / `structure` /
`instance`; ZERO forbidden divergence classes in any type.  Everything is `Subtype.ext` +
proof-irrelevance + tensor/sum congruence over the finished bodies 570/578/579/580.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
variable {G : FeynmanGraph}

/-! ## Step 1 — the forest right generator is rename-stable -/

/-- **body-581 — the canonical φ⁴ forest quotient right generator `[Γ/A]` is rename-stable.**
`Subtype.ext` reduces the goal to a `.toClass` equality of the two `phi4CanonicalForestContractGraph`s,
closed by body-580.  All proof arguments enter proof-irrelevantly. -/
theorem AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen_mapPermFor
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    (A : {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G //
        A ∈ G.phi4ForestCoproductIndex}) :
    ((G.phi4ForestCoproductIndexEquiv π A).1).canonicalForestContractToPhi4HopfGen
        (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((G.mapPerm π).phi4ForestCoproductIndex_mem_properDisjoint
          (G.phi4ForestCoproductIndexEquiv π A).2)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
      = A.1.canonicalForestContractToPhi4HopfGen hWF h1PI
          (G.phi4ForestCoproductIndex_mem_properDisjoint A.2) hGDiv := by
  apply Subtype.ext
  simp only [AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen_val]
  exact phi4CanonicalForestContractGraph_mapPerm_toClass_eq hWF π A.1
    (G.phi4ForestCoproductIndex_mem_properDisjoint A.2) _

/-! ## Step 2 — each forest summand is rename-stable -/

/-- **body-581 — each φ⁴ forest coproduct summand `[A] ⊗ [Γ/A]` is rename-stable.**  Left factor via
body-579; right factor via `congrArg phi4Gen` of Step 1. -/
theorem FeynmanGraph.phi4ForestStrictSummand_mapPermFor
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF))
    (A : {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G //
        A ∈ G.phi4ForestCoproductIndex}) :
    (G.mapPerm π).phi4ForestStrictSummand (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
        (G.phi4ForestCoproductIndexEquiv π A).1 (G.phi4ForestCoproductIndexEquiv π A).2
      = G.phi4ForestStrictSummand hWF h1PI hGDiv A.1 A.2 := by
  rw [FeynmanGraph.phi4ForestStrictSummand_eq, FeynmanGraph.phi4ForestStrictSummand_eq]
  congr 1
  · exact G.phi4ForestCoproductIndexEquiv_left_eq π A
  · exact congrArg phi4Gen
      (AdmissibleSubgraph.canonicalForestContractToPhi4HopfGen_mapPermFor G π hWF h1PI hGDiv A)

/-! ## Step 3 — the forest sum reindexes along body-578's `Equiv` -/

/-- **body-581 — the φ⁴ forest coproduct sum reindexes along the rename `Equiv`.**  `Finset.sum_bij`
along body-578's `phi4ForestCoproductIndexEquiv`; per-term equality is Step 2. -/
theorem FeynmanGraph.phi4ForestStrictSum_mapPermFor
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    (∑ A ∈ (G.mapPerm π).phi4ForestCoproductIndex.attach,
        (G.mapPerm π).phi4ForestStrictSummand (FeynmanGraph.mapPerm_wellFormed hWF)
          ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
          ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv) A.1 A.2)
      = ∑ A ∈ G.phi4ForestCoproductIndex.attach,
          G.phi4ForestStrictSummand hWF h1PI hGDiv A.1 A.2 := by
  symm
  refine Finset.sum_bij (fun A _ => G.phi4ForestCoproductIndexEquiv π A) ?_ ?_ ?_ ?_
  · -- maps into
    intro A _
    exact Finset.mem_attach _ _
  · -- injective
    intro A₁ _ A₂ _ h
    exact (G.phi4ForestCoproductIndexEquiv π).injective h
  · -- surjective
    intro B _
    exact ⟨(G.phi4ForestCoproductIndexEquiv π).symm B, Finset.mem_attach _ _,
      Equiv.apply_symm_apply _ _⟩
  · -- per-term equality (Step 2)
    intro A _
    exact (FeynmanGraph.phi4ForestStrictSummand_mapPermFor G π hWF h1PI hGDiv A).symm

/-! ## Step 4 — the representative forest coproduct is rename-stable -/

set_option maxHeartbeats 1000000 in
/-- **body-581 — the representative-level φ⁴ forest coproduct is rename-stable.**  The two boundary
terms are equal via body-570 Step 1 (`toPhi4HopfGen_mapPerm`); the forest sum reindexes via Step 3. -/
theorem FeynmanGraph.coproductGen_forest_phi4_mapPerm
    (G : FeynmanGraph) (π : Equiv.Perm VertexId)
    (hWF : G.WellFormed) (h1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hWF)) :
    (G.mapPerm π).coproductGen_forest_phi4 (FeynmanGraph.mapPerm_wellFormed hWF)
        ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
        ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv)
      = G.coproductGen_forest_phi4 hWF h1PI hGDiv := by
  rw [FeynmanGraph.coproductGen_forest_phi4_eq, FeynmanGraph.coproductGen_forest_phi4_eq]
  have hgen :
      phi4Gen ((G.mapPerm π).toPhi4HopfGen (FeynmanGraph.mapPerm_wellFormed hWF)
          ((FeynmanGraph.mapPerm_isOnePI_iff π G).mpr h1PI)
          ((phi4_mapPerm_isDivergent_iff π (FeynmanSubgraph.self G hWF)).mpr hGDiv))
        = phi4Gen (G.toPhi4HopfGen hWF h1PI hGDiv) :=
    congrArg phi4Gen (FeynmanGraph.toPhi4HopfGen_mapPerm G π hWF h1PI hGDiv)
  rw [hgen, FeynmanGraph.phi4ForestStrictSum_mapPermFor G π hWF h1PI hGDiv]

/-- **body-581 — the representative-level φ⁴ forest coproduct is graph-isomorphism invariant.**
Obtains the renaming witness from `IsIso` and reduces to `coproductGen_forest_phi4_mapPerm`; the
well-formed / 1PI / divergence hypotheses for the two graphs enter proof-irrelevantly.  EXACT mirror of
body-570's `coproductGen_phi4_isomorphism_invariant`. -/
theorem FeynmanGraph.coproductGen_forest_phi4_isomorphism_invariant
    {G₁ G₂ : FeynmanGraph} (hIso : G₁.IsIso G₂)
    (hWF₁ : G₁.WellFormed) (h1PI₁ : G₁.IsOnePI)
    (hGDiv₁ : @FeynmanSubgraph.IsDivergent G₁ (phi4DivergenceMeasureFamily G₁)
      (FeynmanSubgraph.self G₁ hWF₁))
    (hWF₂ : G₂.WellFormed) (h1PI₂ : G₂.IsOnePI)
    (hGDiv₂ : @FeynmanSubgraph.IsDivergent G₂ (phi4DivergenceMeasureFamily G₂)
      (FeynmanSubgraph.self G₂ hWF₂)) :
    G₂.coproductGen_forest_phi4 hWF₂ h1PI₂ hGDiv₂ = G₁.coproductGen_forest_phi4 hWF₁ h1PI₁ hGDiv₁ := by
  obtain ⟨π, hπ⟩ := hIso
  subst hπ
  exact FeynmanGraph.coproductGen_forest_phi4_mapPerm G₁ π hWF₁ h1PI₁ hGDiv₁

end GaugeGeometry.QFT.Combinatorial
