import GaugeGeometry.QFT.HopfAlgebra.ResolvedBoundaryCompletedSubgraph

/-!
# QFT-R1-body-590 — resolved forest left aggregate + rename invariance

Body-589 built the resolved left-component generator `toResolvedPhi4HopfGenBoundaryCompleted` (the
boundary-ID-completed component, landing in `ResolvedPhi4HopfGen`).  This body is the **resolved mirror of
body-579**: it assembles the per-component generators into the forest-level left aggregate
`ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH` and proves that aggregate rename-invariant.  Pure algebraic
wiring — no even/odd ID geometry / traceability is re-opened, no star / correcting permutation, no right
term / tensor summand / coproduct.

## Contents

* Step 1 `boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent` — the component-CD adapter: from
  `γ.forget.IsConnectedDivergent`, the *completed* forgotten graph's self-CD, via body-568 + body-589's
  strict forget equality.  Zero new physics.
* Step 2 `mapPermRFS_toResolvedPhi4HopfGenBoundaryCompleted` — one component's resolved left generator is
  rename-invariant (`Subtype.ext` + body-589 `boundaryCompletedResolvedGraph_mapPerm` +
  `toResolvedClass_mapPerm`; CD witnesses proof-irrelevant).
* Step 3 `ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH` — the forest left aggregate (product over the
  `.attach` of the components; lands in `ResolvedPhi4HopfH`).
* Step 4 `ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH_mapPermFor` — the aggregate is rename-invariant,
  via a `Finset.prod_bij` over the two `.attach` products (body-579's resolved mirror).  No W″ membership
  hypothesis is needed — it holds for *any* family-indexed resolved admissible forest.

Per the HALT: no right term / tensor summand / coproduct / `aeval`; no Measure / E / rep*; no W″ coassoc
migration; no star / correcting permutation; no even/odd ID geometry re-proof; zero new
`class`/`structure`/`instance`; zero forbidden divergence classes; no multiplicity collapse (the `.attach`
product keeps each component's membership certificate).  The target is always `ResolvedPhi4HopfH`.
-/

open scoped Classical

namespace GaugeGeometry.QFT.Combinatorial

namespace ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-! ## Step 1 — component-CD adapter -/

/-- **body-590 (Step 1) — the completed forgotten graph is connected-divergent** (`∃`-form), from the
component's `forget`-CD.  Body-568's flat completion CD pulled back along body-589's strict forget equality
`γ.boundaryCompletedResolvedGraph.forget = γ.forget.boundaryCompletedGraph`.  No topology / degree re-proof. -/
theorem boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent (γ : ResolvedFeynmanSubgraph G)
    (hγCD : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
      γ.forget) :
    ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF) := by
  rw [γ.boundaryCompletedResolvedGraph_forget]
  exact γ.forget.boundaryCompletedGraph_exists_self_isConnectedDivergent hγCD

/-! ## Step 2 — one-component rename invariance -/

/-- **body-590 (Step 2) — the resolved left-component generator is rename-invariant.**  `Subtype.ext`
reduces to `(mapPerm σ)`-invariance of `boundaryCompletedResolvedGraph.toResolvedClass`; body-589's
`boundaryCompletedResolvedGraph_mapPerm` + `toResolvedClass_mapPerm` close it.  CD witnesses enter
proof-irrelevantly; even/odd encoding / traceability are not unfolded. -/
theorem mapPermRFS_toResolvedPhi4HopfGenBoundaryCompleted
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (γ : ResolvedFeynmanSubgraph G₁)
    (hγCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF))
    (hγCDσ : ∃ hWF : (mapPermRFS hσ γ).boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (mapPermRFS hσ γ).boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily (mapPermRFS hσ γ).boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self (mapPermRFS hσ γ).boundaryCompletedResolvedGraph.forget hWF)) :
    (mapPermRFS hσ γ).toResolvedPhi4HopfGenBoundaryCompleted hγCDσ
      = γ.toResolvedPhi4HopfGenBoundaryCompleted hγCD := by
  subst hσ
  apply Subtype.ext
  -- `mapPermRFS rfl γ` reduces to `γ.mapPerm σ`; the `.val`s are the completed-graph resolved classes.
  show (γ.mapPerm σ).boundaryCompletedResolvedGraph.toResolvedClass
    = γ.boundaryCompletedResolvedGraph.toResolvedClass
  rw [boundaryCompletedResolvedGraph_mapPerm]
  exact ResolvedFeynmanGraph.toResolvedClass_mapPerm _ _

end ResolvedFeynmanSubgraph

namespace ResolvedAdmissibleSubgraph

/-! ## Step 3 — the resolved forest left aggregate -/

/-- **body-590 (Step 3) — the resolved boundary-completed forest left aggregate.**  The product of the
per-component resolved left generators (body-589) over the forest's `.attach` — each component carries its
own membership certificate (no dedup, no flat generator, no raw `toFeynmanGraph`).  Lands in
`ResolvedPhi4HopfH`. -/
noncomputable def toResolvedPhi4HopfH {G : ResolvedFeynmanGraph}
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G) : ResolvedPhi4HopfH := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  exact ∏ γ ∈ A.elements.attach, (MvPolynomial.X
    (γ.1.toResolvedPhi4HopfGenBoundaryCompleted
      (γ.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
        (A.isConnectedDivergent γ.1 γ.2))) : ResolvedPhi4HopfH)

/-! ## Step 4 — aggregate rename invariance -/

/-- **body-590 (Step 4, TARGET) — the resolved forest left aggregate is rename-invariant.**  The product
over the components of a renamed admissible forest equals the product over the original.  Componentwise
Step 2 through a `Finset.prod_bij` on the two `.attach` products (body-579's resolved mirror); the
CD-witness alignment inside each summand is proof-irrelevance.  No W″ membership hypothesis. -/
theorem toResolvedPhi4HopfH_mapPermFor
    {G₁ G₂ : ResolvedFeynmanGraph} {σ : Equiv.Perm VertexId} (hσ : G₂ = G₁.mapPerm σ)
    (A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G₁) :
    (mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily hσ A).toResolvedPhi4HopfH = A.toResolvedPhi4HopfH := by
  classical
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  set B := mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily hσ A with hB
  -- membership transport `A.elements → B.elements`
  have hmem : ∀ (γ : ResolvedFeynmanSubgraph G₁), γ ∈ A.elements → mapPermRFS hσ γ ∈ B.elements := by
    intro γ hγ
    rw [hB, mapPermResolvedAdmissibleSubgraphFor_elements]
    exact Finset.mem_image.mpr ⟨γ, hγ, rfl⟩
  symm
  simp only [toResolvedPhi4HopfH]
  refine Finset.prod_bij
    (fun (γ : {x // x ∈ A.elements}) _ => (⟨mapPermRFS hσ γ.1, hmem γ.1 γ.2⟩ :
      {x // x ∈ B.elements}))
    (fun _ _ => Finset.mem_attach _ _)
    ?_ ?_ ?_
  · -- injective
    intro γ₁ _ γ₂ _ heq
    have h1 : mapPermRFS hσ γ₁.1 = mapPermRFS hσ γ₂.1 := congrArg Subtype.val heq
    exact Subtype.ext (mapPermRFS_injective hσ h1)
  · -- surjective
    intro b _
    obtain ⟨bv, hbv⟩ := b
    rw [hB, mapPermResolvedAdmissibleSubgraphFor_elements] at hbv
    rcases Finset.mem_image.mp hbv with ⟨γ, hγ, hγeq⟩
    exact ⟨⟨γ, hγ⟩, Finset.mem_attach _ _, Subtype.ext hγeq⟩
  · -- summand equality (Step 2, componentwise)
    intro γ _
    exact congrArg (fun g => (MvPolynomial.X g : ResolvedPhi4HopfH))
      (ResolvedFeynmanSubgraph.mapPermRFS_toResolvedPhi4HopfGenBoundaryCompleted hσ γ.1
        (γ.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
          (A.isConnectedDivergent γ.1 γ.2))
        ((mapPermRFS hσ γ.1).boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
          (B.isConnectedDivergent (mapPermRFS hσ γ.1) (hmem γ.1 γ.2)))).symm

end ResolvedAdmissibleSubgraph

end GaugeGeometry.QFT.Combinatorial
