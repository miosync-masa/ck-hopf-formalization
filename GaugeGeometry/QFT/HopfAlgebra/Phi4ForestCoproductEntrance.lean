import GaugeGeometry.QFT.HopfAlgebra.Phi4ForestRightFactor

/-!
# QFT-R1-body-574 — representative φ⁴ forest coproduct entrance

Bodies 572–573 built the two halves of the genuine (forest) φ⁴ coproduct summand: the boundary-completed
left aggregate `A.toPhi4HopfH` and the canonical forest quotient right generator
`A.canonicalForestContractToPhi4HopfGen`.  This body wires them into a single forest tensor summand and
assembles the **representative-level** forest coproduct formula.  Nothing more: representative invariance,
class descent, `aeval`, and the unqualified `coproduct_phi4` are all deferred.

## Contents

* Step 1 `phi4ForestCoproductIndex` — the final forest index (proper-disjoint + ambient-properness
  `0 < |A.complementEdges|`) + membership accessors.
* Step 2 `phi4ForestStrictSummand` — the forest summand `A.toPhi4HopfH ⊗ [Γ/A]` (left = body-572,
  right = body-573; the same `hA` owner supplies the right factor's base membership) + `_eq` anchor.
* Step 3/4 `coproductGen_forest_phi4` — `[G] ⊗ 1 + 1 ⊗ [G] + ∑ over the attached forest index` +
  `_eq` unfold anchor.  The `attach` gives each summand its own membership certificate.

## Not claimed

Body-574 does **not** claim strict equality of the singleton-forest term with body-569's connected term:
the connected-contraction star and the canonical forest star may differ across presentations.  What later
bodies need is the *contracted graph class equality*, not strict star equality.

## Reaching

```text
final φ⁴ forest index      CONSTRUCTED
boundary-completed left    REUSE (572)
canonical quotient right   REUSE (573)
forest tensor summand      CONSTRUCTED
representative forest Δ     CONSTRUCTED
forest rename invariance    OPEN (575+)
class descent / aeval       NOT ENTERED
```

Per the HALT: no forest `mapPerm`; no canonical-star cross-presentation equality; no representative
invariance; no `Quotient.lift` / `aeval`; no unqualified `coproduct_phi4`; no counit / bialgebra / coassoc;
zero new `class`/`structure`/permanent `instance`; zero forbidden divergence classes.  The only instance
binder is the blanket `[∀ H, Fintype (FeynmanSubgraph H)]` — finite-sum infrastructure (needed so the quotient graph's Fintype resolves without reducing the deep forest-contraction term).
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

-- Finite-sum infrastructure as a blanket (so the quotient graph's Fintype is available without
-- reducing the deep forest-contraction term). NOT physics.
variable [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
variable {G : FeynmanGraph}

/-! ## Step 1 — final forest index -/

/-- **R-6c-QFT-R1-body-574 — the final φ⁴ forest coproduct index.**  Proper-disjoint admissible forests
with a nonempty complement (ambient properness), so `G/A` is a proper quotient. -/
noncomputable def FeynmanGraph.phi4ForestCoproductIndex
    (G : FeynmanGraph) :
    Finset (AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :=
  G.phi4ProperDisjointAdmissibleDivergentSubgraphs.filter
    (fun A => 0 < (@AdmissibleSubgraph.complementEdges G (phi4DivergenceMeasureFamily G) A).card)

@[simp] theorem FeynmanGraph.mem_phi4ForestCoproductIndex
    (G : FeynmanGraph)
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G) :
    A ∈ G.phi4ForestCoproductIndex ↔
      A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs ∧
        0 < (@AdmissibleSubgraph.complementEdges G (phi4DivergenceMeasureFamily G) A).card := by
  unfold FeynmanGraph.phi4ForestCoproductIndex
  simp

theorem FeynmanGraph.phi4ForestCoproductIndex_mem_properDisjoint
    (G : FeynmanGraph)
    {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G}
    (hA : A ∈ G.phi4ForestCoproductIndex) :
    A ∈ G.phi4ProperDisjointAdmissibleDivergentSubgraphs :=
  ((G.mem_phi4ForestCoproductIndex A).mp hA).1

theorem FeynmanGraph.phi4ForestCoproductIndex_complementEdges_pos
    (G : FeynmanGraph)
    {A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G}
    (hA : A ∈ G.phi4ForestCoproductIndex) :
    0 < (@AdmissibleSubgraph.complementEdges G (phi4DivergenceMeasureFamily G) A).card :=
  ((G.mem_phi4ForestCoproductIndex A).mp hA).2

/-! ## Step 2 — canonical forest summand -/

/-- **R-6c-QFT-R1-body-574 — the φ⁴ forest coproduct summand `[A] ⊗ [Γ/A]`.**  Left = body-572's
boundary-completed component-product aggregate; right = body-573's canonical forest quotient generator
(fed the base proper-disjoint membership read off the same `hA`). -/
noncomputable def FeynmanGraph.phi4ForestStrictSummand
    (G : FeynmanGraph)
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF))
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ForestCoproductIndex) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  A.toPhi4HopfH ⊗ₜ[ℚ]
    phi4Gen (A.canonicalForestContractToPhi4HopfGen hGWF hG1PI
      (G.phi4ForestCoproductIndex_mem_properDisjoint hA) hGDiv)

theorem FeynmanGraph.phi4ForestStrictSummand_eq
    (G : FeynmanGraph)
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF))
    (A : AdmissibleSubgraphFor phi4DivergenceMeasureFamily G)
    (hA : A ∈ G.phi4ForestCoproductIndex) :
    G.phi4ForestStrictSummand hGWF hG1PI hGDiv A hA =
      A.toPhi4HopfH ⊗ₜ[ℚ]
        phi4Gen (A.canonicalForestContractToPhi4HopfGen hGWF hG1PI
          (G.phi4ForestCoproductIndex_mem_properDisjoint hA) hGDiv) :=
  rfl

/-! ## Step 3/4 — representative forest coproduct -/

/-- **R-6c-QFT-R1-body-574 — the representative-level φ⁴ forest coproduct.**  `[G] ⊗ 1 + 1 ⊗ [G] +
∑ [A] ⊗ [Γ/A]` over the attached forest index (each summand owns its membership certificate).
Representative independence / class descent is deferred. -/
noncomputable def FeynmanGraph.coproductGen_forest_phi4
    (G : FeynmanGraph)
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    Phi4HopfH ⊗[ℚ] Phi4HopfH :=
  let genG := phi4Gen (G.toPhi4HopfGen hGWF hG1PI hGDiv)
  genG ⊗ₜ[ℚ] (1 : Phi4HopfH)
    + (1 : Phi4HopfH) ⊗ₜ[ℚ] genG
    + ∑ A ∈ G.phi4ForestCoproductIndex.attach,
        G.phi4ForestStrictSummand hGWF hG1PI hGDiv A.1 A.2

theorem FeynmanGraph.coproductGen_forest_phi4_eq
    (G : FeynmanGraph)
    (hGWF : G.WellFormed) (hG1PI : G.IsOnePI)
    (hGDiv : @FeynmanSubgraph.IsDivergent G (phi4DivergenceMeasureFamily G)
      (FeynmanSubgraph.self G hGWF)) :
    G.coproductGen_forest_phi4 hGWF hG1PI hGDiv =
      phi4Gen (G.toPhi4HopfGen hGWF hG1PI hGDiv) ⊗ₜ[ℚ] (1 : Phi4HopfH)
        + (1 : Phi4HopfH) ⊗ₜ[ℚ] phi4Gen (G.toPhi4HopfGen hGWF hG1PI hGDiv)
        + ∑ A ∈ G.phi4ForestCoproductIndex.attach,
            G.phi4ForestStrictSummand hGWF hG1PI hGDiv A.1 A.2 :=
  rfl

end GaugeGeometry.QFT.Combinatorial
