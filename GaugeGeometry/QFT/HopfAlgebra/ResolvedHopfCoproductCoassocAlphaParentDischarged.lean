import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaRemainderDelta
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentReflectionAudit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaTouchedStarDescent
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentOnePI
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedFinal
import GaugeGeometry.QFT.HopfAlgebra.Coassoc

/-!
# R-6c-body-556 — the FINAL Parent discharge: `Parent` GONE, final coassoc keyed only to `Measure` / `E` / `rep*`

Five-hundred-and-fifty-sixth genuine-body step — the **capstone** of the Parent-elimination campaign.  It is a **pure
composition** of bodies 549–555 with the **already-existing** divergence-reflection law
`IsDivergenceReflectedByAdmissibleForestContract`; **NO new proof principle** is introduced.

The chain closes the last honest external physics input `Parent :
ResolvedCanonicalLegSaturatedDecontractionCDSupply`:

```text
Step 1  intrinsic divergence transport  (generic; ambient-invariant `.toFeynmanGraph` reader)
Step 2  canonical remainder divergent    (body-555 intrinsic remainder = δ  ⟹  remainder IsDivergent)
Step 3  reflection APPLIED ONCE          (body-553 adapter ⟹ parent self-subgraph IsDivergent)
Step 4  parentDivergent                  (Step 3 back-transported through Step 1)
Step 5  parent IsConnectedDivergent      (body-552 topology twin + Step 4 divergence)
Step 6  canonicalLegSaturatedDecontractionCDSupply : the SINGLE Parent supply (a `def`, NOT an instance)
Step 7  coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged : final wrapper, NO explicit `Parent` input
```

★The reflection class field is consumed **EXACTLY ONCE** — at Step 3, through body-553's public adapter
`admissibleSubgraphQuotientRemainder_divergent_reflect`.★  ★Steps 1–5 are **STRICTLY** Parent-free: no
`ResolvedCanonicalLegSaturatedAlphaConstructionSupply`, no `R`, no `R.Core`, no `Parent` input.★  Only Step 6 issues the
`Parent` supply; only Step 7 consumes it — exactly once each.  body-546 is UNCHANGED.

This body does **not** "delete a physics law": it **proves** that `Parent` is the canonical resolved *consequence* of the
existing divergence-reflection law, thereby removing the duplicated external input.  The result is
**CK-physics-typeclass-modulo** (it retains `IsDivergenceReflectedByAdmissibleForestContract` and the other ambient
divergence typeclasses as instance arguments); it is **NOT** unconditional.

## Final ledger

```text
Parent topology                 DERIVED (549–552)
star descent                    DERIVED (554)
remainder intrinsic equality    DERIVED (555)
parent divergence               DERIVED FROM EXISTING REFLECTION (556, reflection consumed once)
Parent aggregate                CANONICAL CONSTRUCTED (canonicalLegSaturatedDecontractionCDSupply, a def)
explicit Parent input           GONE
final explicit roots            Measure / E / rep* (CK-physics-typeclass-modulo, incl. IsDivergenceReflectedByAdmissibleForestContract; NOT unconditional)
```

Per the HALT/guards: Steps 1–5 Parent-free (no `R`/`Core`/`Parent` input); Step 6 is a `def`, NOT an `instance`; NO new
`class`/`structure`/`instance`; reflection consumed EXACTLY ONCE (Step 3); NO `HEq`/`cast`; body-546 UNCHANGED; the result
is NOT called unconditional.  No facade, no `sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]
  [IsDivergenceReflectedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Step 1 — intrinsic divergence transport (PUBLIC generic, Parent-free). -/

/-- **R-6c-body-556 (Step 1, helper) — self-subgraph degrees agree across an intrinsic-graph equality.**  For two graphs
`K₁ = K₂` (each well-formed), their self-subgraphs have equal divergence degree.  `subst` on the graph equality collapses
the two ambients; the two well-formedness witnesses coincide by proof irrelevance (`rfl`).  ★NO `HEq`/`cast`.★ -/
private theorem degree_self_eq_of_graph_eq
    {K₁ K₂ : FeynmanGraph} (hWF₁ : K₁.WellFormed) (hWF₂ : K₂.WellFormed) (hK : K₂ = K₁) :
    DivergenceMeasure.degree (FeynmanSubgraph.self K₂ hWF₂)
      = DivergenceMeasure.degree (FeynmanSubgraph.self K₁ hWF₁) := by
  subst hK
  rfl

/-- **R-6c-body-556 (Step 1) — divergence depends only on the intrinsic graph.**  If two subgraphs (possibly of *different*
ambients) have the same intrinsic graph `.toFeynmanGraph`, then divergence transports between them.  Route: lift `γ₁` to
its self-subgraph (`self_toFeynmanGraph_isDivergent`, ambient-invariant), transport the self-degree across the
intrinsic-graph equality `hEq` (the helper, via `subst`), then read back down to `γ₂` via
`IsAmbientInvariantDivergence.degree_self_eq`.  ★NO `HEq`/`cast`; the two ambients differ by design — `.toFeynmanGraph` is
the intrinsic graph and `degree` reads only it.★ -/
theorem feynmanSubgraph_isDivergent_of_toFeynmanGraph_eq
    {G₁ G₂ : FeynmanGraph} {γ₁ : FeynmanSubgraph G₁} {γ₂ : FeynmanSubgraph G₂}
    (hEq : γ₂.toFeynmanGraph = γ₁.toFeynmanGraph) (hDiv : γ₁.IsDivergent) :
    γ₂.IsDivergent := by
  have h1 : (FeynmanSubgraph.self γ₁.toFeynmanGraph γ₁.toFeynmanGraph_wellFormed).IsDivergent :=
    FeynmanSubgraph.self_toFeynmanGraph_isDivergent hDiv
  unfold FeynmanSubgraph.IsDivergent FeynmanSubgraph.divergenceDegree at h1 ⊢
  rw [← IsAmbientInvariantDivergence.degree_self_eq γ₂,
    degree_self_eq_of_graph_eq γ₁.toFeynmanGraph_wellFormed γ₂.toFeynmanGraph_wellFormed hEq]
  exact h1

/-! ## Step 2 — canonical remainder divergence (Parent-FREE). -/

/-- **R-6c-body-556 (Step 2) — the canonical flat quotient remainder is divergent, PARENT-FREE.**  The intrinsic graph of
the remainder is `δ`'s flat graph (body-555), and `δ`'s flat graph is divergent (the resolved forest `z.2.1`'s own
`isConnectedDivergent` accessor at `δ.1`, projected to `IsDivergent`); so Step 1 transports the divergence to the
remainder.  ★No `Parent`.★ -/
theorem canonicalLegSaturated_quotientRemainder_isDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (hH : ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph).WellFormed) :
    (admissibleSubgraphQuotientRemainderSubgraph
        (innerRaw z δ.1
            (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
            (liveAmbient_edges_supported ambientSupportOfW'' z)
            (liveAmbient_legs_supported ambientSupportOfW'' z)).forget
        (canonicalLegSaturatedFlatTouchedInnerStar z δ)
        (FeynmanSubgraph.self ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph) hH)).IsDivergent :=
  feynmanSubgraph_isDivergent_of_toFeynmanGraph_eq
    (canonicalLegSaturated_quotientRemainder_toFeynmanGraph_eq_delta z δ hH)
    (z.2.1.isConnectedDivergent δ.1 (Finset.mem_filter.mp δ.2).1).isDivergent

/-! ## Step 3 — apply the divergence reflection EXACTLY ONCE (Parent-FREE). -/

/-- **R-6c-body-556 (Step 3) — the canonical parent self-subgraph is divergent, via the reflection law.**  ★This is the
ONLY site that consumes the reflection class field.★  Body-553's public adapter
`admissibleSubgraphQuotientRemainder_divergent_reflect` is fed the Parent-free forest-cover premises (body-553 disjoint /
component-divergence, body-554 nonemptiness / flat fresh star), the parent self-subgraph as `γ`, and Step 2's remainder
divergence — reflecting divergence back onto the parent's self-subgraph.  ★No `Parent`.★ -/
theorem canonicalLegSaturated_parentSelf_isDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (hH : ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph).WellFormed) :
    (FeynmanSubgraph.self ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph) hH).IsDivergent :=
  admissibleSubgraphQuotientRemainder_divergent_reflect
    (innerRaw z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)).forget
    (legSaturated_innerRawForget_isPairwiseDisjoint z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z))
    (legSaturated_innerRawForget_hasNonemptyComponents z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z)
        (canonicalLegSaturated_innerRaw_hasNonemptyComponents z δ))
    (legSaturated_innerRawForget_forestDivergent z δ.1
        (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
        (liveAmbient_edges_supported ambientSupportOfW'' z)
        (liveAmbient_legs_supported ambientSupportOfW'' z))
    (canonicalLegSaturatedFlatTouchedInnerStar z δ)
    (canonicalLegSaturatedFlatTouchedInnerStar_isFreshStarAssignment z δ)
    (FeynmanSubgraph.self ((canonicalLegSaturatedParentForget z δ).toFeynmanGraph) hH)
    (canonicalLegSaturated_quotientRemainder_isDivergent z δ hH)

/-! ## Step 4 — `parentDivergent` (Parent-FREE). -/

/-- **R-6c-body-556 (Step 4) — the canonical `W″` parent is divergent, PARENT-FREE.**  Back-transport Step 3 through Step 1:
the parent's intrinsic graph equals its self-subgraph's intrinsic graph (`rfl`), so the parent inherits the self-subgraph's
divergence.  The well-formedness witness is supplied internally by `toFeynmanGraph_wellFormed`.  ★No `Parent`.★ -/
theorem canonicalLegSaturated_parent_isDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsDivergent :=
  feynmanSubgraph_isDivergent_of_toFeynmanGraph_eq
    (γ₂ := canonicalLegSaturatedParentForget z δ)
    (γ₁ := FeynmanSubgraph.self (canonicalLegSaturatedParentForget z δ).toFeynmanGraph
      (canonicalLegSaturatedParentForget z δ).toFeynmanGraph_wellFormed)
    rfl
    (canonicalLegSaturated_parentSelf_isDivergent z δ
      (canonicalLegSaturatedParentForget z δ).toFeynmanGraph_wellFormed)

/-! ## Step 5 — parent `IsConnectedDivergent` (Parent-FREE). -/

/-- **R-6c-body-556 (Step 5) — the canonical `W″` parent is connected-divergent, PARENT-FREE.**  Body-552's topology twin
(`parentCD` from `parentDivergent`, since `parentOnePI` is DERIVED) merged with Step 4's divergence.  ★No `Parent`.★ -/
theorem canonicalLegSaturated_parent_isConnectedDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent :=
  canonicalLegSaturated_parentCD_of_divergent z δ (canonicalLegSaturated_parent_isDivergent z δ)

/-! ## Step 6 — issue the SINGLE canonical `Parent` supply (a `def`, NOT an instance). -/

/-- **R-6c-body-556 (Step 6) — the canonical `W″` de-contraction CD supply, CONSTRUCTED.**  The single honest physics field
`parentCD` is now DERIVED (Step 5), so the whole `Parent` aggregate is the canonical resolved consequence of the existing
divergence-reflection law.  ★This is a plain named `def`, NOT an `instance`, and introduces NO new class/structure.★  The
field type `(localizedParentWithTouchedLegs …).forget.IsConnectedDivergent` is defeq to
`(canonicalLegSaturatedParentForget z δ).IsConnectedDivergent`. -/
def canonicalLegSaturatedDecontractionCDSupply :
    ResolvedCanonicalLegSaturatedDecontractionCDSupply where
  parentCD := fun z δ => canonicalLegSaturated_parent_isConnectedDivergent z δ

/-! ## Step 7 — the final `W″` native `Δᵣ`-coassociativity, with NO explicit `Parent` input. -/

/-- **R-6c-body-556 ∎ — the FINAL Parent discharge.**  Body-546's terminus, with the explicit `Parent` argument replaced by
the canonical Step-6 supply `canonicalLegSaturatedDecontractionCDSupply`.  The remaining explicit roots are `Measure` / `E`
/ `rep*`; the ambient physics typeclasses (including `IsDivergenceReflectedByAdmissibleForestContract`) remain as instance
arguments — this is **CK-physics-typeclass-modulo**, NOT unconditional.  body-546 is UNCHANGED; the `Parent` supply is
consumed here exactly once. -/
theorem coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ H : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalLegSaturatedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalLegSaturatedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalLegSaturated_alpha Measure E
    canonicalLegSaturatedDecontractionCDSupply rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
