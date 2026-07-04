import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveFactorComplete

/-!
# R-6c-body-121 — right-primitive survival transport: `right_primitive_factor` discharged from source + transport

Hundred-and-twenty-first genuine-body step, closing the assembly's `right_primitive_factor` by composing the
body-120 source-side result with the source↔quotient SURVIVAL TRANSPORT.  The transport — that the source
right-primitive forest and the quotient right-survivor forest have the same left term — is the "right survivors
are preserved under the selected-outer contraction" fact, isolated here as one leaf and reduced to the EXISTING
survivor-reembed machinery.

## The composition (PROVED)

`right_primitive_factor_of_transport`: given the transport `leftTerm(sourceRightPrim q) = leftTerm(rightSurvivor)`,

```text
∏_{γ : ¬(p γ).isRight} localRightFactor(p γ) = leftTerm(rightSurvivor)
```

by `(right_primitive_factor_source q).trans transport` — body-120's source-side factor composed with the
transport.  So the assembly's `right_primitive_factor` follows from the single transport leaf.

## The transport reduces to survivor reembed (existing machinery)

`sourceRightPrim q = A'.filterElements rightPrimSelected` (the source right-primitive components) and the
quotient `rightSurvivorForest` is `ofElements (rightComponents.image survivorComponent)`, where
`survivorComponent = survivorReembed …` of a source right-primitive component into the quotient graph.  The
reembed PRESERVES the resolved graph — `survivorReembed_toResolvedFeynmanGraph = rfl`
(`ResolvedSurvivorEmbedSupport`) — and hence the component GENERATOR (`rightSurvivorComponentOf_gen`,
`RightSurvivorDisjoint`).  So

```text
leftTerm(rightSurvivorForest) = ∏_{survivor δ} X(gen δ) = ∏_{source right-prim γ} X(gen γ) = leftTerm(sourceRightPrim)
```

via the survivor `Finset` bijection (`rightComponents ≃ survivor images`) with generators matched by the reembed
`rfl`.  The transport is therefore the resolved analogue of "a component disjoint from the contracted forests
survives the contraction unchanged" — and the SAME fact powers the sector right-forward map
(`rightForward = transport ∘ rightSurvivorComponentOf`), so proving it once feeds the backward map too.

`ResolvedRightPrimitiveSurvivalTransportSupply` fields this transport (per split choice) against an abstract
quotient right-survivor forest; `.right_primitive_factor` composes it with body-120.

Per the HALT: `right_primitive_factor` is discharged from the source factor (body-120) plus the transport; the
transport is isolated as the exact leaf (reducing to `survivorReembed_toResolvedFeynmanGraph` + the survivor
bijection); no sector inverse is entered.

Landed:

* `right_primitive_factor_of_transport` — `right_primitive_factor` from body-120 + the transport (PROVED);
* `ResolvedRightPrimitiveSurvivalTransportSupply D` — the survival transport, per split choice, against an
  abstract right-survivor forest;
* `.right_primitive_factor` — the assembly's field, discharged.

Toolkit body (like body-119/120), one small supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-121 — `right_primitive_factor` from the source factor and the survival transport.**  Compose
body-120's source-side factor with the transport `leftTerm(sourceRightPrim) = leftTerm(rightSurvivor)`. -/
theorem right_primitive_factor_of_transport (q : ResolvedCoassocSplitChoice D G)
    (H : ResolvedFeynmanGraph) (rightSurvivor : ResolvedAdmissibleSubgraph H)
    (transport : resolvedForestLeftTerm (q.1.1.filterElements (fun γ => rightPrimSelected q γ))
      = resolvedForestLeftTerm rightSurvivor) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm rightSurvivor :=
  (right_primitive_factor_source q).trans transport

/-- **R-6c-body-121 — the right-primitive survival transport supply.**  For each split choice, the source
right-primitive forest and the quotient right-survivor forest have the same left term (the "survivor preserved
under contraction" fact; reduces to `survivorReembed_toResolvedFeynmanGraph` + the survivor bijection). -/
structure ResolvedRightPrimitiveSurvivalTransportSupply (D : ResolvedCoproductProperForestData) where
  /-- The quotient right-survivor forest per split choice (over the selected-outer quotient graph). -/
  rightSurvivor : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ResolvedAdmissibleSubgraph q.selectedOuterContractGraph
  /-- The survival transport: source right-primitive forest ≅ quotient right-survivor forest (left terms). -/
  transport : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    resolvedForestLeftTerm (q.1.1.filterElements (fun γ => rightPrimSelected q γ))
      = resolvedForestLeftTerm (rightSurvivor q)

/-- **R-6c-body-121 — the assembly's `right_primitive_factor` from the survival-transport supply.** -/
theorem ResolvedRightPrimitiveSurvivalTransportSupply.right_primitive_factor
    (S : ResolvedRightPrimitiveSurvivalTransportSupply D) (q : ResolvedCoassocSplitChoice D G) :
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (S.rightSurvivor q) :=
  right_primitive_factor_of_transport q q.selectedOuterContractGraph (S.rightSurvivor q) (S.transport q)

end GaugeGeometry.QFT.Combinatorial
