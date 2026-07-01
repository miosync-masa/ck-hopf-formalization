import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductInjectionLeaves
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout

/-!
# R-6c-leaf-9 — Product `remnantInj` reduced to occurrence de-contraction injectivity

Companion of `survivorInj` (leaf-8), closing the Product injection pair.  Unlike the survivor, the remnant
component is the *contracted* source graph (`o.contractedSourceGraph = B.contractWithStars …`), which loses
the original component, so intrinsic-graph preservation does NOT recover `γ` on its own.  What it recovers is
the **occurrence**'s contracted graph; the step back to the occurrence (and hence the component index) is the
genuine de-contraction injectivity, isolated as one leaf:

```text
occurrence_inj : o₁.contractedSourceGraph = o₂.contractedSourceGraph → o₁ = o₂
```

Given that leaf plus the remnant component's graph preservation (`remnantGraph_eq`, satisfied by the concrete
re-embed 6a-5c-4c via `rfl`), `remnantInj` follows: `remnantComponent (occ γᵢ)` equal ⇒ (graph preservation)
`(occ γ₁).contractedSourceGraph = (occ γ₂).contractedSourceGraph` ⇒ (occurrence_inj) `occ γ₁ = occ γ₂` ⇒
(`.γ` projection, `Subtype.ext`) `γ₁ = γ₂`.

Per the HALT, `occurrence_inj` (de-contraction uniqueness) is NOT proved (the supply field); no hPD/hLP/hDisj.

Landed:

* `ResolvedRemnantOccurrenceInjectivitySupply D G s` — the `occurrence_inj` leaf;
* `remnantInj_of_occurrence_graph_inj` — `remnantInj` from graph preservation + `occurrence_inj`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-9 — the occurrence de-contraction injectivity supply.**  Distinct forest occurrences have
distinct contracted source graphs — the genuine de-contraction uniqueness leaf behind `remnantInj`. -/
structure ResolvedRemnantOccurrenceInjectivitySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- Contracted-source-graph equality forces occurrence equality. -/
  occurrence_inj : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    o₁.contractedSourceGraph = o₂.contractedSourceGraph → o₁ = o₂

/-- **R-6c-leaf-9 — the Product `remnantInj` leaf from graph preservation + occurrence injectivity.**  For a
remnant component supply whose components preserve the occurrence's contracted graph (`remnantGraph_eq`), the
occurrence de-contraction injectivity yields `remnantInj`. -/
theorem remnantInj_of_occurrence_graph_inj
    (M : ResolvedRemnantComponentSupply D G) (s : ResolvedCoassocSplitChoice D G)
    (remnantGraph_eq : ∀ o : s.ForestChoiceOccurrence,
      (M.remnantComponent s o).toResolvedFeynmanGraph = o.contractedSourceGraph)
    (Occ : ResolvedRemnantOccurrenceInjectivitySupply D G s) :
    ∀ γ₁ ∈ s.forestComponents.attach, ∀ γ₂ ∈ s.forestComponents.attach,
      M.remnantComponent s (s.forestComponentOccurrence γ₁)
        = M.remnantComponent s (s.forestComponentOccurrence γ₂) → γ₁ = γ₂ := by
  intro γ₁ _ γ₂ _ heq
  apply Subtype.ext
  have hocc : s.forestComponentOccurrence γ₁ = s.forestComponentOccurrence γ₂ := by
    apply Occ.occurrence_inj
    have h := congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph heq
    rw [remnantGraph_eq, remnantGraph_eq] at h
    exact h
  exact congrArg (fun o => o.γ) hocc

end GaugeGeometry.QFT.Combinatorial
