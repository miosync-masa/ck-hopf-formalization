import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantInjection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout

/-!
# R-6c-body-7 — occurrence injectivity reduced to parent recovery

Seventh genuine-body step, on the SHARED de-contraction-uniqueness kernel: `occurrence_inj` powers BOTH the
Product `remnantInj` (leaf-9) and the Sector `forest_forward_injective` (body-6).

A `ForestChoiceOccurrence` is `⟨γ, B, hchoice : s.choiceAt γ = Sum.inr B⟩`, with `contractedSourceGraph =
B.1.contractWithStars (D.starOf γ.1.graph B.1)`.  So `occurrence_inj` (contracted-graph equality ⇒ occurrence
equality) splits into:

* `parent_inj` — the hard kernel: contracted-graph equality recovers the PARENT `o₁.γ = o₂.γ` (a
  de-contraction-injectivity fact — the genuine geometry, fielded);
* then `B` is forced: with `γ₁ = γ₂`, `hchoice₁` / `hchoice₂` both read `s.choiceAt γ₁`, so `Sum.inr B₁ =
  Sum.inr B₂` gives `B₁ = B₂` (`Sum.inr.inj`), and the occurrences are equal (structure ext, `hchoice`
  proof-irrelevant).

Per the HALT, `parent_inj` is the supply field (the parent-recovery geometry); the remnant graph geometry is
untouched.

Landed:

* `ResolvedOccurrenceParentInjectivitySupply D G s` — `parent_inj`;
* `.toRemnantOccurrenceInjectivitySupply` — the leaf-9 `occurrence_inj` supply (`parent_inj` + `B` forced).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-7 — the occurrence parent-injectivity supply.**  Contracted-graph equality recovers the parent
component — the de-contraction-uniqueness kernel. -/
structure ResolvedOccurrenceParentInjectivitySupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (s : ResolvedCoassocSplitChoice D G) where
  /-- Contracted-source-graph equality forces the parent components equal. -/
  parent_inj : ∀ o₁ o₂ : s.ForestChoiceOccurrence,
    o₁.contractedSourceGraph = o₂.contractedSourceGraph → o₁.γ = o₂.γ

/-- **R-6c-body-7 — the leaf-9 occurrence injectivity from parent recovery.**  With the parents equal, the
forest choice `B` is forced by the local choice, so the occurrences coincide. -/
def ResolvedOccurrenceParentInjectivitySupply.toRemnantOccurrenceInjectivitySupply
    {s : ResolvedCoassocSplitChoice D G}
    (P : ResolvedOccurrenceParentInjectivitySupply D G s) :
    ResolvedRemnantOccurrenceInjectivitySupply D G s where
  occurrence_inj := fun o₁ o₂ hcg => by
    obtain ⟨γ₁, B₁, hc₁⟩ := o₁
    obtain ⟨γ₂, B₂, hc₂⟩ := o₂
    have hγ : γ₁ = γ₂ := P.parent_inj ⟨γ₁, B₁, hc₁⟩ ⟨γ₂, B₂, hc₂⟩ hcg
    subst hγ
    have hB : B₁ = B₂ := Sum.inr.inj (hc₁.symm.trans hc₂)
    subst hB
    rfl

end GaugeGeometry.QFT.Combinatorial
