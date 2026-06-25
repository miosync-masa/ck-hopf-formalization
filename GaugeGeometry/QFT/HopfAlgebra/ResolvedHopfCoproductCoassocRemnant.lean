import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivor

/-!
# R-6c-heart-5b-3 — the quotient-side remnant components from forest choices

The full quotient forest is `Right ⊔ Remnant`.  5b-2 built the **Right** part (the right-survivors of
the `Sum.inl false` components).  This file builds the **Remnant** part: the pieces contributed by the
forest choices `choiceAt γ = Sum.inr B`.  Such a `γ` is promoted into `selectedOuter`, and contracting
`selectedOuter` leaves the *remnant* of `B` inside the quotient graph
`selectedOuter.contractWithStars`.

The dependent-codomain pain (`choiceAt γ`'s type depends on `γ`) is handled up front by an **occurrence
index** carrying `γ`, its forest choice `B`, and the witness `hchoice : choiceAt γ = Sum.inr B`.

The actual de-contraction/localize embedding of a remnant into the quotient graph (the genuine remnant
machinery) is — per the HALT — isolated as a supply `ResolvedRemnantComponentSupply`, and the remnant
forest is assembled via `ofElements` over the supplied component images.

Landed:

* `ResolvedCoassocSplitChoice.ForestChoiceOccurrence` — the `(γ, B, hchoice)` remnant index;
* `ResolvedCoassocSplitChoice.forestComponentOccurrence` — the occurrence of a forest component
  (`Classical.choose` of `isForestChoice`);
* `ResolvedRemnantComponentSupply D G` — the remnant component embedding + CD + disjoint (supply);
* `ResolvedRemnantComponentSupply.remnantForest` (+ `_elements` simp) — the remnant half via `ofElements`;
* `ResolvedQuotientForestCrossSupply D G` — the survivor/remnant cross-disjointness for the eventual
  `Right ⊔ Remnant` assembly (supply, 5b-3d).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The concrete remnant embedding and the full
quotient forest (`fullQuotientOf`, 5b-4) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-! ## 5b-3a — the forest-choice occurrence index -/

/-- **R-6c-heart-5b-3a — a forest-choice occurrence.**  An input outer component `γ` together with its
local forest choice `B` and the witness `choiceAt γ = Sum.inr B`.  Carrying `B` explicitly sidesteps the
dependent codomain of `choiceAt` when constructing the remnant. -/
structure ResolvedCoassocSplitChoice.ForestChoiceOccurrence (s : ResolvedCoassocSplitChoice D G) where
  /-- The input outer component making a forest choice. -/
  γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}
  /-- The chosen sub-forest of the component graph. -/
  B : (D.supply γ.1.toResolvedFeynmanGraph).ForestIdx
  /-- The local choice at `γ` is the forest choice `B`. -/
  hchoice : s.choiceAt γ = Sum.inr B

/-- **R-6c-heart-5b-3a — the occurrence of a forest component.**  Every component in `forestComponents`
makes a forest choice; `Classical.choose` extracts the witnessing `B`. -/
noncomputable def ResolvedCoassocSplitChoice.forestComponentOccurrence
    (s : ResolvedCoassocSplitChoice D G) (γ : {x : _ // x ∈ s.forestComponents}) :
    s.ForestChoiceOccurrence :=
  have h : s.isForestChoice γ.1 := (Finset.mem_filter.mp γ.2).2
  ⟨γ.1, Classical.choose h, Classical.choose_spec h⟩

/-! ## 5b-3b/3c — the remnant component supply and forest (scaffold) -/

/-- **R-6c-heart-5b-3b — the remnant component supply.**  Per the HALT, the de-contraction/localize
embedding of each forest-choice remnant into the quotient graph (`remnantComponent`), its
connected-divergence, and the pairwise disjointness of the embedded family are isolated as supply fields
— the genuine `contractWithStars` remnant content. -/
structure ResolvedRemnantComponentSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The remnant of a forest choice embedded into the quotient graph. -/
  remnantComponent : (s : ResolvedCoassocSplitChoice D G) → s.ForestChoiceOccurrence →
    ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each remnant component is connected-divergent. -/
  remnantCD : ∀ (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence),
    (remnantComponent s o).forget.IsConnectedDivergent
  /-- The remnant components are pairwise disjoint in the quotient graph. -/
  remnantDisjoint : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ ⦃δ⦄, δ ∈ s.forestComponents.attach.image
        (fun γ => remnantComponent s (s.forestComponentOccurrence γ)) →
    ∀ ⦃δ'⦄, δ' ∈ s.forestComponents.attach.image
        (fun γ => remnantComponent s (s.forestComponentOccurrence γ)) →
    δ ≠ δ' → δ.Disjoint δ'

/-- **R-6c-heart-5b-3c — the remnant forest.**  The `ofElements` admissible forest over the remnant
component images in the quotient graph — the `Remnant` half of the full quotient. -/
noncomputable def ResolvedRemnantComponentSupply.remnantForest
    (R : ResolvedRemnantComponentSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedAdmissibleSubgraph s.selectedOuterContractGraph :=
  ResolvedAdmissibleSubgraph.ofElements
    (s.forestComponents.attach.image (fun γ => R.remnantComponent s (s.forestComponentOccurrence γ)))
    (by
      intro δ hδ
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ
      exact R.remnantCD s (s.forestComponentOccurrence γ))
    (R.remnantDisjoint s)

@[simp] theorem ResolvedRemnantComponentSupply.remnantForest_elements
    (R : ResolvedRemnantComponentSupply D G) (s : ResolvedCoassocSplitChoice D G) :
    (R.remnantForest s).elements =
      s.forestComponents.attach.image (fun γ => R.remnantComponent s (s.forestComponentOccurrence γ)) :=
  rfl

/-! ## 5b-3d — survivor/remnant cross-disjointness (scaffold) -/

/-- **R-6c-heart-5b-3d — the quotient-forest cross supply.**  Bundles a right-survivor supply and a
remnant supply with the cross-disjointness of their forests — the data needed to assemble the full
quotient `Right ⊔ Remnant` (5b-4).  The cross-disjointness is a supply field (the survivor and remnant
live in disjoint regions of the quotient graph, but the proof needs the embeddings concrete). -/
structure ResolvedQuotientForestCrossSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The right-survivor supply (the `Right` half). -/
  survivor : ResolvedRightSurvivorSupply D G
  /-- The remnant supply (the `Remnant` half). -/
  remnant : ResolvedRemnantComponentSupply D G
  /-- Survivor and remnant components are cross-disjoint. -/
  cross : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ δ ∈ (survivor.rightSurvivorForest s).elements,
    ∀ δ' ∈ (remnant.remnantForest s).elements, δ ≠ δ' → δ.Disjoint δ'

end GaugeGeometry.QFT.Combinatorial
