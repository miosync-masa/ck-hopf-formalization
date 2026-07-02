import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteCodomainForests

/-!
# R-6c-leaf-30 — Sector `forestLocal_mem` via an occurrence match (mem_image)

Twenty-fifth leaf-body discharge — the forest-side analogue of leaf-29, closing the right/forest asymmetry in
the Sector Forward memberships.  The remnant forest's elements are the `ofElements`-image (over
`s.forestComponents.attach`) of the transported remnant components indexed by `forestComponentOccurrence γ`,
while `forestLocal s f = (Local.remnant s).remnantComponent f.toOccurrence` is indexed by `f.toOccurrence`.
The gap is an OCCURRENCE MATCH: `f.toOccurrence` is `forestComponentOccurrence γ` for some `γ ∈ forestComponents`
(they agree by `Classical.choose` proof-irrelevance on the same `∃ B, choiceAt … = inr B`).

Given that match (`occurrence_match`) plus the remnant-forest element shape, `forestLocal_mem` is `mem_image`
(`refine mem_image.mpr ⟨γ, mem_attach, ?_⟩; simp only [forestLocal, hγ]`).

Per the HALT, `occurrence_match` (the `Classical.choose` proof-irrelevance / `f.i.toComponent ∈ forestComponents`
content) stays a supply field; backward maps / Perm / Retarget untouched.

Landed:

* `ResolvedForestOccurrenceMatchSupply C Local Align` — `remnantForest_elements_eq` + `occurrence_match`;
* `.forestLocal_mem` — the Sector Forward remnant membership, DERIVED via `mem_image`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

open scoped Classical

/-- **R-6c-leaf-30 — the forest occurrence-match supply.**  The remnant forest's element shape + the match
`f.toOccurrence = forestComponentOccurrence γ`. -/
structure ResolvedForestOccurrenceMatchSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Local : ResolvedSectorLocalComponentSupply D G)
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf) where
  /-- The Codomain remnant forest is the `ofElements`-image of the transported remnant components. -/
  remnantForest_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.remnantForest s).elements =
      s.forestComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (Align.quotientGraph_eq s)
          ((Local.remnant s).remnantComponent (s.forestComponentOccurrence γ)))
  /-- Each forest index's occurrence is a forest-component occurrence. -/
  occurrence_match : ∀ (s : ResolvedCoassocSplitChoice D G) (f : ForestPrimitiveIndex D G s),
    ∃ γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents},
      s.forestComponentOccurrence γ = f.toOccurrence

/-- **R-6c-leaf-30 — the Sector Forward remnant membership from the occurrence match. -/
theorem ResolvedForestOccurrenceMatchSupply.forestLocal_mem
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {Local : ResolvedSectorLocalComponentSupply D G}
    {Align : ResolvedSectorForwardGraphAlignment D G imageOf}
    (M : ResolvedForestOccurrenceMatchSupply C Local Align)
    (s : ResolvedCoassocSplitChoice D G) (f : ForestPrimitiveIndex D G s) :
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.forestLocal s f)
      ∈ (C.remnantForest s).elements := by
  obtain ⟨γ, hγ⟩ := M.occurrence_match s f
  rw [M.remnantForest_elements_eq s]
  refine Finset.mem_image.mpr ⟨γ, Finset.mem_attach _ _, ?_⟩
  simp only [ResolvedSectorLocalComponentSupply.forestLocal, hγ]

end GaugeGeometry.QFT.Combinatorial
