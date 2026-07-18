import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantComponentValueWiring
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOuterComponents

/-!
# R-6c-body-385 — bank-3b: the concrete touched-collection theorem `touchedOuterComponents_of_occurrence` (PROVED)

Three-hundred-and-eighty-fifth genuine-body step — the shared core of the parent/remnant three-projection audit
(bodies 381/382), proved **on the concrete remnant** and consuming ONLY the body-383 cross-ambient datum
`promoted_star_agrees`.  For a forward forest-choice occurrence `o` whose concrete contracted-source remnant is `δ`,
the touched collection of the forward-selected outer inside `δ` is EXACTLY the occurrence's `o.B`-promoted collection:

```text
touchedOuterComponents (fwd q) δ.1 = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements
```

No abstract `V.Remnant` is used — `δ` is stated over the concrete `(Concrete q.1).remnantComponent o`, whose data is
`o.contractedSourceGraph`'s by `rfl` (`reembedAsSubgraph`); the abstract adapter (via body-384's `Wiring`) is body-386.

## The two inclusions (both cross-ambient, star-classified)

`δ.1.vertices = o.contractedSourceGraph.vertices = (o.γ.1.vertices \ o.B.1.vertices) ∪ o.B.1.starVertices innerStar`
(`hδ` + `contractWithStars_vertices`), where `innerStar = D.starOf o.γ.1.tRFG o.B.1`.

* **promoted ⊆ touched** — `A = o.γ.1.promote b`, `b ∈ o.B.1.elements`; `A ∈ selectedOuterRawOf q.1`
  (`promote_mem_selectedOuterRawOf`); `promoted_star_agrees` sends its outer star to `innerStar b ∈ o.B.1.starVertices
  ⊆ δ.1.vertices` (`mem_starVertices`).
* **touched ⊆ promoted** — `A ∈ selectedOuterRawOf q.1`, `star A ∈ δ.1.vertices`; `starOf_fresh` puts `star A ∉ G.vertices`,
  so it is NOT in the outside branch `o.γ.1.vertices \ o.B.1.vertices ⊆ o.γ.1.vertices ⊆ G.vertices`; hence it is a
  `B`-star `innerStar b`; `promoted_star_agrees` rewrites it to `star (o.γ.1.promote b)`, and `starOf_injective` on
  `selectedOuterRawOf q.1` gives `A = o.γ.1.promote b`.

Per the HALT: only the concrete touched theorem is proved; the sole geometric datum consumed is `promoted_star_agrees`;
the abstract `V.Remnant` / body-384 `Wiring` / `OccInv` / `parent_remnantComponent` / forest bridge / forward
round-trip are NOT used; freshness classifies but does NOT fabricate the cross-graph star equality (that IS the datum).
No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-385 — a promoted inner component lands in the forward-selected outer.**  For a forest-choice
occurrence `o` and an inner component `b ∈ o.B.1.elements`, the promotion `o.γ.1.promote b` is one of the
`selectedOuterRawOf q.1` components (via `promotedOf`'s biUnion at `o.γ` under `o.hchoice`). -/
theorem promote_mem_selectedOuterRawOf {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    {b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph} (hb : b ∈ o.B.1.elements) :
    o.γ.1.promote b
      ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).elements := by
  classical
  have hmem : o.γ.1.promote b
      ∈ ((resolvedPromotedOfSupply D G).promotedOf q.1).elements := by
    rw [ResolvedPromotedOfSupply.promotedOf_elements]
    unfold ResolvedCoassocSplitChoice.promotedElements
    refine Finset.mem_biUnion.mpr ⟨o.γ, Finset.mem_attach _ _, ?_⟩
    rw [ResolvedCoassocSplitChoice.promotedComponentElements_inr q.1 o.hchoice]
    simp only [ResolvedAdmissibleSubgraph.promote_elements, Finset.mem_image]
    exact ⟨b, hb, rfl⟩
  simp only [ResolvedForestPromoteSupply.selectedOuterRawOf,
    ResolvedAdmissibleSubgraph.union_elements, Finset.mem_union]
  exact Or.inr hmem

/-- **R-6c-body-385 — the concrete touched-collection theorem.**  The forward-selected outer's touched collection
inside the concrete remnant `δ` of a forest-choice occurrence `o` is the occurrence's `o.B`-promoted collection. -/
theorem touchedOuterComponents_of_occurrence
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (Fstar : ResolvedCanonicalStarFacts D)
    (Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ResolvedConcreteRemnantReembedSupply D G s)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq ((Concrete q.1).remnantComponent o) δ.1) :
    touchedOuterComponents (fwdMapFilteredValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements := by
  -- `δ`'s vertices are the contracted source graph's, split into outside / inner-star image.
  have hcr : (Concrete q.1).remnantComponent o = δ.1 := eq_of_heq hδ
  have hδv : δ.1.vertices
      = (o.γ.1.toResolvedFeynmanGraph.vertices \ o.B.1.vertices)
        ∪ o.B.1.starVertices (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1) := by
    rw [← hcr]
    exact ResolvedAdmissibleSubgraph.contractWithStars_vertices o.B.1 _
  apply Finset.ext
  intro A
  simp only [mem_touchedOuterComponents, ResolvedAdmissibleSubgraph.promote_elements,
    Finset.mem_image]
  constructor
  · -- touched ⊆ promoted
    rintro ⟨hAmem, hstar⟩
    rw [hδv] at hstar
    rcases Finset.mem_union.mp hstar with hout | hstarv
    · exfalso
      rw [Finset.mem_sdiff] at hout
      exact Fstar.starOf_fresh G _ A hAmem (o.γ.1.vertices_subset hout.1)
    · rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hstarv
      obtain ⟨b, hb, hbstar⟩ := hstarv
      have hpsa := StarProm.promoted_star_agrees q o b hb
      have hpmem : o.γ.1.promote b ∈ (fwdMapFilteredValue Fmem V q).1.1.elements :=
        promote_mem_selectedOuterRawOf q o hb
      have hAeq : A = o.γ.1.promote b :=
        Fstar.starOf_injective G _ hAmem hpmem (hbstar.symm.trans hpsa.symm)
      exact ⟨b, hb, hAeq.symm⟩
  · -- promoted ⊆ touched
    rintro ⟨b, hb, rfl⟩
    have hpmem : o.γ.1.promote b ∈ (fwdMapFilteredValue Fmem V q).1.1.elements :=
      promote_mem_selectedOuterRawOf q o hb
    refine ⟨hpmem, ?_⟩
    rw [hδv]
    exact Finset.mem_union.mpr
      (Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr
        ⟨b, hb, (StarProm.promoted_star_agrees q o b hb).symm⟩))

end GaugeGeometry.QFT.Combinatorial
