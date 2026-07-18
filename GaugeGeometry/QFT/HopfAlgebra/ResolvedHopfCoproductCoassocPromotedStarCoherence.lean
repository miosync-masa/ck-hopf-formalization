import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParentRemnantSectionValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarForestBridge
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalStarFacts

/-!
# R-6c-body-383 — bank-3b: the cross-ambient promoted-star bridge, isolated as an honest datum (PROVED)

Three-hundred-and-eighty-third genuine-body step — the star audit for `touchedOuterComponents_of_occurrence` (body-384).
That alignment turns on the CROSS-AMBIENT identity

```text
D.starOf G (selectedOuterRawOf q) (o.γ.1.promote b) = D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1 b
```

comparing the star of the promoted component (over `G` / `selectedOuterRawOf q`) with the star of the inner component
`b ∈ o.B.1.elements` (over `o.γ.1.tRFG` / `o.B.1`).

**Audit verdict (a NEW honest datum, not derivable).**  A search of the resolved star API finds NO such bridge, and —
per body-379's verdict — `D.starOf`'s only structural law is `star_mapPerm` (SAME-graph permutation equivariance);
`starOf_fresh` / `starOf_injective` are also same-`(G', A)` facts.  None can equate stars across TWO ambients / TWO
forests.  So `promoted_star_agrees` is a genuine FORWARD promoted-star coherence datum — distinct from body-349's
`innerStar_agrees` (which compares `M.parent`/`M.innerIdx` stars, reached only through the parent equality we are trying
to prove).  It is isolated here as ONE field.

Landed axiom-clean: `ResolvedPromotedStarCoherenceValueSupply`.

## Roadmap for `touchedOuterComponents_of_occurrence` (body-384, under this datum)

`touchedOuterComponents (fwd q) δ = (selectedOuterRawOf q).elements.filter (starOf · ∈ δ.vertices)`;
`δ.vertices = (remnantComponent o).vertices = (o.B.1.contractWithStars (starOf o.γ.1.tRFG o.B.1)).vertices =
(o.γ.1.tRFG.vertices \ o.B.1.vertices) ∪ o.B.1.starVertices` (body's `contractWithStars_vertices`, `hδ`).
* **promoted ⊆ touched** — `A = o.γ.1.promote b`; `starOf_G A = (promoted_star_agrees) starOf o.γ.1.tRFG o.B.1 b ∈
  o.B.1.starVertices ⊆ δ.vertices` (`mem_starVertices`).
* **touched ⊆ promoted** — `starOf_G A ∈ δ.vertices`; by `starOf_fresh` it is a star, so it is `o.B.1`'s star of some
  `b`; `promoted_star_agrees` rewrites it to `starOf_G (o.γ.1.promote b)`; `starOf_injective` on `selectedOuterRawOf q`
  gives `A = o.γ.1.promote b`.

Per the HALT: only the cross-ambient star VERDICT + the isolated datum are done; freshness is NOT used to fabricate the
cross-graph equality (that is exactly the datum); `touchedOuterComponents_of_occurrence` is body-384, proved UNDER this
datum; `hparent` / `OccInv` / body-341 `houter` / forest bridge / `forestSource` stay unused.  No facade, no flat term,
no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-383 — the forward promoted-star coherence datum.**  The star of a promoted outer component (over the
forward-selected outer) equals the star of its inner component (over the occurrence's parent) — a cross-ambient
identity `star_mapPerm` cannot supply. -/
structure ResolvedPromotedStarCoherenceValueSupply
    (Fmem : ResolvedSelectedOuterFilteredMemSupply D) (V : ResolvedConcreteSummandValueSupply D) where
  /-- The promoted component's star equals the inner component's star (cross-ambient). -/
  promoted_star_agrees : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (b : ResolvedFeynmanSubgraph o.γ.1.toResolvedFeynmanGraph) (_hb : b ∈ o.B.1.elements),
    D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)
        (o.γ.1.promote b)
      = D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1 b

end GaugeGeometry.QFT.Combinatorial
