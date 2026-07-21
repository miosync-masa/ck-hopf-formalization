import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaFmemReduction
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedFamilyDisjoint
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectedSurvivorRemnantCross
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaNativeFilteredValue

/-!
# R-6c-body-497 — canonical alpha `Split` discharge (`survivor_avoids` / `remnant_touches` DERIVED) (PROVED)

Four-hundred-and-ninety-seventh genuine-body step — the second stop of the residual-purification campaign.  Body-496
removed `Fmem` as an independent explicit input (it is a function of the divergence leaves `(N, E)`); this body removes
`Split` : `ResolvedAlphaValueQuotientRegionSplitSupply`.  Its two fields — `survivor_avoids` (every survivor component
`Disjoint` from the value outer star) and `remnant_touches` (every corrected-remnant component MEETS the value outer star)
— are proved directly on the forward `q`, from the SAME `Fstar.starOf_fresh` / promoted-star geometry that already carries
the body-464 remnant disjointness and the body-467 survivor/remnant cross.

## The two Split fields, discharged

* **`survivor_avoids`** — `δ ∈ (survivorSupply_of_measure C.Measure G).rightSurvivorForest q.1` recovers a right component
  `r` with `δ.vertices = r.1.1.vertices ⊆ G.vertices`; a member `v` of the value outer star is `D.starOf G (selectedOuterRawOf
  q.1) A` for some `A ∈ (selectedOuterRawOf q.1).elements`, hence `∉ G.vertices` by `Fstar.starOf_fresh` — contradiction, so
  `Disjoint`.  This is the survivor half of body-467's `correctedRightSurvivor_remnant_disjoint`, re-keyed to the value outer.
* **`remnant_touches`** — `δ = correctedRemnantComponent (q.1.forestComponentOccurrence γ)`; `CarrierProper`'s
  `IsNonempty` gives a component `b ∈ o.B.1.elements`, and `v := promotedOccurrenceStar q.1 o b` lies in BOTH the remnant's
  promoted-star vertices (`correctedRemnantComponent_vertices_eq_promoted` + `mem_starVertices ⟨b, hb, rfl⟩`) and the value
  outer star (`promote_mem_selectedOuterRawOf_raw` + the promoted-star definition), so the two are NOT `Disjoint`.

## Canonical specialization + signature adapter

`canonicalAlphaValueQuotientRegionSplitSupply` is the generic constructor at `(Fstar, CarrierProper, C, F)`; its canonical
`W'` instance `canonicalUniqueAlphaValueQuotientRegionSplitSupply VBuild E` supplies both `Split` and the body-496 canonical
`Fmem`.  `coassoc_gen_of_canonicalMultiStar_alpha_split_discharged` feeds them into the body-495 closed theorem — `Fmem` and
`Split` are GONE from its signature; the remaining explicit roots are `VBuild` / `E` / `ValueGeometry` / `OccRaw` / `rep`.

## Status

```text
Fmem                             CANONICAL DERIVED from Measure + E     (body-496)
Split.survivor_avoids            CANONICAL DERIVED — this body           (star-avoidance, Fstar.starOf_fresh)
Split.remnant_touches            CANONICAL DERIVED — this body           (promoted-star touch, CarrierProper nonempty)
remaining explicit roots         VBuild / E / ValueGeometry / OccRaw / rep / repCD / rep_gen
next root                        VBuild.survivorInj / survivorGen        (CANONICAL DERIVED CANDIDATE)
```

Per the HALT/guards: the closed body-495 theorem is NOT edited (a thin wrapper is added below it); `E` is NOT fabricated
from `Measure`; `OccRaw` / `survivorInj` / `survivorGen` / `quotient_mem` / `quot_eq` are NOT entered; NO new typeclass /
model axiom; NO unconditional-coassoc claim; strict `StarProm` / `InnerStarRaw` stay ZERO; body-445 stays a valid
conditional.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## The generic Split discharge -/

variable {D : ResolvedCoproductProperForestData}
  (Fstar : ResolvedCanonicalStarFacts D) (CarrierProper : ResolvedCarrierProperProvider D)

/-- **R-6c-body-497 ∎ — the generic alpha `Split` supply, both fields DERIVED.**  Over the canonical filtered value
`C.toFilteredConcreteSummandValueSupply` (survivor = `survivorSupply_of_measure C.Measure`, remnant =
`canonicalCorrectedRemnantComponentSupply Fstar CarrierProper`), the survivor/remnant vs value-outer-star geometry closes
both region-split fields with NO new hypothesis. -/
noncomputable def canonicalAlphaValueQuotientRegionSplitSupply
    (C : ResolvedAlphaNativeFilteredValueConstructionSupply D CarrierProper Fstar)
    (F : ResolvedSelectedOuterFilteredMemSupply D) :
    ResolvedAlphaValueQuotientRegionSplitSupply F
      (C.toFilteredConcreteSummandValueSupply CarrierProper Fstar) where
  survivor_avoids := fun {G} q δ hδ => by
    rw [ResolvedRightSurvivorSupply.rightSurvivorForest_elements] at hδ
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hδ
    rw [Finset.disjoint_left]
    intro v hv hv'
    have hvr : v ∈ r.1.1.vertices := hv
    have hv2 : v ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).starVertices
        (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1)) := hv'
    rw [ResolvedAdmissibleSubgraph.mem_starVertices] at hv2
    obtain ⟨A, hA, rfl⟩ := hv2
    exact Fstar.starOf_fresh G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1) A hA
      (r.1.1.vertices_subset hvr)
  remnant_touches := fun {G} q δ hδ => by
    rw [ResolvedRemnantComponentSupply.remnantForest_elements] at hδ
    obtain ⟨γ, -, rfl⟩ := Finset.mem_image.mp hδ
    set o := ResolvedCoassocSplitChoice.forestComponentOccurrence q.1 γ with ho
    obtain ⟨b, hb⟩ : (o.B.1.elements).Nonempty :=
      (CarrierProper.carrier_isProperForest o.γ.1.toResolvedFeynmanGraph o.B.1 o.B.2).1
    rw [Finset.not_disjoint_iff]
    refine ⟨promotedOccurrenceStar q.1 o b, ?_, ?_⟩
    · rw [show ((C.toFilteredConcreteSummandValueSupply CarrierProper Fstar).Remnant.remnant.remnantComponent
              q.1 o).vertices
            = (o.B.1.contractWithStars (promotedOccurrenceStar q.1 o)).vertices
          from correctedRemnantComponent_vertices_eq_promoted q.1 o Fstar,
        ResolvedAdmissibleSubgraph.contractWithStars_vertices, Finset.mem_union]
      exact Or.inr (ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨b, hb, rfl⟩)
    · show promotedOccurrenceStar q.1 o b
          ∈ ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).starVertices
            (D.starOf G ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1))
      exact ResolvedAdmissibleSubgraph.mem_starVertices.mpr
        ⟨o.γ.1.promote b, promote_mem_selectedOuterRawOf_raw q.1 o hb, rfl⟩

/-! ## The canonical `W'` specialization + signature adapter -/

/-- **R-6c-body-497 — the canonical `W'` alpha `Split` supply.**  The generic constructor at the canonical unique-ID
carrier's arguments; `F` is the body-496 canonical `Fmem` built from `VBuild.Measure` and `E`. -/
noncomputable def canonicalUniqueAlphaValueQuotientRegionSplitSupply
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G) :
    ResolvedAlphaValueQuotientRegionSplitSupply
      (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
      VBuild.toCanonicalFilteredValue :=
  canonicalAlphaValueQuotientRegionSplitSupply
    canonicalUniqueStarFactsOfW'
    canonicalUniqueSupportedCarrierProperSupply.toCarrierProperProvider
    VBuild
    (canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)

/-- **R-6c-body-497 ∎ — canonical-`W'` native `Δᵣ`-coassociativity with `Fmem` AND `Split` DISCHARGED.**  A thin wrapper
over the body-495 closed theorem: the canonical `Fmem` (body-496) and canonical `Split` (this body) are supplied
internally, so both are GONE from the signature.  The remaining explicit roots are `VBuild` / `E` / `ValueGeometry` /
`OccRaw` / `rep` / `repCD` / `rep_gen`. -/
theorem coassoc_gen_of_canonicalMultiStar_alpha_split_discharged
    (VBuild : ResolvedCanonicalUniqueAlphaFilteredValueConstructionSupply)
    (E : ∀ G : ResolvedFeynmanGraph, ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (ValueGeometry : ResolvedCanonicalUniqueMultiStarValueGeometrySupply)
    (OccRaw : ResolvedForestOccurrenceInversionValueSupply ValueGeometry.toCoreBuild.toValueCore)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalUniqueSupportedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalUniqueSupportedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x) :=
  coassoc_gen_of_canonicalMultiStar_alpha_closed
    (Fmem := canonicalUniqueSelectedOuterFilteredMemSupply_of_measure VBuild.Measure E)
    VBuild ValueGeometry OccRaw
    (canonicalUniqueAlphaValueQuotientRegionSplitSupply VBuild E)
    rep repCD rep_gen x

end GaugeGeometry.QFT.Combinatorial
