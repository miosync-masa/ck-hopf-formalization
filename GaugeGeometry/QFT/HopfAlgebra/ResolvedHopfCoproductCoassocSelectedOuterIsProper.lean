import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesPositive
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPositiveInternalEdges
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInternalEdgesCardPos
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFwdMapFiltered

/-!
# R-6c-body-264 — `IsProperForest` for the two constructed forests (PROVED)

Two-hundred-and-sixty-fourth genuine-body step — the `IsProperForest` assembly from the five proved conjunct
ingredients (bodies 236/238/241/244/246/263).  `X = selectedOuterRawOf` on the filtered domain is the 5-tuple; `Y`
inherits everything from the carrier forest via an **elements-equality transfer**, so it needs no `fwdMap S` in its
declaration.

## X — the 5-tuple (filtered domain)

`selectedOuterRaw_isProperForest`: from `q.2` (`q.1 ∈ forestBlockDomFinset G`) extract `q.1.2 ∈ forestChoiceCarrier
q.1.1` (`Finset.mem_sigma`), then assemble in `IsProperForest`'s definition order —
`IsNonempty` (244) / `HasNonemptyComponents` (236) / `0 < internalEdges.card` (246) /
`HasPositiveInternalEdgesComponents` (238) / `0 < complementEdges.card` (263).

## Y — elements-equality transfer (canonical, no `fwdMap S`)

`isProperForest_of_elements_eq`: if `B.elements = A.1.elements` for a carrier member `A`, then `B = A.1`
(`ext_elements`) so `B.IsProperForest` is `A`'s carrier properness.  The recovered outer applies this with `A := q.1`
and the partition elements-equality `(unionOuter (fwdMap S q)).1.elements = q.1.1.elements` (body-241 route) — but the
theorem statement is `fwdMap`-free; only the *application* passes the forward-image equality.

Per the HALT: `IsProperForest` for `X` (filtered) and the generic transfer for `Y` are proved; the canonical statements
contain no retired total root / `fwdMap S`; `recovered_eq` and the certificate assembly are untouched.  No facade, no
flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-264 — the selected outer is a proper forest** (filtered domain).  The 5-tuple from the proved
conjunct ingredients, in `IsProperForest`'s definition order. -/
theorem selectedOuterRaw_isProperForest (N : ResolvedConnectedDivergentNonemptySupply G)
    (E : ResolvedConnectedDivergentPositiveInternalEdgesSupply G)
    (P : ResolvedCarrierProperProvider D) (q : FilteredForestBlockDom D G) :
    ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).IsProperForest := by
  have hp : q.1.2 ∈ forestChoiceCarrier q.1.1 := by
    have h := q.2
    simp only [forestBlockDomFinset, Finset.mem_sigma] at h
    exact h.2
  have hNE : ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q.1).IsNonempty :=
    selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier P hp
  exact ⟨hNE, hasNonemptyComponents_of_cdNonempty N _,
    ResolvedAdmissibleSubgraph.internalEdges_card_pos_of_isNonempty _ hNE
      (hasPositiveInternalEdgesComponents_of_cdPositive E _),
    hasPositiveInternalEdgesComponents_of_cdPositive E _,
    selectedOuterRaw_complementEdges_card_pos P q.1⟩

/-- **R-6c-body-264 — proper forest transfers along an elements equality with a carrier member.**  If `B` has the same
elements as a carrier member `A`, then `B = A.1` is a proper forest. -/
theorem isProperForest_of_elements_eq (P : ResolvedCarrierProperProvider D)
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) (B : ResolvedAdmissibleSubgraph G)
    (h : B.elements = A.1.elements) : B.IsProperForest := by
  rw [ResolvedAdmissibleSubgraph.ext_elements h]
  exact P.carrier_isProperForest G A.1 A.2

end GaugeGeometry.QFT.Combinatorial
