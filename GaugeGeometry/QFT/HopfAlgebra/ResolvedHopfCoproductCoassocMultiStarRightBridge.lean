import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocValueQuotientRegionSplit
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRightRegion

/-!
# R-6c-body-368 — Front-3 bank-2: the right-sector component section over the forward image (PROVED)

Three-hundred-and-sixty-eighth genuine-body step — the geometric crux of the right sound/complete bridge.  The two
re-embeddings `survivorComponent` (`= survivorReembedOfDisjoint = reembed`) and `rightReembed` (`= reembed`) compose to
the IDENTITY on the source outer component, over `fwdMapFilteredValue F V q` (NOT the recovered context of body-346).
Both re-embeddings pass ALL THREE data (`vertices` / `internalEdges` / `externalLegs`) through unchanged — so
`ResolvedFeynmanSubgraph.ext` closes each by `rfl`.  This is the "one section" from which body-274's forward-image set
correspondence derives BOTH the right soundness and completeness bridges (body-369).

Landed axiom-clean: `rightReembed_survivorComponent`.

Per the HALT: only the component section is proved; the sound/complete derivation + the
`ResolvedRightRegionValueCoreBridgeSupply` assembly (via body-274 + `hSurvivor`) is body-369; the forest/left bridges,
`hSurvivor`, and the carrier are UNTOUCHED.  No `T` / cover / `hround` / carrier here; body-346's recovered round-trip
is NOT reused (this is the forward-image analogue).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
`promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-368 — the right-sector component section.**  `rightReembed ∘ survivorComponent = id` on the
forward image, as an equality of `ResolvedFeynmanSubgraph G`. -/
theorem rightReembed_survivorComponent (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.1.elements} //
      y ∈ ResolvedCoassocSplitChoice.rightComponents q.1})
    (δ : {x // x ∈ rightDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : δ.1 = (survivorSupply_of_measure Measure G).survivorComponent q.1 γ) :
    rightReembed (fwdMapFilteredValue Fmem V q) δ = γ.1.1 := by
  apply ResolvedFeynmanSubgraph.ext
  · show δ.1.vertices = γ.1.1.vertices
    rw [hδ]; rfl
  · show δ.1.internalEdges = γ.1.1.internalEdges
    rw [hδ]; rfl
  · show δ.1.externalLegs = γ.1.1.externalLegs
    rw [hδ]; rfl

end GaugeGeometry.QFT.Combinatorial
