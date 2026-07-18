import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecontractSection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComplementEdgesMono

/-!
# R-6c-body-378 — bank-4a: the inner raw is mathematically a proper forest (PROVED)

Three-hundred-and-seventy-eighth genuine-body step — the value side of the carrier boundary.  `innerRaw` is a PROPER
FOREST, proved from the INPUT carrier's properness `P` (source outer `z.1.1` and quotient `z.2.1`) — NEVER from the
target `innerRaw_mem`, so the argument is non-circular.  `toInner` keeps each component's three data (`= A.1`'s), and
`innerRaw.elements = touchedOuterComponents.attach.image toInner`, so the outer components' non-emptiness / positivity
transport by `rfl`; the complement-edge count reduces (body-353) to `δ.internalEdges.card`, positive by the quotient
carrier's properness.

Landed axiom-clean: `innerRaw_isProperForest`.

Per the HALT: only properness is proved; it uses `P` on the SOURCE outer / quotient carrier, never the target
`innerRaw_mem` inverse; no `Finset.univ`, no forget-section, no subtype-`.2` bypass; the body-353 chain is applied to
the raw `innerRaw … (Core.legLift) (Core.hE) (Core.hL)`, not re-keyed through `innerRaw_mem`.  This fixes the carrier
boundary: `innerRaw` is proper; only the supplied finite carrier's enumeration of its value remains (body-377's
closure field).  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-378 — the inner raw is a proper forest** (from the input carrier's properness). -/
theorem innerRaw_isProperForest (P : ResolvedCarrierProperProvider D)
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z}) :
    (Core.innerRaw z δ).IsProperForest := by
  have houter := P.carrier_isProperForest G z.1.1 z.1.2
  have hquot := P.carrier_isProperForest _ z.2.1 z.2.2
  have hδz : δ.1 ∈ z.2.1.elements := (Finset.mem_filter.mp δ.2).1
  have hne : (touchedOuterComponents z δ.1).Nonempty :=
    touchedOuterComponents_nonempty z (Finset.mem_filter.mp δ.2).2
  have helem : (Core.innerRaw z δ).elements
      = (touchedOuterComponents z δ.1).attach.image
        (toInner z δ.1 (Core.legLift z δ) (Core.hE G) (Core.hL G)) := innerRaw_elements ..
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- IsNonempty : elements.Nonempty
    rw [ResolvedAdmissibleSubgraph.IsNonempty, helem]
    exact Finset.image_nonempty.mpr (Finset.attach_nonempty_iff.mpr hne)
  · -- HasNonemptyComponents
    intro γ hγ
    rw [helem] at hγ
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hγ
    show 0 < A.1.vertexCount
    exact houter.2.1 A.1 (mem_touchedOuterComponents.mp A.2).1
  · -- 0 < internalEdges.card
    obtain ⟨A, hA⟩ := hne
    have hApos : 0 < A.internalEdges.card :=
      houter.2.2.2.1 A (mem_touchedOuterComponents.mp hA).1
    have hmemInner : toInner z δ.1 (Core.legLift z δ) (Core.hE G) (Core.hL G) ⟨A, hA⟩
        ∈ (Core.innerRaw z δ).elements := by
      rw [helem]; exact Finset.mem_image.mpr ⟨⟨A, hA⟩, Finset.mem_attach _ _, rfl⟩
    have hle : A.internalEdges ≤ (Core.innerRaw z δ).internalEdges :=
      ResolvedAdmissibleSubgraph.internalEdges_le_of_mem (Core.innerRaw z δ) hmemInner
    exact lt_of_lt_of_le hApos (Multiset.card_le_card hle)
  · -- HasPositiveInternalEdgesComponents
    intro γ hγ
    rw [helem] at hγ
    obtain ⟨A, -, rfl⟩ := Finset.mem_image.mp hγ
    show 0 < A.1.internalEdges.card
    exact houter.2.2.2.1 A.1 (mem_touchedOuterComponents.mp A.2).1
  · -- 0 < complementEdges.card
    have hcard : (Core.innerRaw z δ).complementEdges.card = δ.1.internalEdges.card := by
      rw [show (Core.innerRaw z δ).complementEdges
          = (innerRaw z δ.1 (Core.legLift z δ) (Core.hE G) (Core.hL G)).complementEdges from rfl,
        innerRaw_complementEdges_eq,
        ← Multiset.card_map ((touchedOuterForest z δ.1).retargetEdge (D.starOf G z.1.1)),
        quotientEdgePreimage_map, touchedLocalComponent_internalEdges]
    rw [hcard]
    exact hquot.2.2.2.1 δ.1 hδz

end GaugeGeometry.QFT.Combinatorial
