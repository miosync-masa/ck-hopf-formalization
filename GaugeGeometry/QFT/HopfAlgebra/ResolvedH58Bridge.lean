import GaugeGeometry.QFT.HopfAlgebra.Coassoc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Weight

/-!
# Resolved ↔ flat H5.8 bridge (Track R-4-superfull, Step 7L Part B)

The single contact point between the standalone resolved track and the flat H5.8
machinery.  Using the public bridge wrappers exposed from `Coassoc` (Step 7L Part A),
we construct a `ResolvedFlatH58WeightAlignment` and obtain the concrete H5.8 sum-reindex
identity resolved-side.

The flat split-term agreement is supplied as the hypothesis `hTerm` (stated entirely via
the public wrappers); it is the public form of `forestComponentSplitPhi_term_eq_of_split`
— a non-facade algebraic fact.  Everything else (the resolved finite layer, the
resolved→flat index maps, the commutation squares) is resolved-side data.
-/

set_option linter.unusedSectionVars false

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ H : FeynmanGraph, DivergenceMeasure H]
         [∀ H : FeynmanGraph, IsPermInvariantDivergence H]
         [∀ H : FeynmanGraph, IsIsoInvariantDivergence H]
         [∀ H : FeynmanGraph, Fintype (FeynmanSubgraph H)]
         [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]

/-- **Concrete flat alignment** for a resolved finite branch-map layer, built from the
public H5.8 bridge wrappers.  Reduces the resolved concrete H5.8 reindex to: the
resolved→flat index maps, their landing in the flat split index, the commutation
squares, and the flat split-term agreement `hTerm`. -/
noncomputable def resolvedH58WeightAlignmentOfFlat
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen)
    (FL : ResolvedFiniteBranchMapLayer)
    (flatImageOf : FL.layer.Image → h58BridgeQuotientSigma g)
    (forestSplitOf : FL.layer.ForestIdx → h58BridgeSplitChoiceSigma g)
    (mixedSplitOf : FL.layer.MixedIdx → h58BridgeSplitChoiceSigma g)
    (forestSplitOf_mem : ∀ q, forestSplitOf q ∈ h58BridgeSplitChoiceIndex g)
    (mixedSplitOf_mem : ∀ q, mixedSplitOf q ∈ h58BridgeSplitChoiceIndex g)
    (forest_comm : ∀ q,
      flatImageOf (FL.layer.forestImage q) = h58BridgeSplitPhi g (forestSplitOf q))
    (mixed_comm : ∀ q,
      flatImageOf (FL.layer.mixedImage q) = h58BridgeSplitPhi g (mixedSplitOf q))
    (hTerm : ∀ s ∈ h58BridgeSplitChoiceIndex g,
      h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)) :
    ResolvedFlatH58WeightAlignment FL (HopfH ⊗[ℚ] (HopfH ⊗[ℚ] HopfH)) where
  FlatImage := h58BridgeQuotientSigma g
  SplitIdx := h58BridgeSplitChoiceSigma g
  splitMem := fun s => s ∈ h58BridgeSplitChoiceIndex g
  flatTerm := h58BridgeQuotientTerm g
  splitTerm := h58BridgeSplitChoiceTerm g
  flatBranch := h58BridgeSplitPhi g
  splitTerm_eq := hTerm
  flatImageOf := flatImageOf
  forestSplitOf := forestSplitOf
  mixedSplitOf := mixedSplitOf
  forestSplitOf_mem := forestSplitOf_mem
  mixedSplitOf_mem := mixedSplitOf_mem
  forest_comm := forest_comm
  mixed_comm := mixed_comm

/-- **Concrete resolved H5.8 sum-reindex.**  The flat quotient-term sum over the resolved
image carrier splits into the flat split-term sums over the resolved forest and mixed
branches — the H5.8 reindexing identity, resolved-side, with the actual flat tensor
terms. -/
theorem resolvedH58ConcreteWeightSumReindex
    [IsDivergencePreservedByAdmissibleForestContract] (g : HopfGen)
    (FL : ResolvedFiniteBranchMapLayer)
    (flatImageOf : FL.layer.Image → h58BridgeQuotientSigma g)
    (forestSplitOf : FL.layer.ForestIdx → h58BridgeSplitChoiceSigma g)
    (mixedSplitOf : FL.layer.MixedIdx → h58BridgeSplitChoiceSigma g)
    (forestSplitOf_mem : ∀ q, forestSplitOf q ∈ h58BridgeSplitChoiceIndex g)
    (mixedSplitOf_mem : ∀ q, mixedSplitOf q ∈ h58BridgeSplitChoiceIndex g)
    (forest_comm : ∀ q,
      flatImageOf (FL.layer.forestImage q) = h58BridgeSplitPhi g (forestSplitOf q))
    (mixed_comm : ∀ q,
      flatImageOf (FL.layer.mixedImage q) = h58BridgeSplitPhi g (mixedSplitOf q))
    (hTerm : ∀ s ∈ h58BridgeSplitChoiceIndex g,
      h58BridgeSplitChoiceTerm g s = h58BridgeQuotientTerm g (h58BridgeSplitPhi g s)) :
    ∑ z ∈ FL.imageCarrier, h58BridgeQuotientTerm g (flatImageOf z) =
      (∑ q ∈ FL.forestCarrier, h58BridgeSplitChoiceTerm g (forestSplitOf q)) +
      (∑ q ∈ FL.mixedCarrier, h58BridgeSplitChoiceTerm g (mixedSplitOf q)) :=
  (resolvedH58WeightAlignmentOfFlat g FL flatImageOf forestSplitOf mixedSplitOf
    forestSplitOf_mem mixedSplitOf_mem forest_comm mixed_comm hTerm).sum_reindex

end GaugeGeometry.QFT.Combinatorial
