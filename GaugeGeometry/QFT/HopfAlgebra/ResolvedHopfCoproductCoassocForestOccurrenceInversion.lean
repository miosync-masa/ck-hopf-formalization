import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagOccurrenceFloor

/-!
# R-6c-body-343 — occurrence inversion: `forestTag_agrees` + ForestIdx transport become THEOREMS (PROVED)

Three-hundred-and-forty-third genuine-body step — the C-finish.  The single remaining occurrence datum is
isolated as the honest GEOMETRIC leaf `occurrence_inner_elements` (a raw elements equality), and both the
`ForestIdx` transport (culprit D) and `forestTag_agrees` (culprit-A-side) are DERIVED from it as theorems.

## The split (elements datum → transport theorem)

The supplied leaf is an elements-only fact — de-contracting `δ`'s touched components recovers `q`'s chosen
sub-forest, at the level of the underlying admissible subgraphs:

```lean
occurrence_inner_elements :
  (M.innerIdx z δ).1.elements = (transportForestIdx (…hparent…) o.B).1.elements
```

Everything above it is mechanical:

1. `ResolvedAdmissibleSubgraph.ext_elements` — lift the elements equality to `.1` subgraph equality;
2. `Subtype.ext` — the two `ForestIdx`s already exist (carrier membership is proof-irrelevant), so equal `.1`
   gives equal `ForestIdx` (`(D.supply _).ForestIdx = {A // A ∈ carrier}`, no membership re-request);
3. `transportForestIdx_heq` — the transport is heterogeneously the identity;
4. ⟹ `innerIdx_occurrence : HEq (M.innerIdx z δ) o.B` (culprit D discharged);
5. body-342's `forestTag_agrees_of_innerIdx_occurrence` ⟹ `forestTag_agrees_multi`.

Landed (all axiom-clean):

* `ResolvedForestOccurrenceInversionSupply` — the geometric leaf (elements-only, no carrier re-request);
* `innerIdx_occurrence` — the `ForestIdx` transport theorem (culprit D);
* `forestTag_agrees_multi` — the exact-B `forestTag_agrees` theorem.

Per the HALT: the parent equality `hparent` is a hypothesis (derived from forest source / D4 upstream, NOT a
field); the datum requests NO carrier membership; no global forward round-trip / forward quotient is used;
`forestTag_agrees` and the `ForestIdx` transport are now theorems modulo the single elements leaf.  No facade,
no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-343 — the occurrence-inversion geometric leaf.**  The ONLY supplied fact: at a matched
`(δ, o)` (parent `M.parent z δ = o.γ.1`), the de-contracted inner forest's components equal the occurrence's
chosen sub-forest's components — a raw elements equality, no carrier membership re-requested. -/
structure ResolvedForestOccurrenceInversionSupply (M : ResolvedMultiStarDecontractionSupply D) where
  /-- De-contracting `δ`'s touched components recovers `q`'s chosen sub-forest (elements level). -/
  occurrence_inner_elements : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
    (hparent : M.parent z δ = o.γ.1),
    (M.innerIdx z δ).1.elements
      = (transportForestIdx
          (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent.symm) o.B).1.elements

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-343 — the `ForestIdx` transport theorem (culprit D).**  The de-contracted inner index equals
the occurrence's chosen sub-forest, heterogeneously — derived from the elements leaf by `ext_elements` +
`Subtype.ext` + `transportForestIdx_heq`. -/
theorem innerIdx_occurrence (S : ResolvedForestOccurrenceInversionSupply M)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
    (hparent : M.parent z δ = o.γ.1) :
    HEq (M.innerIdx z δ) o.B := by
  have heq : M.innerIdx z δ
      = transportForestIdx
          (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent.symm) o.B :=
    Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements (S.occurrence_inner_elements z δ s o hparent))
  rw [heq]
  exact transportForestIdx_heq _ _

/-- **R-6c-body-343 — the exact-B `forestTag_agrees` theorem.**  Composing body-342's reduction with the
transport theorem: the constructed tag at the recovered parent equals the occurrence's chosen sub-forest. -/
theorem forestTag_agrees_multi (S : ResolvedForestOccurrenceInversionSupply M)
    (Fstar : ResolvedCanonicalStarFacts D) (Measure : ResolvedMeasureLeafSupply D)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
    (hparent : M.parent z δ = o.γ.1)
    (hmem : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements) :
    HEq (M.forestTag Fstar z ⟨M.parent z δ, hmem⟩) o.B :=
  M.forestTag_agrees_of_innerIdx_occurrence Fstar Measure z δ hmem o.B
    (M.innerIdx_occurrence S z δ s o hparent)

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
