import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardQuotientMultiAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMemSupplyReplumb

/-!
# R-6c-body-361 — the recovered-identity root: three identities under one shared `Tags` (PROVED)

Three-hundred-and-sixty-first genuine-body step — the consolidation.  The forward-outer identity (body-341), the
forward-quotient value `HEq` (body-360), and the exact-`B` forest-tag agreement (body-343) all live over the SAME
`Tags : ResolvedRegionTagValueSupply`.  Bundling them into one `ResolvedMultiStarRecoveredIdentitySupply` (which
`extends` body-313's `ResolvedRawForwardValueSupply` and adds only the forest-tag leaf) means body-362 consumes a
single record with a single `Tags` — no `Tags`-equality transport re-appears downstream.

This is a **derived identity supply**, NOT a new model assumption: the construction `toRecoveredIdentitySupply`
plugs body-360's `forward_quotient_value_wired` (quotient) and body-343's `forestTag_agrees_multi` (exact-`B`) into
the caller-supplied `Tags` and its outer identity (which the caller sets to body-341's
`multiStarRegionTagValueSupply` / `multiStar_selectedOuterRawOf_eq`).  Every field traces to a theorem; the only
inputs are the already-named Front-3 gates (`houter` 341, `hRight` 347, `hForest` 359, `hround` 358, `hSurvivor`,
`S` 343's inversion datum).

Landed axiom-clean: `ResolvedMultiStarRecoveredIdentitySupply`, `toRawForwardValueSupply` (the body-313 converter),
`toRecoveredIdentitySupply` (the construction).

Per the HALT: only the identity-root record + converter + construction is built; membership / `Data` / cover are
body-362+; the full `V.Remnant` provider is NOT claimed complete.  No forward hidden round-trip, no facade, no flat
term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-361 — the recovered-identity root.**  Body-313's raw-forward root (`Tags`, forward-outer,
forward-quotient) plus the exact-`B` forest-tag agreement (body-343), all under one shared `Tags`. -/
structure ResolvedMultiStarRecoveredIdentitySupply (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D)
    extends ResolvedRawForwardValueSupply F V where
  /-- The exact-`B` leaf (body-343): the model's `forestTag` agrees with any occurrence's index. -/
  forestTag_agrees : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (s : ResolvedCoassocSplitChoice D G) (o : s.ForestChoiceOccurrence)
    (_hparent : M.parent z δ = o.γ.1)
    (hmem : M.parent z δ ∈ (M.forestRecoveredMulti Fstar z).elements),
    HEq (M.forestTag Fstar z ⟨M.parent z δ, hmem⟩) o.B

namespace ResolvedMultiStarRecoveredIdentitySupply

variable {M : ResolvedMultiStarDecontractionSupply D} {Fstar : ResolvedCanonicalStarFacts D}
  {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-361 — the body-313 converter.**  Drop the forest-tag leaf; the raw-forward root (`Tags`,
forward-outer, forward-quotient) is exactly the `extends` projection. -/
def toRawForwardValueSupply (I : ResolvedMultiStarRecoveredIdentitySupply M Fstar F V) :
    ResolvedRawForwardValueSupply F V :=
  I.toResolvedRawForwardValueSupply

end ResolvedMultiStarRecoveredIdentitySupply

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-361 — the derived recovered-identity supply.**  Plugs body-360's `forward_quotient_value_wired`
and body-343's `forestTag_agrees_multi` into the caller's `Tags` + outer identity (set to body-341's). -/
noncomputable def toRecoveredIdentitySupply (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedForestOccurrenceInversionSupply M) (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V)
    (houter : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (T.recoveredPreimageValue z) = z.1.1)
    (hRight : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (T.Closure.Assembly.Region.rightRecovered z).elements
        = (rightDomain z).attach.image (rightReembed z))
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (T.Closure.Assembly.Region.forestRecovered z).elements = (M.forestRecoveredMulti Fstar z).elements)
    (hround : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ : {x : {y : ResolvedFeynmanSubgraph G //
          y ∈ (T.recoveredPreimageValue z).1.1.elements} // x ∈
          ResolvedCoassocSplitChoice.forestComponents (T.recoveredPreimageValue z)})
      (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) //
          x ∈ forestDomain z}),
      (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).γ.1
        = M.parent z δ →
      HEq (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ).B
        (M.innerIdx z δ) →
      HEq (V.Remnant.remnant.remnantComponent (T.recoveredPreimageValue z)
        (ResolvedCoassocSplitChoice.forestComponentOccurrence (T.recoveredPreimageValue z) γ)) δ.1)
    (hSurvivor : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (V.Survivor.survivor.rightSurvivorForest (T.recoveredPreimageValue z)).elements
        = ((survivorSupply_of_measure Measure G).rightSurvivorForest (T.recoveredPreimageValue z)).elements) :
    ResolvedMultiStarRecoveredIdentitySupply M Fstar Fmem V where
  toResolvedRawForwardValueSupply :=
    { Tags := T
      forward_outer_value := houter
      forward_quotient_value := fun z =>
        M.forward_quotient_value_wired Fstar S Measure T houter hRight hForest hround hSurvivor z }
  forestTag_agrees := fun z δ s o hparent hmem =>
    M.forestTag_agrees_multi S Fstar Measure z δ s o hparent hmem

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
