import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantCollection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorCollection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientPartitionMulti
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank

/-!
# R-6c-body-360 — forward quotient assembly: `toForwardQuotientMultiSupply` + value HEq (PROVED)

Three-hundred-and-sixtieth genuine-body step — the forward-quotient assembly, quotient-only per the HALT.  The
codomain partition (body-344) plus the two collection `HEq`s (survivor body-347, remnant body-359) assemble the
`quotient_elements_heq` field of body-344's `ResolvedForwardQuotientMultiSupply`, closed by body-291's
`heq_of_membership_split` with `V.union_eq` supplying the domain split.

**Status gate (per the discipline).**  `V.union_eq` only says the raw quotient forest splits into `V`'s OWN
`Survivor.survivor.rightSurvivorForest` ⊔ `Remnant.remnant.remnantForest`.  The remnant side lands directly:
body-359 is stated over ANY `ResolvedRemnantComponentSupply`, so instantiating it at `V.Remnant.remnant` matches
`V.union_eq`'s remnant term with NO extra wiring.  The survivor side needs one honest gate `hSurvivor` — body-347
is fixed to `survivorSupply_of_measure Measure`, so identifying it with `V.Survivor.survivor` is a supplied
equality (an `rfl` once a concrete `V` is built with that survivor; left as a gate here, not hidden inside
`V.union_eq`).

Landed axiom-clean: `toForwardQuotientMultiSupply`, `forward_quotient_value_wired`
(`HEq (V.quotientForestRaw recovered) z.2`).

Per the HALT: only the quotient assembly + value `HEq` is built; the cover / `coassoc_gen` is body-361+; the
supplied gates (`houter` body-341, `hRight` body-347, `hForest` body-359, `hround` body-358, `hSurvivor` the
survivor wiring, `S` body-343's inversion datum) stay explicit; the full `V.Remnant` provider is NOT claimed
complete.  No forward quotient hidden round-trip, no facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D)
  {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-360 — the forward-quotient multi-star supply**, assembled from the codomain partition
(body-344), the survivor collection (body-347), and the remnant collection (body-359). -/
noncomputable def toForwardQuotientMultiSupply (Fstar : ResolvedCanonicalStarFacts D)
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
    ResolvedForwardQuotientMultiSupply V T where
  quotient_elements_heq := fun {G} z => by
    have hs : HEq (V.Survivor.survivor.rightSurvivorForest (T.recoveredPreimageValue z)).elements
        (rightDomain z) := by
      rw [hSurvivor z]
      exact ResolvedRegionTagValueSupply.rightSurvivorForest_elements_heq Measure T z (houter z)
        (hRight z)
    have hr : HEq (V.Remnant.remnant.remnantForest (T.recoveredPreimageValue z)).elements
        (forestDomain z) :=
      M.remnantForest_elements_heq Fstar S T z V.Remnant.remnant (houter z) (hForest z) (hround z)
    refine heq_of_membership_split (houter z) (fun x => ?_) (fun x => ?_) hs hr
    · rw [V.union_eq (T.recoveredPreimageValue z), ResolvedAdmissibleSubgraph.union_elements]
      exact @Finset.mem_union _ (Classical.decEq _) _ _ _
    · rw [← rightDomain_union_forestDomain z]
      simp only [Finset.mem_union]

/-- **R-6c-body-360 — the forward-quotient value HEq**, `HEq (V.quotientForestRaw recovered) z.2`,
via body-344's `forward_quotient_value_multi` on the assembled supply. -/
theorem forward_quotient_value_wired (Fstar : ResolvedCanonicalStarFacts D)
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
        = ((survivorSupply_of_measure Measure G).rightSurvivorForest (T.recoveredPreimageValue z)).elements)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    HEq (V.quotientForestRaw (T.recoveredPreimageValue z)) z.2 :=
  forward_quotient_value_multi
    (M.toForwardQuotientMultiSupply Fstar S Measure T houter hRight hForest hround hSurvivor) houter z

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
