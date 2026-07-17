import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocHardcodedStarSwap
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestOccurrenceInversion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRemnant

/-!
# R-6c-body-358 — the remnant component round-trip: `HEq (remnantComponent recovered o) δ.1` (PROVED)

Three-hundred-and-fifty-eighth genuine-body step — the remnant half's occurrence round-trip.  A forest-choice
occurrence `o` whose parent is `M.parent z δ` and whose `B` is `M.innerIdx z δ` (heterogeneously, body-343)
re-contracts to `δ`: its `contractedSourceGraph = o.B.1.contractWithStars (D.starOf o.γ.1.tRFG o.B.1)` has `δ`'s
three data (body-357's hardcoded re-contract, after the dependent transport is closed inside each DATA
projection — never carrying `contractedSourceGraph` wholesale).  `remnantComponent` re-embeds it (data `rfl`),
and body-341's `houter` aligns the ambient, so body-346's `subgraph_heq_of_data` gives the `HEq`.

Landed axiom-clean:

* `contractedSourceGraph_vertices_eq` / `_internalEdges_eq` / `_externalLegs_eq` — the three data (subst the
  parent-graph equality, `eq_of_heq` the index, land on body-357);
* `remnantComponent_roundtrip` — `HEq (Remnant.remnantComponent o) δ.1`.

Per the HALT: only the component construction / round-trip is proved; the full `V.Remnant` provider (with its
`remnantInj` / `remnantGen` / factor fields) is NOT claimed complete; the collection `HEq` (body-359, `forestSource_parent`
+ this) and the assembly are next; no forward quotient / global forward round-trip.  No facade, no flat term, no
`forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-358 — vertices data helper** (dependent transport closed on the projection). -/
theorem contractedSourceGraph_vertices_helper (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedInnerStarCoherenceSupply M) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {H : ResolvedFeynmanGraph} (B' : (D.supply H).ForestIdx)
    (hH : H = (M.parent z δ).toResolvedFeynmanGraph) (hB' : HEq B' (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card) :
    (B'.1.contractWithStars (D.starOf H B'.1)).vertices = δ.1.vertices := by
  subst hH
  rw [eq_of_heq hB']
  exact M.recontract_hardcoded_vertices Fstar S z δ hConn hPos

/-- **R-6c-body-358 — internal edges data helper.** -/
theorem contractedSourceGraph_internalEdges_helper (S : ResolvedInnerStarCoherenceSupply M)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {H : ResolvedFeynmanGraph} (B' : (D.supply H).ForestIdx)
    (hH : H = (M.parent z δ).toResolvedFeynmanGraph) (hB' : HEq B' (M.innerIdx z δ)) :
    (B'.1.contractWithStars (D.starOf H B'.1)).internalEdges = δ.1.internalEdges := by
  subst hH
  rw [eq_of_heq hB']
  exact M.recontract_hardcoded_internalEdges S z δ

/-- **R-6c-body-358 — external legs data helper.** -/
theorem contractedSourceGraph_externalLegs_helper (S : ResolvedInnerStarCoherenceSupply M)
    (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {H : ResolvedFeynmanGraph} (B' : (D.supply H).ForestIdx)
    (hH : H = (M.parent z δ).toResolvedFeynmanGraph) (hB' : HEq B' (M.innerIdx z δ)) :
    (B'.1.contractWithStars (D.starOf H B'.1)).externalLegs = δ.1.externalLegs := by
  subst hH
  rw [eq_of_heq hB']
  exact M.recontract_hardcoded_externalLegs S z δ

/-- **R-6c-body-358 — the remnant component round-trip.**  `HEq (Remnant.remnantComponent o) δ.1`. -/
theorem remnantComponent_roundtrip (Fstar : ResolvedCanonicalStarFacts D)
    (S : ResolvedInnerStarCoherenceSupply M) (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    {s : ResolvedCoassocSplitChoice D G} (Remnant : ResolvedConcreteRemnantReembedSupply D G s)
    (o : s.ForestChoiceOccurrence)
    (hparent : o.γ.1 = M.parent z δ) (hidx : HEq o.B (M.innerIdx z δ))
    (hConn : (touchedLocalComponent z δ.1).forget.IsConnected)
    (hPos : 0 < (touchedLocalComponent z δ.1).internalEdges.card)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s = z.1.1) :
    HEq (Remnant.remnantComponent o) δ.1 :=
  subgraph_heq_of_data (congrArg (fun A => A.contractWithStars (D.starOf G A)) houter)
    (Remnant.remnantComponent o) δ.1
    (M.contractedSourceGraph_vertices_helper Fstar S z δ o.B
      (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx hConn hPos)
    (M.contractedSourceGraph_internalEdges_helper S z δ o.B
      (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx)
    (M.contractedSourceGraph_externalLegs_helper S z δ o.B
      (congrArg ResolvedFeynmanSubgraph.toResolvedFeynmanGraph hparent) hidx)

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
