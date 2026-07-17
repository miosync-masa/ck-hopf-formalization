import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSurvivorTagPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank

/-!
# R-6c-body-346 — survivor round-trip: `survivorComponent(recovered)(rightReembed δ) = δ` (HEq, PROVED)

Three-hundred-and-forty-sixth genuine-body step — stage 2 of the survivor collection alignment.  The concrete
survivor re-embedding (body-302, `G → contracted`) undoes body-337's `rightReembed` (`contracted → G`): both
carry the SAME carrier data (`rightReembed δ` is `δ`'s data, star-avoiding, retarget-identity), so the
round-trip is `δ` back, heterogeneously over the contracted graph aligned by body-341's `houter`.

## The strategy (body-339 discipline)

The ambient graph is abstracted into `subgraph_heq_of_data` (a free-variable `subst` helper): given a graph
equality `H₁ = H₂` and the three carrier-data equalities (`vertices` / `internalEdges` / `externalLegs`, whose
TYPES do not depend on the ambient), it lifts to `HEq`.  `houter` supplies the graph equality
(`selectedOuterContractGraph(recovered) = z.1.1.contractWithStars`), and the data equalities are `rfl`-chains
through the two re-embeddings (`survivorReembedOfDisjoint` and `rightReembed` both pass `vertices`/`edges`/`legs`
through, then body-337's `rightReembed_vertices`).  The dependent survivor term is NOT `rcases`-d — the graph
equality is transported once, inside the helper.

Landed axiom-clean:

* `subgraph_heq_of_data` — `H₁ = H₂` + carrier-data equalities ⟹ `HEq` of the subgraphs;
* `rightSurvivor_roundtrip` — `HEq (survivorComponent(recovered) γ) δ.1` for any `γ` with `γ.1.1 = rightReembed z δ`.

Per the HALT: only stage 2 (the round-trip) is proved; the collection `HEq` (stage 3, via body-345 + this) is
next; the witness `γ` (with `γ.1.1 = rightReembed δ`) is a HYPOTHESIS here (constructed from body-345 in the
assembly), not built; `V` is not wired, the six bridge gates / carrier membership / remnant geometry are NOT
used.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-346 — subgraph `HEq` from a graph equality + carrier data equalities.**  The three data fields
are ambient-independent (`Finset VertexId` / `Multiset _`), so `subst` on the graph equality reduces to `ext`. -/
theorem subgraph_heq_of_data {H₁ H₂ : ResolvedFeynmanGraph} (h : H₁ = H₂)
    (γ₁ : ResolvedFeynmanSubgraph H₁) (γ₂ : ResolvedFeynmanSubgraph H₂)
    (hv : γ₁.vertices = γ₂.vertices) (hi : γ₁.internalEdges = γ₂.internalEdges)
    (hl : γ₁.externalLegs = γ₂.externalLegs) : HEq γ₁ γ₂ := by
  subst h
  exact heq_of_eq (ResolvedFeynmanSubgraph.ext hv hi hl)

namespace ResolvedRegionTagValueSupply

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-346 — the survivor round-trip.**  `survivorComponent(recovered) γ = δ` heterogeneously, for any
witness `γ` at `rightReembed z δ`.  Data: the two re-embeddings pass carrier data through; graph: `houter`. -/
theorem rightSurvivor_roundtrip (Measure : ResolvedMeasureLeafSupply D)
    (T : ResolvedRegionTagValueSupply Fmem V) {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (houter : (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf
      (T.recoveredPreimageValue z) = z.1.1)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ rightDomain z})
    (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ (T.recoveredPreimageValue z).1.1.elements} //
      y ∈ ResolvedCoassocSplitChoice.rightComponents (T.recoveredPreimageValue z)})
    (hγ : γ.1.1 = rightReembed z δ) :
    HEq ((survivorSupply_of_measure Measure G).survivorComponent (T.recoveredPreimageValue z) γ) δ.1 := by
  refine subgraph_heq_of_data
    (congrArg (fun A => A.contractWithStars (D.starOf G A)) houter) _ δ.1 ?_ ?_ ?_
  · show γ.1.1.vertices = δ.1.vertices
    rw [hγ]; exact rightReembed_vertices z δ
  · show γ.1.1.internalEdges = δ.1.internalEdges
    rw [hγ]; rfl
  · show γ.1.1.externalLegs = δ.1.externalLegs
    rw [hγ]; rfl

end ResolvedRegionTagValueSupply

end GaugeGeometry.QFT.Combinatorial
