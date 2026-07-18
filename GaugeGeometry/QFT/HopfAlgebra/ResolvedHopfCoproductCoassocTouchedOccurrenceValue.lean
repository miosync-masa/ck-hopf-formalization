import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocTouchedOccurrenceConcrete

/-!
# R-6c-body-386 — bank-3b: the abstract-`V` adapter of the touched-collection theorem (PROVED)

Three-hundred-and-eighty-sixth genuine-body step — the thin ownership adapter that lifts body-385's concrete
touched-collection theorem to the ABSTRACT `V.Remnant.remnant.remnantComponent`.  The only new content is the body-384
`Wiring` gate used purely to transport the `HEq` from `V`'s remnant to the concrete one; the geometry (both inclusions
+ `promoted_star_agrees`) is entirely body-385's, invoked verbatim.

* `remnantComponent_heq_toConcrete` — the reusable `HEq` transport `V`'s remnant ⟶ concrete remnant (via `Wiring`);
* `touchedOuterComponents_of_occurrence_wired` — body-385 restated over `V.Remnant.remnant.remnantComponent`.

Per the HALT: NO new geometry; `Wiring.remnantComponent_eq` is used ONLY for the ownership transport; the sole geometric
datum is body-385's `promoted_star_agrees`; `OccInv` / the parent section / the forest bridge / the forward round-trip
are NOT used; NO full supply equality is required.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO
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

variable {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
  {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-386 — the ownership `HEq` transport.**  Under the body-384 wiring, an `HEq` from `V`'s abstract remnant
component to any target carries over to the concrete contracted-source remnant. -/
theorem remnantComponent_heq_toConcrete
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    HEq ((Concrete q.1).remnantComponent o) δ.1 :=
  (heq_of_eq (Wiring.remnantComponent_eq q.1 o).symm).trans hδ

/-- **R-6c-body-386 — the abstract-`V` touched-collection theorem.**  Body-385 restated over the abstract
`V.Remnant.remnant.remnantComponent`, via the body-384 wiring transport. -/
theorem touchedOuterComponents_of_occurrence_wired
    (Fstar : ResolvedCanonicalStarFacts D)
    (Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete)
    (StarProm : ResolvedPromotedStarCoherenceValueSupply Fmem V)
    {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G)
    (o : ResolvedCoassocSplitChoice.ForestChoiceOccurrence q.1)
    (δ : {x // x ∈ forestDomain (fwdMapFilteredValue Fmem V q)})
    (hδ : HEq (V.Remnant.remnant.remnantComponent q.1 o) δ.1) :
    touchedOuterComponents (fwdMapFilteredValue Fmem V q) δ.1
      = (ResolvedAdmissibleSubgraph.promote o.γ.1 o.B.1).elements :=
  touchedOuterComponents_of_occurrence Fstar Concrete StarProm q o δ
    (remnantComponent_heq_toConcrete Wiring q o δ hδ)

end GaugeGeometry.QFT.Combinatorial
