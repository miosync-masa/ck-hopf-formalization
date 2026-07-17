import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarCover

/-!
# R-6c-body-364 — conditional native `Δᵣ`-coassociativity from the multi-star cover (PROVED)

Three-hundred-and-sixty-fourth genuine-body step — the raid-boss re-entry.  Body-286's S-free top-level proof term
is mirrored verbatim, with its `R.toCover` replaced by body-363's canonical `toMultiStarCover`: the multi-star
concrete cover + body-272's free forward-quotient membership feed body-270's raid-boss bijection side, and its
`.coassoc_gen` returns native `Δᵣ`-coassociativity on `X x`.

This CONNECTS the multi-star concrete cover through the raid-boss to `coassoc_gen` — the value cover is the public
artifact (body-363), the round-trip `R`'s `let`-chain is not duplicated, forward-quotient codomain membership is
body-272's free projection, and `rep` / `repCD` / `rep_gen` appear ONLY as top-level conditional hypotheses (base
leaves), never as a facade inside the construction.  No `.ofLegacy`, no `Forward`, no phantom `S`.

Landed axiom-clean: `coassoc_gen_of_multiStar_model`.

Per the HALT: this is the CONDITIONAL theorem (its hypotheses are `I` / `P` / the two multi-star wirings + the base
leaves), NOT an unconditional result — Front-3's canonical model inhabitants (`hForest` / `hFT` `rfl` for the
multi-star `Tags`, `P`, and `I`'s own gates via body-361's `toRecoveredIdentitySupply`) stay to be discharged.  No
facade, no flat term, no `forgetHopf`, no rep/perm facade, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-364 — conditional native `Δᵣ`-coassociativity from the multi-star model.**  Body-286's raid-boss
adapter fed by body-363's `toMultiStarCover`. -/
theorem coassoc_gen_of_multiStar_model (M : ResolvedMultiStarDecontractionSupply D)
    (Fstar : ResolvedCanonicalStarFacts D) (OccInv : ResolvedForestOccurrenceInversionSupply M)
    (Measure : ResolvedMeasureLeafSupply D)
    {Fmem : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}
    (I : ResolvedMultiStarRecoveredIdentitySupply M Fstar Fmem V) (P : ResolvedCarrierProperProvider D)
    (hForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      (I.Tags.Closure.Assembly.Region.forestRecovered z).elements
        = (M.forestRecoveredMulti Fstar z).elements)
    (hFT : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
      (γ' : {x : ResolvedFeynmanSubgraph G // x ∈ (I.Tags.Closure.unionOuterValue z).1.elements})
      (h : γ'.1 ∈ (I.Tags.Closure.Assembly.Region.forestRecovered z).elements)
      (h' : γ'.1 ∈ (M.forestRecoveredMulti Fstar z).elements),
      I.Tags.forestTag z γ' h = M.forestTag Fstar z ⟨γ'.1, h'⟩)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (ResolvedFilteredBijectionSideSupply.mk Fmem V (M.toMultiStarCover Fstar OccInv Measure I P hForest hFT)
    (forwardQuotientMemValueOfValue Fmem V) carrier_isProperForest rep repCD rep_gen).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
