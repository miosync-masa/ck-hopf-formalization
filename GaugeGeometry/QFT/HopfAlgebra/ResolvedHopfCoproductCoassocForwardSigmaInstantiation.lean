import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientBody

/-!
# R-6c-body-114 — forward σ-cover instantiation: the assembly's FORWARD block from existing machinery

Hundred-and-fourteenth genuine-body step, instantiating the FORWARD block (`imageSupply` / `quotientRaw` /
`quotient_mem`) of body-113's `ResolvedOuterMixingAssemblySupply` from the existing σ-cover construction.  The
forward map is already `⟨selectedOuterOf, quotientForestOf⟩` (bodies 105/106), so its data comes from the
existing selected-outer image supply and the full-grain quotient supply; the only genuinely-remaining forward
obligation is the quotient forest's carrier membership.

## The σ-cover forward chain

`ResolvedForwardSigmaInstantiationSupply` bundles the existing forward supplies:

* `imageSupply : ∀ G, ResolvedCoassocSelectedOuterImageSupply D G` — the selected-outer map `A_target = leftOf ∪
  promotedOf` (`SelectedOuterBridge`);
* `sigmaSupply : ∀ G, ResolvedCoassocSigmaDataSupply D G (imageSupply G)` — the σ-cover data over the selected
  outer forest (`parentsOf` + `containsAoutEdges` / `starFresh` / `componentPositiveEdges`, `QuotientBody`);
* `fullQuotient : ∀ G, ResolvedCoassocFullQuotientSupply D G (imageSupply G) (sigmaSupply G)` — the full-grain
  quotient image (remnant ⊔ right survivors), giving `quotientForestOf` (`QuotientBody` 97);
* `quotient_mem` — the quotient forest lies in the quotient graph's carrier (the isolated proper-forest
  obligation).

Then the assembly's FORWARD fields are:

* `imageSupplyField := imageSupply`;
* `quotientRawField G q := (fullQuotient G).quotientForestOf q` — the existing de-contraction quotient forest,
  of exactly the assembly's `quotientRaw` type;
* `quotient_memField := quotient_mem`.

## What remains (isolated)

`quotient_mem` — that `quotientForestOf q` is a carrier forest of the quotient graph — is the sole forward leaf
not already provided by the existing construction (the existing `quotientForestOf` carries only the
`isForestByStar` discriminator witness, not carrier membership).  So the FORWARD block reduces to the existing
`selectedOuter` / `quotientForestOf` construction plus this one membership fact.

Per the HALT: only the FORWARD block is instantiated; `quotient_mem` is isolated as the remaining forward leaf;
the backward / selection / contract fields are untouched; no proper-forest / CD proof is discharged.

Landed:

* `ResolvedForwardSigmaInstantiationSupply D` — the σ-cover forward chain (`imageSupply` / `sigmaSupply` /
  `fullQuotient` / `quotient_mem`);
* `.imageSupplyField` / `.quotientRawField` / `.quotient_memField` — the assembly's FORWARD fields.

Partial-instantiation body (no `coassoc_gen`; feeds the FORWARD block of body-113's assembly).  No facade, no
flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-114 — the forward σ-cover instantiation supply.**  The existing selected-outer image supply, the
σ-cover data, and the full-grain quotient supply, plus the quotient forest's carrier membership — from which the
assembly's FORWARD block (`imageSupply` / `quotientRaw` / `quotient_mem`) is filled. -/
structure ResolvedForwardSigmaInstantiationSupply (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply (`A_target = leftOf ∪ promotedOf`). -/
  imageSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G
  /-- The σ-cover data over the selected outer forest. -/
  sigmaSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSigmaDataSupply D G (imageSupply G)
  /-- The full-grain quotient image (remnant ⊔ right survivors), giving `quotientForestOf`. -/
  fullQuotient : ∀ (G : ResolvedFeynmanGraph),
    ResolvedCoassocFullQuotientSupply D G (imageSupply G) (sigmaSupply G)
  /-- The quotient forest lies in the quotient graph's carrier (the isolated forward leaf). -/
  quotient_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (fullQuotient G).quotientForestOf q ∈ D.carrier (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))

/-- **R-6c-body-114 — the assembly's `imageSupply` field.** -/
def ResolvedForwardSigmaInstantiationSupply.imageSupplyField
    (S : ResolvedForwardSigmaInstantiationSupply D) :
    ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G :=
  S.imageSupply

/-- **R-6c-body-114 — the assembly's `quotientRaw` field** (the existing `quotientForestOf`). -/
noncomputable def ResolvedForwardSigmaInstantiationSupply.quotientRawField
    (S : ResolvedForwardSigmaInstantiationSupply D) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    ResolvedAdmissibleSubgraph (((S.imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((S.imageSupply G).selectedOuterOf q).1)) :=
  (S.fullQuotient G).quotientForestOf q

/-- **R-6c-body-114 — the assembly's `quotient_mem` field.** -/
theorem ResolvedForwardSigmaInstantiationSupply.quotient_memField
    (S : ResolvedForwardSigmaInstantiationSupply D) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    S.quotientRawField G q ∈ D.carrier (((S.imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((S.imageSupply G).selectedOuterOf q).1)) :=
  S.quotient_mem G q

end GaugeGeometry.QFT.Combinatorial
