import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardMapCoherence
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftPrimitiveFactorComplete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromotedFactorSource
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocNonemptyLeavesIntegration
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorTransport

/-!
# R-6c-body-129 — concrete summand bundle: the summand agreement fed entirely from base supplies

Hundred-and-twenty-ninth genuine-body step, the wiring capstone: with body-128's `rfl` forward-map coherence in
hand, EVERY summand-agreement leaf is fed from base supplies.  `ResolvedConcreteSummandBundleSupply D` bundles the
forward coherence, the measure leaf, the survivor/remnant transports, and the fielded quotient data; its
`.toSummandBundle` streams the already-proved factor / disjointness lemmas into body-128's `.toSummandBundle`, so
the whole summand-agreement PRODUCT side stands on `Forward + Measure + Survivor + Remnant + [quotient union +
quot_eq]` alone.

## What is streamed (PROVED, all defeq against the concrete image supply)

Since `(Forward.imageSupply G).leftSelection = resolvedConcreteLeftSelectionSupply` and `.promotedOf =
(resolvedPromotedOfSupply _).promotedOf` DEFINITIONALLY, the left-side lemmas land on the bundle's fields with no
rewriting:

* `left_primitive_factor` ← `left_primitive_factor_concrete` (body-119, unconditional);
* `promoted_factor` ← `promoted_factor_of_hPD` with `Measure.promotedHPD` (body-122 + body-124);
* `hLdisj` ← `Measure.leftHDisj` (body-116/124).

The right-side factors are the transport supplies' fields, and slot in by body-128's graph alignment:

* `right_primitive_factor` ← `Survivor.toRightPrimitiveSurvivalTransportSupply.right_primitive_factor` (body-121/125);
* `remnant_factor` ← `Remnant.remnant_factor` (body-126).

## What is still fielded (the quotient side)

The quotient forest `B`, its `rightSurvivor ⊔ remnant` decomposition (`hcross` / `union_eq` / `hRdisj`, body-115)
and the contract-twice generator identity (`quot_eq`, body-111 with the bodies-27–49 geometry) are exposed as
supply fields — they carry the genuine de-contraction / contract-twice content that ties the codomain quotient to
the survivor/remnant forests, and their concrete providers (the full-quotient union instantiation and the
contract-twice geometry supply) are separate obligations.  Together with `Forward.selectedOuter_mem` (the
parametric-carrier closure) these are exactly the residual "quotient side" leaves.

## Consequence

The summand-agreement side is now a single supply built from base data.  `.summand_agree` gives, per split choice,
`resolvedSplitChoiceTerm q = leftTerm(selectedOuterOf q) ⊗ (leftTerm B ⊗ rightTerm B)`.  The remaining coassoc
content is purely the index/cover BIJECTION (backward map / `maps_to` / inverse laws), the quotient providers
(`quotient_mem`, the union instantiation, the contract-twice geometry), and the base providers (`carrier_isProperForest`,
the measure leaf's own obligation, the survivor/remnant `Inj`/`Gen`, `selectedOuter_mem`).

Per the HALT: only wiring; the left factors / disjointness are streamed from the proved lemmas, the quotient side
is exposed as fields, and no backward map / inverse law is touched.

Landed:

* `ResolvedConcreteSummandBundleSupply D` — the base-supply bundle (forward coherence + measure + survivor +
  remnant + fielded quotient data);
* `.toSummandBundle` — the `ResolvedSummandFactorBundle` fed entirely from the bundle;
* `.summand_agree` — the summand agreement per split choice, from base supplies.

Toolkit body (like body-127/128), one bundling supply.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-129 — the concrete summand bundle supply.**  The base-supply bundle: the forward-map coherence
(body-128), the measure leaf, the survivor (body-125) and remnant (body-126) transports, and the fielded quotient
data (the codomain forest with its survivor ⊔ remnant split and the contract-twice `quot_eq`). -/
structure ResolvedConcreteSummandBundleSupply (D : ResolvedCoproductProperForestData) where
  /-- The forward-map coherence (`rfl` graph alignment, body-128). -/
  Forward : ResolvedForwardMapCoherenceSupply D
  /-- The measure leaf (`cd_nonempty` → `hPD` / `hLP`, body-124). -/
  Measure : ResolvedMeasureLeafSupply D
  /-- The right-survivor transport supply (body-125). -/
  Survivor : ResolvedRightSurvivorTransportSupply D
  /-- The remnant transport supply (body-126). -/
  Remnant : ResolvedRemnantTransportSupply D
  /-- The codomain quotient forest index over the contract graph. -/
  quotientForest : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply (((Forward.imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((Forward.imageSupply G).selectedOuterOf q).1))).ForestIdx
  /-- Survivor/remnant cross-disjointness (body-115). -/
  hcross : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ∀ γ ∈ (Survivor.survivor.rightSurvivorForest q).elements,
    ∀ δ ∈ (Remnant.remnant.remnantForest q).elements, γ ≠ δ → γ.Disjoint δ
  /-- The quotient forest is the survivor ⊔ remnant union (body-115). -/
  union_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (quotientForest q).1
      = (Survivor.survivor.rightSurvivorForest q).union (Remnant.remnant.remnantForest q) (hcross q)
  /-- Survivor/remnant `Finset`-disjointness (body-115). -/
  hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Disjoint (Survivor.survivor.rightSurvivorForest q).elements
      (Remnant.remnant.remnantForest q).elements
  /-- The contract-twice quotient generator identity (`quot_eq`, body-111 + bodies-27–49 geometry). -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply G).rightTerm q.1
      = (D.supply (((Forward.imageSupply G).selectedOuterOf q).1.contractWithStars
          (D.starOf G ((Forward.imageSupply G).selectedOuterOf q).1))).rightTerm (quotientForest q)

/-- **R-6c-body-129 — the summand factor bundle from base supplies.**  Streams the proved left factors /
disjointness (body-119/122/124, defeq against the concrete image supply) and the transport supplies' right
factors (body-121/125/126) into body-128's `.toSummandBundle`. -/
noncomputable def ResolvedConcreteSummandBundleSupply.toSummandBundle
    (S : ResolvedConcreteSummandBundleSupply D) : ResolvedSummandFactorBundle D :=
  S.Forward.toSummandBundle S.Survivor.toRightPrimitiveSurvivalTransportSupply S.Remnant
    (fun {G} q => S.quotientForest q)
    (fun {G} q => S.hcross q)
    (fun {G} q => S.union_eq q)
    (fun {G} q => S.hRdisj q)
    (fun {G} q => left_primitive_factor_concrete q)
    (fun {G} q => promoted_factor_of_hPD q (S.Measure.promotedHPD q))
    (fun {G} q => S.Measure.leftHDisj q)
    (fun {G} q => S.quot_eq q)

/-- **R-6c-body-129 — the summand agreement from base supplies.**  For every split choice, the resolved
split-choice term is `leftTerm(selectedOuterOf q) ⊗ (leftTerm B ⊗ rightTerm B)` — the whole summand-agreement side
standing on `Forward + Measure + Survivor + Remnant + [quotient union + quot_eq]`. -/
theorem ResolvedConcreteSummandBundleSupply.summand_agree (S : ResolvedConcreteSummandBundleSupply D)
    (q : ForestBlockDomType D G) :
    D.resolvedSplitChoiceTerm (q : ResolvedCoassocSplitChoice D G)
      = (D.supply G).leftTerm (S.toSummandBundle.selected.selectedOuterOf q) ⊗ₜ[ℚ]
          ((D.supply ((S.toSummandBundle.selected.selectedOuterOf q).1.contractWithStars
              (D.starOf G (S.toSummandBundle.selected.selectedOuterOf q).1))).leftTerm
                (S.toSummandBundle.quotientForest q)
            ⊗ₜ[ℚ] (D.supply ((S.toSummandBundle.selected.selectedOuterOf q).1.contractWithStars
              (D.starOf G (S.toSummandBundle.selected.selectedOuterOf q).1))).rightTerm
                (S.toSummandBundle.quotientForest q)) :=
  S.toSummandBundle.summand_agree q

end GaugeGeometry.QFT.Combinatorial
