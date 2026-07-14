import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocParametricCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockBijection
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitFilteredValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValueCanonical

/-!
# R-6c-body-270 — the filtered bijection side + `coassoc_gen_of_parametric_model` (PROVED)

Two-hundred-and-seventieth genuine-body step — the top-level connection.  It inhabits the raid-boss target
`ResolvedForestBlockBijectionSupply` (body-97) **directly from the filtered / value chain**, with no `.ofLegacy` and no
total `ResolvedForwardMapCoherenceSupply.selectedOuter_mem`, and chains it to `coassoc_gen`.  This closes the R-6c
parametric layer to a single honest conditional statement: *from the model's closure assumptions + the original geometry
leaves, `Δᵣ`-coassociativity on generators*.

## The one missing forward leaf (Forward-free)

Every `ResolvedForestBlockBijectionSupply` field is suppliable from the migrated chain (bodies 252/253/259) **except**
the forward codomain membership `toFun_mem`.  Unfolded, `fwdMapFilteredValue F V q ∈ forestBlockCodFinset G` reduces
(via `Finset.mem_sigma` + `Finset.mem_attach` on the outer tag) to
`(fwdMapFilteredValue F V q).2 ∈ (D.supply (…contractWithStars…)).forestCarrier` — the forward quotient membership over
the **value root** (`selectedOuterRawOf`), NOT over the total `Forward`.  This is the sole remaining forward leaf; it is
`Forward`-free (needs no `selectedOuter_mem`), so it lives as its own supply `ResolvedForwardQuotientMemValueSupply`.

## The filtered bijection side

`ResolvedFilteredBijectionSideSupply` bundles the filtered pieces and inhabits `ResolvedForestBlockBijectionSupply`:

| bijection field | source (all Forward-free, no `.ofLegacy`) |
|---|---|
| `toFun`     | `fwdMapFilteredValue F V ⟨q, hq⟩` (body-252) |
| `invFun`    | `cover.witnessSplit` (body-253) |
| `toFun_mem` | `forwardMem.quotient_mem` (the new leaf) + `Finset.mem_attach` |
| `invFun_mem`| `cover.witnessSplit_mem` (body-253) |
| `left_inv`  | `cover.backward_witness` (body-253) |
| `right_inv` | `cover.forward_witness` (body-253) |
| `summand_agree` | `summand_agree_value_of_value F V` (body-259) — **derived**, not assumed |
| `carrier_isProperForest` / `rep` / `repCD` / `rep_gen` | base model leaves |

The summand agreement is *derived* from `F + V` (body-259), so it is not a field of the side supply.

## The conditional model theorem

`coassoc_gen_of_parametric_model` takes the parametric carrier-closure supply (body-269) and the original geometry as
**separate** arguments, consumes `Closure.toSelectedOuterFilteredMemSupply` (converter 1) as the filtered selected-outer
root `F`, and produces `coassoc_gen`.  No `.ofLegacy`, no total `Forward` on this path.

## Audit — the 5 systems and converter wiring

* forward maps-to (`toFun`/`toFun_mem`): `fwdMapFilteredValue` + the new `forwardMem` leaf — Forward-free;
* inverse maps-to (`invFun`/`invFun_mem`): `cover` (body-253), which the region construction (bodies 156/157/173/184)
  builds from `Closure.toRegionPartitionSupply` / `.toRecoveredOuterCarrierSupply` (converters 2 / 3);
* round-trips (`left_inv`/`right_inv`): `cover.backward_witness` / `.forward_witness` (body-253);
* term agreement (`summand_agree`): `summand_agree_value_of_value` (body-259) — derived;
* region construction: consolidated in the closure (body-269); its two region converters feed the concrete `cover`.

Converter 1 (`toSelectedOuterFilteredMemSupply`) is consumed **directly** on the canonical path here.  Converters 2 / 3
feed the *concrete construction* of `cover` from the region chain — that concrete cover is the **single remaining
migration boundary** (the region → backward-map assembly, bodies 156/157/173/184, still phrased against the total
forward map).  As a *theorem*, `coassoc_gen_of_parametric_model` is already fully `Forward`-free / `.ofLegacy`-free: the
`cover` it consumes is the migrated value-root supply (body-253), taken as a hypothesis.

Per the HALT: the filtered bijection side + the conditional model theorem are defined/proved; the single forward leaf is
isolated; no total `selectedOuter_mem`, no `unionOuter.2` assumption, no `recovered_eq`, no facade, no flat term, no
`forgetHopf`.
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

/-- **R-6c-body-270 — the forward quotient membership over the value root** (the sole remaining forward leaf).
`Forward`-free: the quotient forest of `fwdMapFilteredValue F V q` lies in the quotient graph's carrier, phrased over
`selectedOuterRawOf` (body-252), never over the total `Forward`. -/
structure ResolvedForwardQuotientMemValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- `fwdMapFilteredValue`'s quotient forest is a carrier forest of the quotient graph. -/
  quotient_mem : ∀ {G : ResolvedFeynmanGraph} (q : FilteredForestBlockDom D G),
    (fwdMapFilteredValue F V q).2
      ∈ (D.supply ((fwdMapFilteredValue F V q).1.1.contractWithStars
          (D.starOf G (fwdMapFilteredValue F V q).1.1))).forestCarrier

/-- **R-6c-body-270 — the filtered bijection side.**  All `ResolvedForestBlockBijectionSupply` data from the migrated
value-root chain (bodies 252/253) + the new forward-membership leaf + base model leaves; the summand agreement is
derived from `F + V` (body-259), so it is not a field here. -/
structure ResolvedFilteredBijectionSideSupply (D : ResolvedCoproductProperForestData) where
  /-- The filtered selected-outer carrier closure (body-245). -/
  F : ResolvedSelectedOuterFilteredMemSupply D
  /-- The value-only summand bundle (body-252). -/
  V : ResolvedConcreteSummandValueSupply D
  /-- The value-root witnessSplit cover — the inverse map + its round-trips (body-253). -/
  cover : ResolvedWitnessSplitFilteredValueCoverSupply F V
  /-- The forward quotient membership over the value root (the sole remaining forward leaf). -/
  forwardMem : ResolvedForwardQuotientMemValueSupply F V
  /-- Every carrier forest is a proper forest (body-96; base model leaf). -/
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  /-- A representative graph for each generator (base model leaf). -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

namespace ResolvedFilteredBijectionSideSupply

/-- **R-6c-body-270 — inhabiting the raid-boss `ResolvedForestBlockBijectionSupply`** from the filtered side, with no
`.ofLegacy` and no total `Forward`. -/
noncomputable def toForestBlockBijectionSupply (B : ResolvedFilteredBijectionSideSupply D) :
    ResolvedForestBlockBijectionSupply D where
  toFun := fun _ q hq => fwdMapFilteredValue B.F B.V ⟨q, hq⟩
  invFun := fun _ r _ => B.cover.witnessSplit r
  toFun_mem := fun G q hq => by
    simp only [forestBlockCodFinset, Finset.mem_sigma]
    exact ⟨Finset.mem_attach _ _, B.forwardMem.quotient_mem ⟨q, hq⟩⟩
  invFun_mem := fun _ r hr => B.cover.witnessSplit_mem r hr
  left_inv := fun _ q hq => B.cover.backward_witness ⟨q, hq⟩
  right_inv := fun _ r hr => B.cover.forward_witness r hr
  summand_agree := fun _ q hq => (summand_agree_value_of_value B.F B.V).summand_agree_value ⟨q, hq⟩
  carrier_isProperForest := B.carrier_isProperForest
  rep := B.rep
  repCD := B.repCD
  rep_gen := B.rep_gen

/-- **R-6c-body-270 — `coassoc_gen` from the filtered bijection side.** -/
theorem coassoc_gen (B : ResolvedFilteredBijectionSideSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  B.toForestBlockBijectionSupply.coassoc_gen x

end ResolvedFilteredBijectionSideSupply

/-- **R-6c-body-270 — coassociativity from the parametric model** (the top-level conditional statement).  From the
parametric carrier-closure supply (body-269) — via its filtered selected-outer converter — plus the original geometry
leaves (value bundle, witnessSplit cover, forward membership, properness, representative lift), native
`Δᵣ`-coassociativity holds on every generator.  No `.ofLegacy`, no total `Forward`; the summand agreement is derived. -/
theorem coassoc_gen_of_parametric_model {S : ResolvedConcreteSummandBundleSupply D}
    (Closure : ResolvedParametricCarrierClosureSupply D S)
    (V : ResolvedConcreteSummandValueSupply D)
    (cover : ResolvedWitnessSplitFilteredValueCoverSupply Closure.toSelectedOuterFilteredMemSupply V)
    (forwardMem : ResolvedForwardQuotientMemValueSupply Closure.toSelectedOuterFilteredMemSupply V)
    (carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
      A ∈ D.carrier G → A.IsProperForest)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  (ResolvedFilteredBijectionSideSupply.mk Closure.toSelectedOuterFilteredMemSupply V cover forwardMem
    carrier_isProperForest rep repCD rep_gen).coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
