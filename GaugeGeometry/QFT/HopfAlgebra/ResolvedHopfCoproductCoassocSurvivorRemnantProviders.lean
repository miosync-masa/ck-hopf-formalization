import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantTransport

/-!
# R-6c-body-148 — survivor / remnant provider bank: the four Inj/Gen leaves in one record

Hundred-and-forty-eighth genuine-body step, a base-side bank.  The survivor / remnant transport supplies
(body-125 `ResolvedRightSurvivorTransportSupply`, body-126 `ResolvedRemnantTransportSupply`) — each carrying the
component embedding plus its injectivity and generator equality — are bundled into one provider, so the four
`survivorInj` / `survivorGen` / `remnantInj` / `remnantGen` leaves flow from a single object.

## The four leaves (recap) and their dependencies

* `Survivor.survivorInj` — the right-survivor component embedding is injective (id-tracked; body-8, ultimately the
  parent/star kernel `ResolvedStarGlobalGapSupply` via `occurrence_inj`);
* `Survivor.survivorGen` — the survivor's generator term is the source component's (an `rfl`-level reembed fact,
  `rightSurvivorComponentOf_gen`, body-125);
* `Remnant.remnantInj` — the remnant component embedding is injective (id-tracked; leaf-9 via `occurrence_inj`,
  same kernel);
* `Remnant.remnantGen` — the remnant's generator term is the forest choice's right factor (the de-contraction
  class equality, `product_remnantGen_of_decontraction`, body-126).

So `survivorGen` is `rfl`-level, `remnantGen` is the de-contraction geometry, and the two injectivities are the
id-tracked component injectivity — all recognised leaves.  The provider does not reprove them; it banks them and
exposes the (shared) parent/star-kernel dependency of the two injectivities.

## The provider (bundle)

`ResolvedSurvivorRemnantProvider D` holds one `Survivor` and one `Remnant` transport supply; `.toSurvivor` /
`.toRemnant` re-export them, and they feed body-129's `ResolvedConcreteSummandBundleSupply` (its `Survivor` /
`Remnant` fields) — hence the right-primitive / remnant factor products (bodies 125/126) and, through the summand
bundle, the whole PRODUCT side.  So the survivor / remnant Inj/Gen needs no longer appear separately; they are one
provider.

Per the HALT: the parent/star kernel is not reproved; the two injectivities' dependence on it is named; this is
provider banking only.

Landed:

* `ResolvedSurvivorRemnantProvider D` — the survivor + remnant transport bundle;
* `.toSurvivor` / `.toRemnant` — the two transport supplies (→ body-129, the factor products).

Toolkit body (like body-137/140), one base provider.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-148 — the survivor / remnant provider.**  The right-survivor (body-125) and remnant (body-126)
transport supplies bundled — the four `survivorInj` / `survivorGen` / `remnantInj` / `remnantGen` leaves in one
record. -/
structure ResolvedSurvivorRemnantProvider (D : ResolvedCoproductProperForestData) where
  /-- The right-survivor transport supply (`survivorInj` + `survivorGen`, body-125). -/
  Survivor : ResolvedRightSurvivorTransportSupply D
  /-- The remnant transport supply (`remnantInj` + `remnantGen`, body-126). -/
  Remnant : ResolvedRemnantTransportSupply D

/-- **R-6c-body-148 — the right-survivor transport supply from the provider** (→ body-129, the right-primitive
factor product). -/
def ResolvedSurvivorRemnantProvider.toSurvivor (P : ResolvedSurvivorRemnantProvider D) :
    ResolvedRightSurvivorTransportSupply D :=
  P.Survivor

/-- **R-6c-body-148 — the remnant transport supply from the provider** (→ body-129, the remnant factor product). -/
def ResolvedSurvivorRemnantProvider.toRemnant (P : ResolvedSurvivorRemnantProvider D) :
    ResolvedRemnantTransportSupply D :=
  P.Remnant

end GaugeGeometry.QFT.Combinatorial
