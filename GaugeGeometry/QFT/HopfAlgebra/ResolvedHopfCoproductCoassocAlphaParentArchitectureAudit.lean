import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaSaturatedConstructionRoot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalizedParentCD
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocToInner
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawM3
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawAggregate

/-!
# R-6c-body-548 — the `Parent` aggregate ARCHITECTURE AUDIT (bounded decomposition, PROVED)

Five-hundred-and-forty-eighth genuine-body step — a BOUNDED DECOMPOSITION AUDIT of the ONE remaining honest physics
field, `Parent = ResolvedCanonicalLegSaturatedDecontractionCDSupply` (body-541).  This body DECOMPOSES the `parentCD`
aggregate into its minimal residuals and FORMALLY BANKS the assets that already discharge every side but the two genuine
frontiers.  It builds NO `Parent` inhabitant, proves NEITHER frontier, and introduces NO new structure / typeclass /
groupoid / fiber-product / quotient API.  ★Scope is the whole point.★

## The `parentCD` field (body-541)

`Parent.parentCD` is, at each `(z, δ)`, a single value:
`(localizedParentWithTouchedLegs z δ.1 … ).forget.IsConnectedDivergent`, where `.forget : FeynmanSubgraph G.forget`
(`ResolvedSubGraph.lean:56`).  By `isConnectedDivergent_def` (`SubGraph.lean:1358/1361`, `Iff.rfl`) this is the 3-way
`IsConnected ∧ IsOnePI ∧ IsDivergent`, and `IsOnePI.isConnected` (`SubGraph.lean:686`) makes the first conjunct
REDUNDANT.

## Step 1 — the logical minimal decomposition (the ONLY substantive content)

`canonicalLegSaturatedParentForget z δ` abbreviates the `W″` parent's `.forget` subgraph.  Then:

* `canonicalLegSaturated_parentCD_of_onePI_divergent` : `OnePI → Divergent → IsConnectedDivergent`
  (Connected DERIVED via `IsOnePI.isConnected`, never a field).
* `canonicalLegSaturated_parentOnePI_of_cd` / `_parentDivergent_of_cd` : the reverse `.2.1` / `.2.2` projections.
* `canonicalLegSaturated_parentCD_iff_onePI_divergent` : the Prop-level equivalence
  `IsConnectedDivergent ↔ IsOnePI ∧ IsDivergent` (the Connected conjunct is redundant).

Net: `parentCD ↔ parentOnePI ∧ parentDivergent`; the **Connected residual is ELIMINATED**.

## Step 2 — `parentCD` consumer audit (classification only)

| consumer | what it reads | note |
| --- | --- | --- |
| (a) `forestRecoveredMulti` / `forestRegion` component CD (`MultiStarDecontraction.lean:94`, `M.parentCD z δ`) | the WHOLE aggregate `IsConnectedDivergent` | flows into `ResolvedAdmissibleSubgraph.ofElements`'s CD obligation |
| (b) `innerRaw_mem` parent-graph carrier membership (the `.forget.toFeynmanGraph_isConnectedDivergent` bridge, body-443/538) | the WHOLE aggregate | membership gate for the inner forest |

Direct `.1` (Connected) consumers are parent-vertex reconstruction — future-replaceable by `IsOnePI.isConnected`
(Step 1).  `.2.1` / `.2.2` have NO independent direct consumer: `parentCD` flows as an aggregate, so the decomposition is
a re-key of that aggregate, not a change of any call site.

## Step 3 — insertion premises already available (cited theorems; ONE trivial re-export banked)

The quotient/inserted CD premises are ALREADY theorems (cite; do NOT reprove):

* quotient component `δ` is CD from `δ.2 : δ.1 ∈ forestDomain z` (a `z.2.1` component) fed through
  `touchedLocalComponent_isConnectedDivergent` (`LocalizedParentCD.lean:67`).
* inserted (retyped) components are CD via `toInner_isConnectedDivergent` (`ToInner.lean:70`).
* the insertion trace: `promote_toInner` (`ToInner.lean:64`) + `toInner_injective` (`ToInner.lean:84`) +
  `promote_innerRaw_elements` (`InnerRawM3.lean:75`).

One trivial `:=`-term re-export is banked here (`canonicalLegSaturated_insertedComponent_isConnectedDivergent`),
specialising `toInner_isConnectedDivergent` to the canonical `W″` datum/ambient; everything else is a citation.

## Step 4 — reconstruction geometry audit (recontract field projections)

`localizedParentWithTouchedLegs`'s fields (`TouchedLegLiftDatum.lean:94`):
`externalLegs = datum.legs`; `internalEdges = touchedOuterForest.internalEdges + quotientEdgePreimage …`;
`vertices = G.vertices.filter (touched ∨ quotient-edge-preimage ∨ datum-leg)`.  Read alongside
`promote_innerRaw_elements` (`InnerRawM3.lean:75`) and `innerRaw_vertices_eq_touchedOuterForest`
(`InnerRawAggregate.lean:90`), these record that the parent is the recontraction of `innerRaw` + the datum/star gluing
interface (`touchedInnerStarTotal`, `InnerRawAggregate.lean:75`, is the gluing witness — NOT a hardcoded canonical star).

BANKED as PLAIN `rfl` field-value theorems (statement = the defeq field value):
`recontract548_parent_externalLegs`, `recontract548_parent_internalEdges`, `recontract548_parent_vertices`.
All three closed by `rfl` (convenience bank, NOT load-bearing).

## Step 5 — frontier verdict

```text
reconstruction geometry      EXISTING / DERIVED   (Step 4 + localizedParentWithTouchedLegs fields)
inserted occurrence trace    EXISTING             (toInner / promote_toInner / promote_innerRaw_elements)
equivalence invariance       EXISTING             (mapPerm / IsIso ambient-invariance)
Connected                    DERIVED FROM OnePI   (Step 1)
parentOnePI                  OPEN COMBINATORIAL TOPOLOGY frontier
parentDivergent              OPEN PHYSICS CLOSURE frontier
```

True remaining decomposition:
`Parent = topological insertion preservation (parentOnePI) + divergence insertion closure (parentDivergent)`.
`parentDivergent` is the quotient-level shadow of the divergence insertion closure; it is NAMED, NOT built into a
`CompatibleInsertionDivergenceClosure` primitive/typeclass.  The two bare-`Prop` frontier defs
`CanonicalLegSaturatedParentOnePIFrontier` / `CanonicalLegSaturatedParentDivergentFrontier` NAME the frontiers — they do
NOT inhabit them (no fields, no instances, no obligations).

## Scoreboard (`Parent` architecture audit)

```text
Parent aggregate           DECOMPOSED   (parentCD ↔ parentOnePI ∧ parentDivergent)
Connected residual         ELIMINATED   (derived from OnePI, Step 1)
reconstruction / trace     BANKED       (Step 3 cite + Step 4 rfl projections)
parentOnePI                NAMED COMBINATORIAL FRONTIER
parentDivergent            NAMED PHYSICS FRONTIER
```

Sharpened four-move architecture: geometry + traceability + invariance EXISTING, Connected FREE, remaining =
OnePI-insertion + Divergence-insertion (two frontiers).

Per the HALT/guards: NO `Parent` inhabitant is built; NEITHER `parentOnePI` nor `parentDivergent` is proved; NO new
typeclass/structure with obligations, NO groupoid / homotopy fiber product / quotient API, NO Weinberg-degree formula;
`Parent` is NOT reverse-engineered from forward round-trip / coassoc; NO `sourceStar = targetStar` strict socket; the
existing `ResolvedCanonicalLegSaturatedDecontractionCDSupply` (541) stays valid and UNMODIFIED; the bare-`Prop` frontier
defs carry no field/instance/obligation.  No facade, no `sorry`/`admit`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-! ## Step 1 — the logical minimal decomposition `parentCD ↔ parentOnePI ∧ parentDivergent`. -/

/-- **R-6c-body-548 — the canonical `W″` parent's `.forget` subgraph.**  The graph on which `Parent.parentCD` states
`IsConnectedDivergent`; here `.forget : FeynmanSubgraph G.forget`. -/
noncomputable abbrev canonicalLegSaturatedParentForget {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    FeynmanSubgraph G.forget :=
  (localizedParentWithTouchedLegs z δ.1
    (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
    (liveAmbient_edges_supported ambientSupportOfW'' z)
    (liveAmbient_legs_supported ambientSupportOfW'' z)).forget

/-- **R-6c-body-548 — `parentCD` from `parentOnePI` + `parentDivergent`.**  The Connected conjunct is DERIVED from
`IsOnePI.isConnected`; it is never a field. -/
theorem canonicalLegSaturated_parentCD_of_onePI_divergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (hOnePI : (canonicalLegSaturatedParentForget z δ).IsOnePI)
    (hDiv : (canonicalLegSaturatedParentForget z δ).IsDivergent) :
    (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent :=
  ⟨hOnePI.isConnected, hOnePI, hDiv⟩

/-- **R-6c-body-548 — the `parentOnePI` projection** of `parentCD` (`.2.1`). -/
theorem canonicalLegSaturated_parentOnePI_of_cd {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (h : (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent) :
    (canonicalLegSaturatedParentForget z δ).IsOnePI :=
  h.2.1

/-- **R-6c-body-548 — the `parentDivergent` projection** of `parentCD` (`.2.2`). -/
theorem canonicalLegSaturated_parentDivergent_of_cd {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (h : (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent) :
    (canonicalLegSaturatedParentForget z δ).IsDivergent :=
  h.2.2

/-- **R-6c-body-548 ∎ — the minimal decomposition.**  `parentCD ↔ parentOnePI ∧ parentDivergent`; the Connected conjunct
is redundant (`IsOnePI.isConnected`). -/
theorem canonicalLegSaturated_parentCD_iff_onePI_divergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}) :
    (canonicalLegSaturatedParentForget z δ).IsConnectedDivergent ↔
      (canonicalLegSaturatedParentForget z δ).IsOnePI ∧
        (canonicalLegSaturatedParentForget z δ).IsDivergent := by
  constructor
  · rintro ⟨_, hPI, hDiv⟩; exact ⟨hPI, hDiv⟩
  · rintro ⟨hPI, hDiv⟩; exact ⟨hPI.isConnected, hPI, hDiv⟩

/-! ## Step 3 — the inserted-component CD, a ONE-LINE re-export of the existing `toInner_isConnectedDivergent`. -/

/-- **R-6c-body-548 — inserted-component CD (re-export).**  A retyped touched component of the canonical `W″` parent is
connected-divergent — a trivial specialisation of `toInner_isConnectedDivergent` (`ToInner.lean:70`) to the canonical
datum + ambient.  Cited, not reproved. -/
theorem canonicalLegSaturated_insertedComponent_isConnectedDivergent {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z})
    (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ.1}) :
    (toInner z δ.1
      (touchedLegLiftDatum_of_complete z δ.1 (canonicalLegSaturated_touchedLegComplete z δ))
      (liveAmbient_edges_supported ambientSupportOfW'' z)
      (liveAmbient_legs_supported ambientSupportOfW'' z) A).forget.IsConnectedDivergent :=
  toInner_isConnectedDivergent z δ.1 _ _ _ A

/-! ## Step 4 — the recontract field projections (PLAIN `rfl`, convenience bank). -/

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-548 — recontract external-leg projection** (`rfl`).  The parent's external legs ARE the datum's leg
preimage. -/
theorem recontract548_parent_externalLegs {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (localizedParentWithTouchedLegs z δ datum hE hL).externalLegs = datum.legs :=
  rfl

/-- **R-6c-body-548 — recontract internal-edge projection** (`rfl`).  The parent's internal edges ARE the touched outer
forest's internal edges plus the quotient-edge preimage — the recontraction of `innerRaw` + star interface. -/
theorem recontract548_parent_internalEdges {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (localizedParentWithTouchedLegs z δ datum hE hL).internalEdges
      = (touchedOuterForest z δ).internalEdges
        + quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1) (touchedLocalComponent z δ) :=
  rfl

/-- **R-6c-body-548 — recontract vertex projection** (`rfl`).  The parent's vertices ARE the touched / quotient-edge
preimage / datum-leg filter of `G.vertices`. -/
theorem recontract548_parent_vertices {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)))
    (datum : ResolvedTouchedLegLiftDatum z δ)
    (hE : ∀ e ∈ G.internalEdges, e.source ∈ G.vertices ∧ e.target ∈ G.vertices)
    (hL : ∀ ℓ ∈ G.externalLegs, ℓ.attachedTo ∈ G.vertices) :
    (localizedParentWithTouchedLegs z δ datum hE hL).vertices
      = G.vertices.filter (fun v =>
          v ∈ (touchedOuterForest z δ).vertices ∨
          (∃ e ∈ quotientEdgePreimage (touchedOuterForest z δ) (D.starOf G z.1.1)
              (touchedLocalComponent z δ), e.source = v ∨ e.target = v) ∨
          (∃ ℓ ∈ datum.legs, ℓ.attachedTo = v)) :=
  rfl

/-! ## Step 5 — bare-`Prop` frontier names (they NAME the frontiers, they do NOT inhabit them). -/

/-- **R-6c-body-548 — the OPEN combinatorial-topology frontier.**  A bare `Prop` NAMING "every canonical `W″` parent's
`.forget` is 1PI"; NO field / instance / obligation — this NAMES the frontier, it does not inhabit it. -/
def CanonicalLegSaturatedParentOnePIFrontier : Prop :=
  ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (canonicalLegSaturatedParentForget z δ).IsOnePI

/-- **R-6c-body-548 — the OPEN physics-closure frontier.**  A bare `Prop` NAMING "every canonical `W″` parent's `.forget`
is divergent" — the quotient-level shadow of the divergence insertion closure; NO field / instance / obligation. -/
def CanonicalLegSaturatedParentDivergentFrontier : Prop :=
  ∀ {G : ResolvedFeynmanGraph}
    (z : ForestBlockCodType canonicalLegSaturatedCarrierProperSupply.toData G)
    (δ : {x : ResolvedFeynmanSubgraph
        (z.1.1.contractWithStars (canonicalLegSaturatedCarrierProperSupply.toData.starOf G z.1.1)) //
          x ∈ forestDomain z}),
    (canonicalLegSaturatedParentForget z δ).IsDivergent

end GaugeGeometry.QFT.Combinatorial
