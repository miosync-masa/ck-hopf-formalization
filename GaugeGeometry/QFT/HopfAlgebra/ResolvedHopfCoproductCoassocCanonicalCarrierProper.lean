import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider

/-!
# R-6c-body-228 — canonical carrier proper: `carrier_isProperForest` PROVED from a proper-forest finite index

Two-hundred-and-twenty-eighth genuine-body step — the first real *grounding* of a floor leaf into a canonical
model instance.  Body-227 found the canonical carrier is a repackaging for three of the four floor leaves, but
`carrier_isProperForest` (body-137) is a **genuine free win**: if the carrier is built from a proper-forest finite
index (each member *known* proper), the leaf falls out of the index's own `mem_proper`.  This body banks that win.

## The construction

`ResolvedCanonicalCarrierProperSupply` is a wrapper that carries the abstract carrier's *heavy* ingredients as
honest fields — the per-graph proper-forest **index** (`ResolvedProperForestFiniteIndex G`, which already bundles
`carrier` with `mem_proper : ∀ A ∈ carrier, A.IsProperForest`, `ResolvedCoproduct.lean:172`), the star assignment,
the contraction CD, and the two `mapPerm` naturalities — and assembles them into a `ResolvedCoproductProperForestData`
whose `carrier G := (index G).carrier`.  Because the carrier *is* a proper-forest index carrier, the body-137 leaf

```
carrier_isProperForest : ∀ G A, A ∈ D.carrier G → A.IsProperForest
```

is discharged by the **one-liner** `fun G A hA => (index G).mem_proper A hA` — no longer a raw field but a theorem
about this `D`.  So `ResolvedCarrierProperProvider W.toData` is *constructed*, not fielded.

## What this settles (and what it does not)

* **Settled** — `carrier_isProperForest` is no longer a floor leaf for a canonical proper-forest-indexed carrier: it
  is proved from `ResolvedProperForestFiniteIndex.mem_proper`.  This is the concrete instance of the body-227 verdict
  "only 137 is a free win", now realized in Lean: `.toCarrierProperProvider` builds the body-137 provider outright.
* **Still fielded (heavy, per body-227)** — `index` (the actual proper-forest enumeration, e.g. the `ofFlatForest` /
  `canonicalCover` payload — `ResolvedPayloadModel.lean:429`), `starOf`, `hCD`, and the two `mapPerm` naturalities.
  These are the genuine data of a canonical model; body-228 does not construct them (per the HALT), it names them.
* **Untouched** — `selectedOuter_mem` (128) and `recovered_outer_mem` (159) remain construction-specific obligations
  (body-227): the canonical carrier converts them into properness/disjointness of *constructed* regions, not into a
  free `mem_proper` projection.  They are not addressed here.

Per the HALT: the canonical `index` / `starOf` / `hCD` are not built (they are a whole payload model, remote from this
file); only `carrier_isProperForest` is grounded, and it is genuinely **proved**.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

set_option linter.unusedSectionVars false

/-- **R-6c-body-228 — a canonical proper-forest-indexed carrier supply.**  Bundles the heavy carrier ingredients
(the per-graph proper-forest `index`, the star assignment, the contraction CD, and the two `mapPerm` naturalities)
so that the assembled `ResolvedCoproductProperForestData` has a carrier that is *by construction* a proper-forest
index carrier — making `carrier_isProperForest` a theorem rather than a field. -/
structure ResolvedCanonicalCarrierProperSupply where
  /-- The per-graph proper-forest index (carrier + `mem_proper`); the canonical model fills this via
  `ofFlatForest` / `canonicalCover`. -/
  index : (G : ResolvedFeynmanGraph) → ResolvedProperForestFiniteIndex G
  /-- The star assignment per forest (heavy data; fielded). -/
  starOf : (G : ResolvedFeynmanGraph) → ResolvedAdmissibleSubgraph G →
    (ResolvedFeynmanSubgraph G → VertexId)
  /-- The contraction is connected divergent for every index member (fielded). -/
  hCD : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G), A ∈ (index G).carrier →
    ((A.contractWithStars (starOf G A)).forget.toClass.IsConnectedDivergent)
  /-- The index carrier transports by relabeling (fielded). -/
  carrier_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    (index (G.mapPerm σ)).carrier = ((index G).carrier).image (fun A => A.mapPerm σ)
  /-- The star assignment is `mapPerm`-natural (fielded). -/
  star_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) (γ : ResolvedFeynmanSubgraph G), γ ∈ A.elements →
    starOf (G.mapPerm σ) (A.mapPerm σ) (γ.mapPerm σ) = σ (starOf G A γ)

/-- **R-6c-body-228 — the assembled coproduct forest data** whose carrier is the proper-forest index carrier. -/
def ResolvedCanonicalCarrierProperSupply.toData (W : ResolvedCanonicalCarrierProperSupply) :
    ResolvedCoproductProperForestData where
  carrier := fun G => (W.index G).carrier
  starOf := W.starOf
  hCD := W.hCD
  carrier_mapPerm := W.carrier_mapPerm
  star_mapPerm := W.star_mapPerm

/-- **R-6c-body-228 — the body-137 carrier-proper provider, PROVED.**  `carrier_isProperForest` is discharged from
the index's `mem_proper`; no longer a raw field.  This is the canonical grounding of floor leaf 137. -/
def ResolvedCanonicalCarrierProperSupply.toCarrierProperProvider
    (W : ResolvedCanonicalCarrierProperSupply) :
    ResolvedCarrierProperProvider W.toData where
  carrier_isProperForest := fun G A hA => (W.index G).mem_proper A hA

end GaugeGeometry.QFT.Combinatorial
