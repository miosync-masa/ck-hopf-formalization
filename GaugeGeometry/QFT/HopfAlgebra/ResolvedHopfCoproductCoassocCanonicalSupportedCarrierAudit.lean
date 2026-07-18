import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAmbientSupportScopeRepair
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-body-401 — canonical supported-carrier root audit (verdict anchor + support-source feasibility)

Four-hundred-and-first genuine-body step — the FIRST root of the canonical-discharge front (body-400's residual is now a
different battle).  Source correction to body-395's "carrier EXISTING" verdict:

* `W.toCarrierProperProvider : ResolvedCarrierProperProvider W.toData` IS constructed — **given a `W`**
  (`CanonicalCarrierProper.lean:88`, `carrier_isProperForest := (W.index G).mem_proper`).
* But `W : ResolvedCanonicalCarrierProperSupply` itself has **NO inhabitant yet** — `index` / `starOf` / `hCD` /
  `carrier_mapPerm` / `star_mapPerm` are heavy per-`G` fields (`CanonicalCarrierProper.lean:59-75`).  So `W` is an
  existing INTERFACE, not an existing inhabitant.
* `(W.index G).mem_proper` guarantees ONLY the properness of a carrier member `A` — it does NOT yield ambient-`G`
  endpoint support: a `G` with a carrier-external malformed edge is not contradicted by any member's properness.  Ambient
  support CANNOT be fabricated from `mem_proper`.
* `canonicalPayload_edges_supported` / `_legs_supported` (`ResolvedActualSigmaCover.lean:1718/1725`) are stated for the
  specific payload graph `(canonical…payload g).G` PER `g : HopfGen`; they do NOT fill the generic `W`'s `∀ G`.

## The six audit findings

1. **`canonicalCover (g : HopfGen)`** (`ResolvedPayloadModel.lean:429`) is PER `HopfGen` — a `ResolvedProperForest
   FiniteCover (ofFlatGraph (repG g).toFeynmanGraph)`.  The generic `W.index : (G) → ProperForestFiniteIndex G` must LIFT
   this per-`g` cover to a per-`G` index, empty off the payload graphs.
2. **Emptying off-payload** needs a definable/decidable identification of "`G` is a canonical unique-id lift `ofFlat
   GraphWithUniqueIds Gf`" (or `G = payload g`).  This is the crux for `index G := ∅` otherwise — OPEN (body-402).
3. **`carrier_mapPerm`** must hold for the lifted per-`G` index (the proper-forest filter is `mapPerm`-natural; the
   payload identification must be `mapPerm`-closed) — to verify (body-402).
4. **`starOf` total**: only CONSTRAINED on carrier members (`hCD` / `star_mapPerm`); off-carrier it may be any default, so
   totality is free.
5. **`hCD` / `star_mapPerm`**: `hCD` (member contraction CD) + `star_mapPerm` come from the existing canonical star
   geometry on the payload graphs — to wire (body-402), not fabricate.
6. **`A ∈ W.toData.carrier G → AmbientEdgesSupported G ∧ AmbientLegsSupported G`**: derivable IFF `index G` is non-empty
   ONLY on `ofFlatGraphWithUniqueIds Gf` with `Gf.WellFormed`.  **The honest support source is `Gf.WellFormed`, NOT
   `mem_proper`** — banked below as `ambientSupported_of_ofFlatGraphWithUniqueIds` (PROVED feasibility).

Per the HALT: this is the root audit + the support-source feasibility ONLY; ambient support is NOT fabricated from
`mem_proper`; `canonicalPayload_*_supported` is NOT transported to a type-differing arbitrary `G`; `W` is recorded as an
existing INTERFACE (not an inhabitant); nothing is plugged into `CoreBuild` until the emptying feasibility (2/3) is
confirmed.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-401 — the honest ambient-support source for the canonical carrier.**  A unique-id lift of a WELL-FORMED
flat graph is both edge- and leg-supported — so body-397's `AmbientEdgesSupported` / `AmbientLegsSupported` follow from
`Gf.WellFormed` (NOT from any carrier member's `mem_proper`).  This is the feasibility root for a supported canonical
carrier: emptying `index G` off unique-id lifts of well-formed graphs makes the body-397 gate dischargeable. -/
theorem ambientSupported_of_ofFlatGraphWithUniqueIds {Gf : FeynmanGraph} (hGf : Gf.WellFormed) :
    AmbientEdgesSupported (ofFlatGraphWithUniqueIds Gf) ∧
      AmbientLegsSupported (ofFlatGraphWithUniqueIds Gf) :=
  ⟨ofFlatGraphWithUniqueIds_edges_supported hGf, ofFlatGraphWithUniqueIds_legs_supported hGf⟩

end GaugeGeometry.QFT.Combinatorial
