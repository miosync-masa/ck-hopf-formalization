import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestTagPartition

/-!
# R-6c-body-349 — inner-star coherence audit: the re-contract section's hidden star address (scout + datum)

Three-hundred-and-forty-ninth genuine-body step — the star-config-board scout for the remnant re-contract
section (body-348's residual).  Opening the panel BEFORE the door: the re-contract section carries a second,
easily-missed address — a **star allocation coherence** between two DIFFERENT star maps.

## The two star maps

`M.parent z δ = localizedParentWithTouchedLegs z δ.1 (M.legLift z δ) (M.hE z) (M.hL z)` is built with the
ORIGINAL star map `D.starOf G z.1.1` (TouchedLegLiftDatum.lean:100-106).  But
`contractedSourceGraph o = o.B.1.contractWithStars (D.starOf o.γ.1.tRFG o.B.1)` (RemnantScout) uses the
star map hardcoded on the PARENT graph and the inner forest:

```text
D.starOf (M.parent z δ).toResolvedFeynmanGraph  (M.innerIdx z δ).1   -- the re-contract star map
```

applied through `toInner` (`(M.innerIdx z δ).1 = innerRaw = image toInner`, ToInner/InnerRawM3).  That these
two star maps AGREE on each touched component does NOT follow from `starOf_fresh` / `starOf_injective`, nor from
`star_mapPerm` (Supply.lean:141 — same-graph perm-equivariance only, `starOf (G.mapPerm σ) (A.mapPerm σ) …`, no
cross-graph iso-invariance).  It is a genuine coherence gap.

## The two-layer split for the re-contract section (verdict)

1. **`recontract_innerRaw_with_touchedStars`** — the EXPLICIT-star section, star map spelled out:

   ```text
   (M.innerIdx z δ).1.contractWithStars (fun B => D.starOf G z.1.1 (source of B)) = touchedLocalComponent z δ.1
   ```

   This is MECHANICAL — provable from the M1/M3 primitives (`toInner` data = `A`'s data; `innerRaw_elements`
   image bijection, bodies 327/328; `quotientEdgePreimage_map` for edges; `ResolvedTouchedLegLiftDatum.map_eq`
   for the external legs).  It is NOT yet stated, but it is a theorem, not a datum.

2. **`innerStar_agrees`** — the star coherence, isolated below as `ResolvedInnerStarCoherenceSupply`:

   ```text
   D.starOf (M.parent z δ).tRFG (M.innerIdx z δ).1 (toInner … A) = D.starOf G z.1.1 A.1
   ```

   VERDICT: this is NOT derivable from the available star facts (`star_mapPerm` / `starOf_fresh` /
   `starOf_injective`); it is a genuine **star allocation coherence DATUM** — the same caliber as `parentCD` /
   `legLift` / `starOf_fresh`, discharged by the canonical carrier in Front-3, NOT free from naturality of a
   name.

So the remnant round-trip `HEq (remnantComponent recovered o) δ.1` (body-350's precursor) composes:
`occurrence_inner_elements` (body-343, `o.B = innerIdx z δ`) + `innerStar_agrees` (this datum) +
`recontract_innerRaw_with_touchedStars` (mechanical) ⟹ `contractedSourceGraph o = δ` at the data level, then
`reembedAsSubgraph` ⟹ the HEq.

Per the HALT: this scout opens the star board and isolates the coherence datum; the explicit-star section is
PROVABLE (next body), the residual is EXACTLY `innerStar_agrees` (a canonical-carrier gate).  Skipping it would
let culprit D (`ForestIdx` transport) return under the alias "star-incoherence."  No new geometry is proved
here; no forward quotient / global forward round-trip; the six bridge gates do NOT fabricate the coherence.  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-349 — the inner-star coherence datum.**  The re-contract star map (`D.starOf` hardcoded on the
parent graph and the inner forest) agrees on each touched component with the ORIGINAL star map (`D.starOf G
z.1.1`).  NOT derivable from `star_mapPerm` / `starOf_fresh` / `starOf_injective` — a canonical-carrier gate. -/
structure ResolvedInnerStarCoherenceSupply (M : ResolvedMultiStarDecontractionSupply D) where
  /-- The parent/inner star map equals the original star map on each touched outer component. -/
  innerStar_agrees : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ.1}),
    D.starOf (M.parent z δ).toResolvedFeynmanGraph (M.innerIdx z δ).1
        (toInner z δ.1 (M.legLift z δ) (M.hE z) (M.hL z) A)
      = D.starOf G z.1.1 A.1

end GaugeGeometry.QFT.Combinatorial
