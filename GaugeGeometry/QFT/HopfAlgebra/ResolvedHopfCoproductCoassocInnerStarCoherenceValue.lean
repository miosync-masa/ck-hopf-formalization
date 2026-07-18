import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerRawCarrierClosure
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocInnerStarCoherence

/-!
# R-6c-body-379 — bank-3b: inner-star coherence lowered to the raw value layer (PROVED)

Three-hundred-and-seventy-ninth genuine-body step — the star model datum, stated on the RAW value core alone.  Body-349's
`ResolvedInnerStarCoherenceSupply` routes through `M.innerIdx` (a post-carrier-lift `ForestIdx`), but the coherence
MATHEMATICS mentions only the raw `Core.innerRaw` — so it belongs to bank-3b (value), separate from the carrier lift
(bank-4a).

* `ResolvedInnerStarCoherenceValueSupply Core` — the raw datum `innerStar_agrees_raw` (over `Core.innerRaw`, no `innerIdx`);
* `ResolvedMultiStarDecontractionValueCoreSupply.toInnerStarCoherenceSupply` — value core + carrier closure + raw
  coherence ⟶ body-349's supply, closed by `rfl` (`toValueCore_parent` / `toValueCore_innerRaw` are `rfl`, so
  `(M.innerIdx z δ).1 = Core.innerRaw z δ` definitionally).

**Star-allocation audit (verdict).**  `D.starOf`'s only structural law is `star_mapPerm` — SAME-graph permutation
equivariance, NOT cross-graph / component-identity ambient-independence.  The coherence compares stars across TWO
ambients (`(Core.parent z δ).tRFG` vs `G`) and TWO forests (`Core.innerRaw` vs `z.1.1`), which `star_mapPerm` cannot
bridge.  Verdict (2): `innerStar_agrees_raw` is an HONEST model datum — the concrete canonical star allocator must be
built component-identity-based for it to hold; it is NOT provable from the abstract `star_mapPerm`.

Landed axiom-clean: `ResolvedInnerStarCoherenceValueSupply`, `toInnerStarCoherenceSupply`.

Per the HALT: only the raw coherence interface + converter + the allocation verdict are done; `innerRaw_mem` is NOT used
to prove coherence; the raw occurrence inversion, the parent/remnant section, and the carrier lift stay for the rest of
bank-3b.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
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

/-- **R-6c-body-379 — the raw inner-star coherence datum** over a value core.  The parent/inner star map equals the
original star map on each touched outer component — stated on `Core.innerRaw` (no `ForestIdx`). -/
structure ResolvedInnerStarCoherenceValueSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D) where
  /-- The parent/inner star map equals the original star map on each touched outer component (raw). -/
  innerStar_agrees_raw : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x : ResolvedFeynmanSubgraph (z.1.1.contractWithStars (D.starOf G z.1.1)) // x ∈ forestDomain z})
    (A : {x : ResolvedFeynmanSubgraph G // x ∈ touchedOuterComponents z δ.1}),
    D.starOf (Core.parent z δ).toResolvedFeynmanGraph (Core.innerRaw z δ)
        (toInner z δ.1 (Core.legLift z δ) (Core.hE z) (Core.hL z) A)
      = D.starOf G z.1.1 A.1

/-- **R-6c-body-379 — raw coherence ⟶ body-349's supply** (over the carrier-lifted `M`), by `rfl`. -/
def ResolvedMultiStarDecontractionValueCoreSupply.toInnerStarCoherenceSupply
    (Core : ResolvedMultiStarDecontractionValueCoreSupply D)
    (Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core)
    (StarRaw : ResolvedInnerStarCoherenceValueSupply Core) :
    ResolvedInnerStarCoherenceSupply (Core.toDecontractionSupply Closure) where
  innerStar_agrees := StarRaw.innerStar_agrees_raw

end GaugeGeometry.QFT.Combinatorial
