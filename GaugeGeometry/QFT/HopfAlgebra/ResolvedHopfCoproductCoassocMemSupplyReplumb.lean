import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestNonemptyLeaf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredPreimageValueMem

/-!
# R-6c-body-313 — membership re-plumbing: `Data` (body-283) assembled from the L2 raw-forward root (PROVED)

Three-hundred-and-thirteenth genuine-body step — the membership-layer re-wiring promised by the body-309 verdict B
re-stratification.  It defines the single combined L2 root `ResolvedRawForwardValueSupply` (`Tags` + the two
classifier-free forward identities), and INHABITS body-283's `ResolvedRecoveredPreimageValueMemSupply` from it plus the
carrier-proper provider `P` (body-228) — with all three membership leaves discharged by the proved lemmas
(`mixed_ne_pR` body-310, `mixed_ne_pL` body-311, `forest_nonempty` body-312).  The three leaves that were honest FIELDS
of `Data` are now derived; the membership residual disappears at the interface.

## The re-wiring

```text
ResolvedRawForwardValueSupply  =  Tags + forward_outer_value + forward_quotient_value      (single shared Tags)
  → toRawForwardOuterValueSupply    (Tags + forward_outer)          → mixed_ne_pR   (body-310, unconditional)
  → toRawForwardQuotientValueSupply (Tags + forward_outer/quotient) → mixed_ne_pL   (body-311, unconditional)
  → forest_nonempty  (body-312, Region := Tags.Closure.Assembly.Region)
  ⟹ ResolvedRecoveredPreimageValueMemSupply  (body-283)
```

The two mixed leaves are UNCONDITIONAL (body-310/311 prove `≠ p_R` / `≠ p_L` with no classifier hypothesis), so the
`Data` fields' `¬ resolvedIsForestImage` premises are received and discarded (`fun z _ => …`).  `Tags` is threaded ONCE
(the converters set `Tags := R.Tags`), so no cross-converter `Tags`-equality bridge is needed —
`(R.toRawForwardOuterValueSupply).Tags` is `R.Tags` definitionally.

## Guards (as instructed)

* `Tags` appears once; the converters copy it, no bridge.
* Body-283's three leaves are DERIVED, not re-fielded.
* `forest_value_eq` and the full round-trip `R` are NOT mixed in (body-314+).
* `Tags.Closure`'s `recovered_raw_mem` remains the Group-3 CARRIER-MODEL root — NOT claimed proved here.
* floor-297/298 untouched.

Per the HALT: only the `Data` (body-283) inhabitant is built; the round-trip leaf supply (body-285) `forest_value_eq`
and the carrier closure are later fronts; no facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-313 — the combined L2 raw-forward root.**  A single shared `Tags` with BOTH classifier-free forward
identities; the source for the membership leaves (no `Data`, no mixed membership). -/
structure ResolvedRawForwardValueSupply (F : ResolvedSelectedOuterFilteredMemSupply D)
    (V : ResolvedConcreteSummandValueSupply D) where
  /-- The raw region-tag supply (body-282). -/
  Tags : ResolvedRegionTagValueSupply F V
  /-- The reconstruction's re-promoted outer is the original outer (body-289). -/
  forward_outer_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf (Tags.recoveredPreimageValue z) = z.1.1
  /-- The reconstruction's quotient forest is the original `B` (body-290, heterogeneous). -/
  forward_quotient_value : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (V.quotientForestRaw (Tags.recoveredPreimageValue z)) z.2

namespace ResolvedRawForwardValueSupply

variable {F : ResolvedSelectedOuterFilteredMemSupply D} {V : ResolvedConcreteSummandValueSupply D}

/-- **R-6c-body-313 — converter to the outer L2 root (body-310).** -/
def toRawForwardOuterValueSupply (R : ResolvedRawForwardValueSupply F V) :
    ResolvedRawForwardOuterValueSupply F V where
  Tags := R.Tags
  forward_outer_value := R.forward_outer_value

/-- **R-6c-body-313 — converter to the quotient L2 root (body-311).** -/
def toRawForwardQuotientValueSupply (R : ResolvedRawForwardValueSupply F V) :
    ResolvedRawForwardQuotientValueSupply F V where
  Tags := R.Tags
  forward_outer_value := R.forward_outer_value
  forward_quotient_value := R.forward_quotient_value

/-- **R-6c-body-313 — body-283's membership supply, assembled from the L2 root + the carrier-proper provider.**  All
three membership leaves are the proved lemmas (bodies 310/311/312); the classifier hypotheses of the mixed leaves are
received and discarded (both are unconditional). -/
noncomputable def toRecoveredPreimageValueMemSupply
    (R : ResolvedRawForwardValueSupply F V) (P : ResolvedCarrierProperProvider D) :
    ResolvedRecoveredPreimageValueMemSupply F V where
  Tags := R.Tags
  forest_nonempty := fun {_G} _z hz =>
    forestRecovered_nonempty_of_resolvedIsForestImage R.Tags.Closure.Assembly.Region hz
  mixed_ne_pR := fun {_G} z _ =>
    ResolvedRawForwardOuterValueSupply.mixed_ne_pR_of_forward_outer P R.toRawForwardOuterValueSupply z
  mixed_ne_pL := fun {_G} z _ =>
    ResolvedRawForwardQuotientValueSupply.mixed_ne_pL_of_forward_quotient P R.toRawForwardQuotientValueSupply z

end ResolvedRawForwardValueSupply

end GaugeGeometry.QFT.Combinatorial
