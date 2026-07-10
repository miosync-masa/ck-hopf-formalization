import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalMembershipCertificate
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership

/-!
# R-6c-body-233 — canonical membership adapters: `selectedOuter_mem` (128) / `recovered_outer_mem` (159) from certificates

Two-hundred-and-thirty-third genuine-body step — the wiring that connects body-232's proved `cert_mem` adapter to the
two actual coassoc closure leaves.  With a per-graph canonical cover and a `carrier_eq` identifying `D.carrier G` with
the cover's carrier, each leaf is produced from a single membership certificate: no longer a raw supply hypothesis /
field, but `cert_mem` applied to the constructed forest.

## The wiring

`ResolvedCanonicalCarrierWiring D` bundles the shared ingredients — a canonical cover per graph and the identification
of the abstract carrier with it:

```lean
structure ResolvedCanonicalCarrierWiring (D) where
  cover      : ∀ G, ResolvedProperForestFiniteCover G
  carrier_eq : ∀ G, D.carrier G = (cover G).index.carrier
```

`carrier_eq` is the canonical-`D` identification (the body-228 grounding, where `D.carrier G = (index G).carrier`); it
is kept as a field because it is exactly the "canonical `D`" commitment, not a generic fact.

## The two adapters (proved)

* `selectedOuterMem` — from `∀ s, certificate (cover G) (selectedOuterRawOf s)` produces the exact hypothesis
  `∀ s, selectedOuterRawOf s ∈ D.carrier G` that `resolvedConcreteSelectedOuterImageSupply` (body-128) consumes:
  `rw [carrier_eq]; exact (cert s).mem`.
* `recoveredOuterSupply` — from `∀ z, certificate (cover G) (region union)` builds the body-159
  `ResolvedRecoveredOuterCarrierSupply` outright, its `recovered_outer_mem` field discharged the same way.

Both reduce to `cert_mem` (body-232) after the `carrier_eq` rewrite — the membership is *proved*, and the residual is
exactly the supplied certificates.

## What this settles

The two carrier-closure leaves are now **routed through certificates**: their residual is precisely `selectedOuter_cert`
/ `recoveredOuter_cert` (each a `ResolvedCanonicalMembershipCertificate`, i.e. `isProper` + `recovered_eq`, body-232)
plus the `carrier_eq` wiring.  All subsequent work on 128/159 is "fill the certificate fields" — the five
`IsProperForest` conjuncts (via `forget_union_elements`, body-231) and the section condition.

Per the HALT: no certificate field (`isProper` / `recovered_eq`) is proved, no `carrier_eq` is constructed (it is the
canonical-`D` commitment, fielded), and `D`'s full canonical construction is not entered — only the wiring from
certificates to the two leaves, which is proved.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-233 — the canonical carrier wiring.**  A per-graph canonical cover and the identification of the
abstract carrier `D.carrier G` with the cover's carrier (the canonical-`D` commitment). -/
structure ResolvedCanonicalCarrierWiring (D : ResolvedCoproductProperForestData) where
  /-- The canonical proper-forest cover per graph. -/
  cover : ∀ (G : ResolvedFeynmanGraph), ResolvedProperForestFiniteCover G
  /-- The abstract carrier is the cover's carrier (the canonical-`D` identification). -/
  carrier_eq : ∀ (G : ResolvedFeynmanGraph), D.carrier G = (cover G).index.carrier

/-- **R-6c-body-233 — `selectedOuter_mem` (body-128) from certificates.**  Given a membership certificate for every
`selectedOuterRawOf s`, the exact carrier-membership hypothesis that `resolvedConcreteSelectedOuterImageSupply`
consumes is proved by `cert_mem`. -/
theorem ResolvedCanonicalCarrierWiring.selectedOuterMem (W : ResolvedCanonicalCarrierWiring D)
    (G : ResolvedFeynmanGraph)
    (cert : ∀ s, ResolvedCanonicalMembershipCertificate (W.cover G)
      ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s)) :
    ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G := by
  intro s
  rw [W.carrier_eq G]
  exact (cert s).mem

/-- **R-6c-body-233 — body-159's `ResolvedRecoveredOuterCarrierSupply` from certificates.**  Given a membership
certificate for every recovered-outer region union, the body-159 carrier-closure supply is built, its
`recovered_outer_mem` discharged by `cert_mem`. -/
def ResolvedCanonicalCarrierWiring.recoveredOuterSupply (W : ResolvedCanonicalCarrierWiring D)
    (S : ResolvedConcreteSummandBundleSupply D)
    (leftResidual rightRecovered forestRecovered :
      ∀ {G : ResolvedFeynmanGraph}, ForestBlockCodType D G → ResolvedAdmissibleSubgraph G)
    (hcross_lr : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ (leftResidual z).elements, ∀ δ ∈ (rightRecovered z).elements, γ ≠ δ → γ.Disjoint δ)
    (hcross_lrf : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ∀ γ ∈ ((leftResidual z).union (rightRecovered z) (hcross_lr z)).elements,
      ∀ δ ∈ (forestRecovered z).elements, γ ≠ δ → γ.Disjoint δ)
    (cert : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
      ResolvedCanonicalMembershipCertificate (W.cover G)
        (((leftResidual z).union (rightRecovered z) (hcross_lr z)).union (forestRecovered z) (hcross_lrf z))) :
    ResolvedRecoveredOuterCarrierSupply D S leftResidual rightRecovered forestRecovered hcross_lr hcross_lrf where
  recovered_outer_mem := by
    intro G z
    rw [W.carrier_eq G]
    exact (cert z).mem

end GaugeGeometry.QFT.Combinatorial
