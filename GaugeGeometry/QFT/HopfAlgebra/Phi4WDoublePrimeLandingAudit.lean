import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentDischarged

/-!
# QFT-R1-body-575 — W″ landing-interface scope audit (docstring-only)

Before extending the φ⁴ bridge toward the CK / W″ coassociativity terminus, this body **measures the far
bank**: it fixes, by `@`-signature X-ray, the lowest class-free / explicit-supply boundary at which the φ⁴
family could land.  No new geometry, no new declaration, no W″ theorem applied — this file has **zero
declarations**; the verdict lives in this docstring and is anchored by the machine-checked signatures below.

## Step 1 — signature X-ray (verified by `@ #check`)

Every interface in the W″ landing chain — the carrier, the construction/round-trip supplies, and both the
pre- and post-Parent-discharge coassoc theorems — carries the **same seven** old blanket binders:

```text
[∀ G, DivergenceMeasure G]
[∀ G, IsPermInvariantDivergence G]
[∀ G, IsIsoInvariantDivergence G]
[∀ G, Fintype (FeynmanSubgraph G)]
[IsAmbientInvariantDivergence]
[IsDivergencePreservedByContract]
[IsDivergencePreservedByAdmissibleForestContract]
```

and the Parent-discharge terminus adds one more at the top:

```text
[IsDivergenceReflectedByAdmissibleForestContract]     -- consumed once for parentDivergent
```

Confirmed on: `canonicalLegSaturatedCarrierProperSupply` (body-533, → `ResolvedCanonicalCarrierProperSupply`),
`ResolvedCanonicalLegSaturatedAlphaConstructionSupply`, `ResolvedRecoveredPreimageAlphaValueRoundTripLeafSupply`,
`coassoc_gen_of_canonicalLegSaturated_alpha` (7 binders), and
`coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged` (8 binders).  Beyond the binders, the
terminus takes three **explicit** supplies — `ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData`
(the power-counting leaf), `∀ H, ResolvedConnectedDivergentPositiveInternalEdgesSupply H` (non-degeneracy),
and the `rep* : ResolvedHopfGen → ResolvedFeynmanGraph` representation interface — all keyed to the
**resolved** carrier `canonicalLegSaturatedCarrierProperSupply`, not to a flat φ⁴ carrier.

### Binder classification

```text
[∀ G, DivergenceMeasure G]                              explicit supply ownership (phi4DivergenceMeasureFamily IS a term of this type)
[∀ G, Fintype (FeynmanSubgraph G)]                      Fintype infrastructure
[∀ G, IsPermInvariantDivergence G]                      section-variable leakage → actually consumed at the carrier's rename well-definedness
[∀ G, IsIsoInvariantDivergence G]                       section-variable leakage → consumed at the class-quotient well-definedness
[IsAmbientInvariantDivergence]                          actually consumed (subgraph → intrinsic-graph divergence lift)
[IsDivergencePreservedByContract]                       actually consumed (single-contraction right factor)
[IsDivergencePreservedByAdmissibleForestContract]       actually consumed (forest right factor divergence)
[IsDivergenceReflectedByAdmissibleForestContract]       actually consumed once (parentDivergent, body-556)
Measure / E / rep*                                       explicit supply ownership, keyed to the RESOLVED carrier
```

**There is no class-free interface in the chain** — even body-533's carrier already carries all seven.

## Step 2 — first consumer of each old blanket class

The first consumption point is **the W″ carrier itself** (body-533,
`canonicalLegSaturatedCarrierProperSupply`): it already carries all seven, because the saturated carrier is
built on `canonicalUniqueSupportedCarrierProperSupply` (body-405+) whose rigidification/rename/class
machinery consumes Perm/Iso/Ambient invariance and both contraction-preservation classes.  The generic
coassoc entry (body-481, `coassoc_gen_of_canonicalMultiStar_alpha`) then threads them upward unchanged.  So
the classes are **not** a thin top-level wrapper that could be peeled at the terminus — they are load-bearing
from the carrier up.  `Fintype` first appears with the finite coproduct sum and is pure infrastructure.

## Step 3 — the local-instance route is formally rejected (body-564 no-go, reconfirmed)

Supplying a **local** `DivergenceMeasure G := phi4DivergenceMeasureFamily G` instance does **not** inhabit
`IsPermInvariantDivergence` (nor `IsIso`/`IsAmbient`).  Its field

```text
degree_mapPerm : ∀ π [DivergenceMeasure (G.mapPerm π)] γ, degree (γ.mapPerm π) = degree γ
```

**re-quantifies the target measure** as an independent instance; a local instance only sets a *default* for
synthesis, it does not weaken the field's universal quantifier.  Body-564 proved the family cannot satisfy
this shape; bodies 570/573 confirmed that consuming the polluted forest wrappers would require exactly this
forbidden inhabitation.  The route is closed: the classes must be **replaced**, not **inhabited**.

## Step 4 — landing verdict

Classifying each layer of the terminus:

```text
REUSE (explicit supplies suffice)
    [∀ G, Fintype (FeynmanSubgraph G)]                   -- φ⁴ already carries the blanket (bodies 566/571/574)
    [∀ G, DivergenceMeasure G]                           -- phi4DivergenceMeasureFamily supplies it as a term

FAMILY RE-KEY (old blanket ownership re-issued to the φ⁴ family)
    [∀ G, IsPermInvariantDivergence G]                   -- → body-565 PermInvariantDivergenceMeasureFamily phi4… (INHABITED)
    [∀ G, IsIsoInvariantDivergence G]                    -- → an Iso analogue of body-565's coherent-family interface (not yet built)
    [IsAmbientInvariantDivergence]                        -- refuted on toFeynmanGraph (562); holds on the boundary-completed graph (567) → boundary-aware re-key
    [IsDivergencePreservedByContract]                     -- over-strong single-contraction (559/560); φ⁴ bypasses via the quotient-divergence leaf → not required
    [IsDivergencePreservedByAdmissibleForestContract]     -- φ⁴ COMPUTES it from boundary preservation (573) → CONSTRUCTED, not assumed

GENUINE RESOLVED WORK (boundary-ID completion / traceability)
    [IsDivergenceReflectedByAdmissibleForestContract]     -- reverse / insertion law; needs a boundary-aware reverse power-counting realization
    Measure / E / rep* (resolved-carrier leaves)          -- bridge φ⁴'s FLAT Phi4HopfGen/Phi4HopfH to the RESOLVED W″ carrier (the resolved boundary-ID layer body-567 flagged as separate)
```

**Minimal family-explicit landing interface (the choice):** since even the carrier carries the seven, the
landing cannot reuse an existing interface — it must be a *fresh family-indexed landing root* (body-576+)
that:
  1. takes `phi4DivergenceMeasureFamily` + the blanket `Fintype` (REUSE);
  2. takes body-565's `PermInvariantDivergenceMeasureFamily phi4…` and an Iso analogue in place of the Perm/Iso
     blankets (FAMILY RE-KEY);
  3. drops `IsAmbientInvariantDivergence` / `IsDivergencePreservedByContract` (φ⁴ works boundary-completed /
     via the quotient leaf) and *constructs* `IsDivergencePreservedByAdmissibleForestContract` from body-573;
  4. leaves exactly two genuine obligations to later bodies — the **reflection law** and the **flat→resolved
     carrier bridge** (Measure/E/rep*).

So the far-bank pier sits at a family-indexed re-key of the carrier/construction root; the resolved boundary
completion is built only for the fields that interface actually demands.

## Ledger

```text
W″ landing chain binders          X-RAYED (7 blanket + reflection, load-bearing from the carrier up)
class-free interface              NONE EXISTS in the chain
local-instance route              REJECTED (body-564 no-go reconfirmed)
DivergenceMeasure / Fintype       REUSE
Perm / Iso / Ambient / Contract   FAMILY RE-KEY
ForestContract preservation       CONSTRUCTED (from boundary preservation, 573)
reflection + resolved bridge      GENUINE RESOLVED WORK (named open frontier)
minimal landing interface         CHOSEN: fresh family-indexed carrier/construction re-key (576+)
```

Per the HALT: zero new `class`/`structure`/`instance`; no local φ⁴ instance is created; no target-measure
equality is assumed; no W″ theorem is applied; no resolved boundary completion is built; body-574 and the CK
final theorem are not edited; no coassociativity realization is claimed.  This body only *measures the pier*.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Intentionally no declarations: this module is the W″ landing-interface scope-audit record.
-- The classification lives in the module docstring above; body-575 adds no obligations.

end GaugeGeometry.QFT.Combinatorial
