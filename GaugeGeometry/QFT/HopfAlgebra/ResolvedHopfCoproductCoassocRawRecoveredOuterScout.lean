import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterIsProper

/-!
# R-6c-body-267 — raw recovered-outer root + carrier-closure verdict: honest supplied leaf (2026-07-13)

Two-hundred-and-sixty-seventh genuine-body step — the independent raw recovered-outer root (the last circularity pin)
plus the audit of the two options for closing carrier membership.  **Verdict: (3) HONEST SUPPLIED LEAF** — option 1a is
impossible (no `Fintype`), option 1b converts membership into further obligations without eliminating them, option 2's
section fails on the promoted region.  Carrier membership stays a supplied canonical-model field.

## The independent raw root (circularity pin)

`rawRecoveredOuter` is defined from the three region maps + their pairwise disjointnesses (body-158) via
`ResolvedAdmissibleSubgraph.union` alone — **no `unionOuter`, no carrier tag, no `recovered_outer_mem`** in its
definition or argument types.  (`unionOuter z = ⟨rawRecoveredOuter …, recovered_outer_mem z⟩`, so the body-159 field is
exactly this value plus the `∈ D.carrier G` tag; only that tag is circular.)  This separates the value from the
membership — the same move that beat the total `selectedOuter` (body-252).

## DECISIVE — no `Fintype (ResolvedAdmissibleSubgraph G)` (option 1a impossible)

`ResolvedCoproduct.lean:164` states by design: "There is no `Fintype (ResolvedFeynmanSubgraph G)` (no global resolved
enumeration)".  There is no `Fintype (ResolvedAdmissibleSubgraph G)`, no `Fintype (ResolvedFeynmanSubgraph G)`, and no
`DecidablePred IsProperForest` anywhere (grep empty).  So `carrier G := Finset.univ.filter IsProperForest`
**cannot even be formed** — there is no `Finset.univ`.  **Option 1a (filter univ of all proper forests) is decisively
BLOCKED.**  The carrier must remain a supplied payload `Finset` (`ResolvedCoproductProperForestData.carrier`,
`ResolvedHopfCoproductSupply.lean:130`).

## The four options, verdict

```text
1a  all-proper-filter carrier            RULED OUT — no Fintype (ResolvedAdmissibleSubgraph G).
1b  payload carrier containing the        NOT Fintype-blocked (forestBlockDom/CodFinset are finite), but NOT free:
    constructed forests                    still owes carrier_mapPerm / hCD for the enlarged carrier AND the
                                           GENERIC-z raw IsProperForest (body-266 covers only z = fwdMap S q, since
                                           recovered_region_partition is over the forward image; recovered_outer_mem
                                           is ∀ z). Converts membership into properness+equivariance, not a discharge.
2   shape-specific section                OBSTRUCTION: A = ofForgetForest A.forget holds for leftOf / carrier-member
    (A = ofForgetForest A.forget)          components (already constant-id lifts) but FAILS for promotedOf: promote
                                           (ResolvedSubgraphPromote.lean:46) keeps δ's original ids, not the constant-id
                                           re-lift; selectedOuterRawOf mixes both. forget is not globally injective.
3   honest supplied leaf                  CURRENT, CORRECT STATE: recovered_outer_mem (159) / selectedOuter_mem (128,
                                           now filtered) stay supplied fields, dischargeable only against a specific
                                           constructed canonical model — not by any generic mechanism.
```

## Assessment and plan

* **Carrier membership is a supplied canonical-model field (state 3).**  This is R-4-full's parametric-`D` premise:
  the carrier and its closure are supplied data; body-264/266's `IsProperForest` (5/5) is the *material* a concrete
  canonical instance uses to discharge membership, but generically it is a field.  The certificate route (body-232/233)
  is a *sufficient interface*, not a generic discharge; body-265's `.2` bypass was circular (body-266).
* **The productive residual for a concrete instance (1b)** is: the generic-`z` raw `IsProperForest` (extend body-266
  past the forward image) plus `carrier_mapPerm` / `hCD` equivariance for a carrier enlarged to contain the constructed
  images.  This is a real construction, remote from the parametric layer.
* **body-268**: the parametric coassoc layer is complete up to these supplied carrier-closure fields; the next genuine
  front is a docs refresh consolidating the `IsProperForest` completion + the carrier-closure verdict, then the
  concrete canonical-instance construction (1b) as the remaining reduction — or leaving membership as the honest
  supplied leaf, matching `selectedOuter_mem`'s filtered status.

Per the HALT: the raw root is defined (circularity pin); the carrier-closure verdict (honest supplied leaf, 1a
impossible) is recorded; no membership is discharged and no `recovered_eq` is attempted.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-267 — the independent raw recovered outer** (circularity pin).  The triple region union built from the
region maps + their pairwise disjointnesses via `ResolvedAdmissibleSubgraph.union` alone — no `unionOuter`, no carrier
tag, no `recovered_outer_mem`.  `unionOuter z` is exactly this value plus the (circular) membership tag. -/
noncomputable def rawRecoveredOuter (leftResidual rightRecovered forestRecovered : ResolvedAdmissibleSubgraph G)
    (hcross₁ : ∀ γ ∈ leftResidual.elements, ∀ δ ∈ rightRecovered.elements, γ ≠ δ → γ.Disjoint δ)
    (hcross₂ : ∀ γ ∈ (leftResidual.union rightRecovered hcross₁).elements,
      ∀ δ ∈ forestRecovered.elements, γ ≠ δ → γ.Disjoint δ) :
    ResolvedAdmissibleSubgraph G :=
  (leftResidual.union rightRecovered hcross₁).union forestRecovered hcross₂

end GaugeGeometry.QFT.Combinatorial
