import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocAlphaParentDischarged

/-!
# R-6c-body-558 — CK physics-frontier semantic audit (docstring-only)

Five-hundred-and-fifty-eighth genuine-body step.  This is **not** a discharge — it FIXES THE MEANING of what remains after
the Parent discharge (bodies 548–556).  No new theorem / `class` / `structure` / `instance`; the final theorem
`coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged` is NOT edited.  The purpose is to record, without
cross-wiring, exactly which mathematical role each surviving assumption plays — so the frontier is a clean *realization*
question, not an unfinished coassociativity proof.

## Step 1 — the final theorem's assumptions, classified

`coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged` carries EIGHT instance binders.  ★Correction to the earlier
framing: they are **6 physics families + 1 finiteness infrastructure + 1 reflection law**, NOT "7 physics + reflection" —
`Fintype (FeynmanSubgraph G)` is combinatorial infrastructure, not physics.★

| Instance | Class | Content |
|---|---|---|
| `∀ G, DivergenceMeasure G` | **numerical realization** | the raw `degree` function; carries no law, just a valuation |
| `∀ G, IsPermInvariantDivergence G` | **rename invariance** | `degree` preserved under `G → G.mapPerm π` |
| `∀ G, IsIsoInvariantDivergence G` | **intra-ambient invariance** | `degree` preserved under Path-B subgraph iso |
| `IsAmbientInvariantDivergence` | **intrinsic invariance** | descent from ambient to the intrinsic self-graph |
| `IsDivergencePreservedByContract` | **forward closure** | contracting a single 1PI divergent subgraph preserves divergence |
| `IsDivergencePreservedByAdmissibleForestContract` | **forward forest closure** | forest-contracting a divergent ambient preserves it |
| `IsDivergenceReflectedByAdmissibleForestContract` | **reverse / insertion closure** | divergent remainder + inserted forest ⟹ source divergence |
| `∀ G, Fintype (FeynmanSubgraph G)` | **combinatorial infrastructure** | finite sums / finite carrier; NOT physics |

So the surviving *physics* content is six divergence families + the one reflection law; `Fintype` is bookkeeping.

## Step 2 — the explicit (non-instance) supplies

```text
Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData
    cd_nonempty            -- a connected-divergent component has a vertex
    contract_preserves_CD  -- the resolved-carrier contraction closure leaf

E : ∀ H, ResolvedConnectedDivergentPositiveInternalEdgesSupply H
    cd_positiveInternalEdges  -- a connected-divergent graph has a positive internal-edge count

rep : ResolvedHopfGen → ResolvedFeynmanGraph
repCD / rep_gen               -- the Hopf-generator representation interface
```

Verdict (ownership levels are DISTINCT — do not conflate):
- `Measure` / `E` are the power-counting **leaves** that make the concrete resolved carrier proper / non-degenerate.
- `rep*` is the **Hopf-generator representation** interface (which resolved graph realizes a generator).
- These are at a different ownership level from the global invariance / preservation typeclasses.  ★At this point NONE is
  judged alias/redundant — that is an OPEN audit item, not a claim.★

## Step 3 — the direction table (what each law does, by direction)

```text
presentation change:
  Perm / Iso / Ambient invariance              ↔ transport (no graph change of divergence status)
contraction:
  Contract / ForestContract preservation       → forward closure (collapse a divergent piece, stay divergent)
decontraction / insertion:
  ForestReflection                             → reverse closure (a divergent remainder + inserted forest reflects back)
carrier admissibility:
  Measure.cd_nonempty / E                      → non-degeneracy of the concrete carrier
  Measure.contract_preserves_CD               → resolved-carrier contraction closure
```

★`IsDivergenceReflectedByAdmissibleForestContract` is the **quotient-level shadow of compatible-insertion closure**★ — the
reverse of forest contraction, exactly the law body-556 consumes once to realize `parentDivergent`.  NO groupoid / operad
structure is built here — the direction table is a classification only.

## Step 4 — overlaps recorded as CANDIDATES only (all AUDIT OPEN — none proved here)

- Perm / Iso / Ambient invariance *look like* three cross-sections of one unified groupoid invariance — **candidate**, not
  a proved implication.
- single-contraction preservation and forest-contraction preservation **overlap** — candidate.
- `Measure.contract_preserves_CD` is a topology-carrying **resolved** leaf, plausibly stronger than the abstract forest
  preservation — candidate.
- the reflection law is plausibly **realizable from a Weinberg-type additive power-counting rule with boundary
  corrections** — candidate.
- `cd_nonempty` / `E` are plausibly **derivable in a concrete model from degree/residue constraints** — candidate.

Every one is **AUDIT OPEN**; this body proves none of them and asserts no implication/redundancy.

## Step 5 — the frontier split into two (three) theorems

```text
Formalization theorem
    native W″ Δᵣ-coassociativity modulo the CK divergence laws                 COMPLETE   (bodies …–556)
Concrete realization theorem
    a concrete Weinberg / boundary valuation INHABITS those laws               OPEN       (the next main theorem)
Structural abstraction theorem
    coherence + traceability + closure + descent as a boundary-interface
    groupoid / operadic architecture                                          FUTURE
```

The formalization campaign is closed.  What remains is a DIFFERENT main theorem — *a concrete QFT realizes this abstract
CK divergence architecture* — not more coassociativity plumbing.

## Ledger

```text
coassoc construction campaign       CLOSED
combinatorial infrastructure        SEPARATED  (Fintype ≠ physics)
physics invariance laws             CLASSIFIED (6 families)
forward / reverse closure           SEPARATED  (Contract/ForestContract vs ForestReflection)
concrete Weinberg realization       NAMED OPEN FRONTIER
new obligations                     ZERO
```

Per the HALT: no typeclass is merged; no instance inhabitant is built; the reflection law is NOT fabricated from
`Measure`; `Fintype` is NOT treated as physics; no implication / redundancy is asserted unproved; NO
unconditionalization campaign is started; the final theorem is NOT edited.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Intentionally no declarations: this module is the semantic-frontier audit record.
-- The classification lives in the module docstring above; body-558 adds no obligations.

end GaugeGeometry.QFT.Combinatorial
