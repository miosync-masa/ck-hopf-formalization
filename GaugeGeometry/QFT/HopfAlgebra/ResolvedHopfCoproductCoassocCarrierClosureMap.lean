import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRawRecoveredOuterScout
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterIsProper

/-!
# R-6c-body-268 — carrier-closure map: bodies 262–267 (docs anchor)

Two-hundred-and-sixty-eighth genuine-body step, a documentation anchor (no new geometry).  It fixes the carrier-closure
verdict — the counterpart of the migration closure (body-260): all five `IsProperForest` conjuncts are proved for the
constructed forests, but properness does not imply carrier membership, so carrier closure is an honest parametric-model
obligation.  Imports body-267/264 so the map stays type-checked.  Reader-facing narrative:
`CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 262–267"; proof-dependency map: `CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies
262–267".

## The arc (262–267)

```text
262  complementEdges monotonicity infra (PROVED).
263  complement positivity for X / Y by GLOBAL monotonicity (PROVED, no deep leaf).
264  IsProperForest ASSEMBLED — all five conjuncts complete (X 5-tuple filtered; Y elements-equality transfer).
265  generic recovered_eq / ofForgetForest section is an HONEST LEAF (forget not globally injective).
266  CORRECTION — body-265's "unionOuter.2 free membership" bypass is CIRCULAR (unionOuter z = ⟨raw, recovered_outer_mem z⟩);
       non-circular content = only the raw outer's IsProperForest. SUPERSEDES body-265's "off the critical path".
267  independent rawRecoveredOuter root (region maps + disjointness via .union, no carrier tag) + carrier verdict.
```

## The headline (precise)

```text
All five IsProperForest conjuncts are proved for the relevant constructed forests, but properness does not imply
membership in the supplied finite resolved carrier.

Carrier closure is therefore an honest parametric-model obligation, not a remaining coassociativity proof-shape gap.

rawRecoveredOuter is the canonical circularity-prevention root; unionOuter.2 is an INPUT to a carrier-closure proof,
never an OUTPUT of one (body-265's bypass superseded by body-266).
```

## Carrier-closure route table

```text
Route                                          Verdict
all resolved proper forests via Finset.univ    IMPOSSIBLE — no global Fintype (ResolvedAdmissibleSubgraph G)
                                               (ResolvedCoproduct.lean:164, by design; no DecidablePred IsProperForest)
payload carrier extension                      possible concrete-model work, NOT free (owes generic-z raw IsProperForest
                                               + carrier_mapPerm / hCD equivariance)
forget-image section (A = ofForgetForest       OBSTRUCTED — forget not injective; promotedOf keeps δ's ids, not the
  A.forget)                                    constant-id re-lift
parametric carrier-closure supply              the canonical current interface (selectedOuter_mem filtered body-245;
                                               recovered_outer_mem / cross-disjoint supplied)
```

## Note

`IsProperForest` (all five conjuncts) is complete; the migration residual is none (bodies 248–259).  What remains is
the **parametric carrier-closure supply** (filtered selected-outer closure + raw recovered-outer closure +
cross-disjointnesses) — an honest model obligation, not a proof-shape gap — plus the original geometry (branch specs,
eight sector directions, forward compatibility, non-region base).  The next front is the top-level parametric
carrier-closure supply consolidating these, not the concrete carrier-enumeration construction (a separate phase:
enumeration + permutation closure + `hCD`).  No declarations beyond this docstring anchor; the import keeps the map
honest against the source.  No facade, no flat term, no `forgetHopf`.
-/
