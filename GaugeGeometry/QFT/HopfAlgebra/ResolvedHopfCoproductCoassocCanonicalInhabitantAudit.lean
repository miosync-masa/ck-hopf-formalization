import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGenValueGeometry

/-!
# R-6c-body-395 — canonical inhabitant source audit for the body-394 residual (verdict anchor)

Three-hundred-and-ninety-fifth genuine-body step — the audit that pins, for EACH surviving hypothesis of body-394's
`coassoc_gen_of_multiStar_value_geometry`, its canonical inhabitant source in one of four classes:

```text
EXISTING          — a concrete inhabitant already exists in the tree (reuse verbatim);
RFL-WIRING        — becomes `rfl`/pass-through once the faithful concrete `V` is built with the right owner;
NEW CONSTRUCTION  — no faithful constructor exists yet; a genuine new value must be built;
HONEST DATUM      — a base-model geometry axiom, surfaced (not derivable, not a facade).
```

No mega-record; this is a verdict anchor (like body-382).  The ownership-chain root is fixed first:
`D = W.toData`, then `Fmem`, then the faithful `V`, then `Split`.

## The four-class verdict

### NEW CONSTRUCTION — the first true root

* **`V : ResolvedConcreteSummandValueSupply D`** — the ONLY constructor in the tree is `ResolvedConcreteSummandValue
  Supply.ofLegacy S` (`ConcreteSummandValue.lean:123`), and the legacy `Forward` is UNFAITHFUL to the canonical path.
  So a faithful direct `V` (fields `Measure` / `Survivor` / `Remnant` / `quotientForestRaw` + the structural laws
  `union_eq` / `hcross` / `hRdisj` / `quot_eq`, `:68-96`) has NO existing constructor — **this is the genuine first
  root** (body-396).
* **`Concrete : ∀ {G} s, ResolvedConcreteRemnantReembedSupply D G s`** — the re-embedding support containments + CD
  (`ConcreteRemnant.lean:66`); the genuine de-contraction datum, built alongside the faithful `V.Remnant` (body-396).

### RFL-WIRING — pass-through once the faithful `V` is built

* **`Measure : ResolvedMeasureLeafSupply D`** — do NOT duplicate; project from `V.Measure` (the single owner).
* **`hSurvivorComponent`** — `V.Survivor.survivor.survivorComponent = (survivorSupply_of_measure Measure G).survivor
  Component`.  If `V.Survivor := survivorSupply_of_measure Measure` (`FreeClusterBank.lean:58`), this is `rfl`.
* **`Wiring : ResolvedRemnantComponentValueWiringSupply V Concrete`** — `V.Remnant.remnant.remnantComponent =
  (Concrete s).remnantComponent`.  If `V.Remnant` is built from the SAME `Concrete`, this is `rfl` (body-384's gate).

### EXISTING — reuse verbatim from the canonical carrier `W`

* **`D = W.toData`** — the canonical carrier's data (`CanonicalCarrierProper.lean`).
* **`CarrierProper : ResolvedCarrierProperProvider D`** — CONSTRUCTED, `fun G A hA => (index G).mem_proper A hA`
  (`CanonicalCarrierProper.lean:90-91`); not a raw field.
* **`Ids : ResolvedFilteredForestBlockUniqueIdSupply D`** (body-390) — the `q`-local edge/leg id uniqueness; the base
  graphs are `ofFlatGraphWithUniqueIds` (`ResolvedUniqueIdLift.lean:102`), so both leaves are the canonical
  unique-payload win restricted to the live domain.
* **`Fmem : ResolvedSelectedOuterFilteredMemSupply D`** — the selected-outer filtered membership (canonical membership
  adapter, `CanonicalMembershipAdapters.lean`).
* **`Fstar : ResolvedCanonicalStarFacts D`** — `starOf_fresh` + `starOf_injective`; the canonical carrier `W` supplies
  the star assignment, so these are the base-model star facts fielded by `W` (`CanonicalStarFacts.lean:41`).

### HONEST DATUM — base-model geometry, surfaced

* **`StarProm`** (body-383 `promoted_star_agrees`), **`StarRaw`** (body-379 `innerStar_agrees_raw`), **`OccRaw`**
  (body-380 `occurrence_inner_elements_raw`) — the CROSS-AMBIENT star / occurrence-inversion identities; verdicts 379 /
  380 / 383 already recorded them as not derivable from `star_mapPerm`.  NO existing inhabitant — genuine datums
  (body-398), discharged only by the concrete σ-cover star model.
* **`Core : ResolvedMultiStarDecontractionValueCoreSupply D`** — `hE` / `hL` are graph endpoint support (EXISTING); but
  `legLift` (the touched-leg-lift datum, body-376) and `parentCD` (localized-parent CD) are constructed / honest
  (body-397).
* **`Closure : ResolvedMultiStarInnerRawCarrierClosureSupply Core`** (body-377 `innerRaw_mem`) and **`rrm`**
  (`regionRawUnion ∈ D.carrier`, body-341's `recovered_raw_mem`) — the two carrier-closure obligations (body-397); the
  parametric-model membership the resolved carrier isolates.
* **`rep` / `repCD` / `rep_gen`** — the representation section (base leaves, body-399).

## The route to a residual-zero floor

```text
396  faithful concrete V + V-wiring (Wiring / hSurvivorComponent become rfl)
397  Core (legLift / parentCD) + carrier closures (Closure / rrm)
398  StarProm / StarRaw / OccRaw from the concrete σ-cover star model
399  base ownership (Ids / CarrierProper / Fstar / Measure / Split / Fmem) + representation
400  the unconditional wrapper (or the residual-zero floor theorem)
```

Per the HALT: this is the source audit + the four-class verdict ONLY; the faithful `V` is body-396; no new construction,
transport, or datum is landed here; the KEY finding is that `V` has NO faithful direct constructor (only `ofLegacy`).  No
facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

-- Audit anchor only (body-382 style): the four-class inhabitant verdict for the body-394 residual is recorded in the
-- module docstring.  The KEY finding: `ResolvedConcreteSummandValueSupply` has ONLY `ofLegacy` — the faithful direct
-- `V` (body-396) is the genuine first root; `Wiring` / `hSurvivorComponent` then become `rfl` off that owner.

end GaugeGeometry.QFT.Combinatorial
