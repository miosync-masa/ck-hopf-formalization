import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterReindexInterface

/-!
# R-6c-body-51 — the final facade-free dependency map of `Δᵣ`-coassociativity

Fifty-first genuine-body step, a CONSOLIDATION: one file fixing the whole reduction of resolved
`Δᵣ`-coassociativity to its remaining primitive assumptions, in Lean-near names.  No new mathematics — a
documentation + capstone re-export.  Everything referenced is axiom-clean (`propext` / `Classical.choice` /
`Quot.sound`); no facade, no flat term, no `forgetHopf`, no rep/perm.

## Top-level theorem chain (support-9 + regroup, bodies 36–38, 50)

```text
coassoc_gen  (D.coassocLeft (X x) = D.coassocRight (X x))
  ⇐ ResolvedOuterReindexInterfaceSupply D          (body-50: .coassoc_gen)
  ⇐ ResolvedRegroupReindexSupply D                 (body-38: rep choice + grand + 2 cover reindexes)
  ⇐ ResolvedRegroupAgreementSupply D               (body-37: rep_eq + agreements at representative)
  ⇐ ResolvedCoassocRepresentativeFamilySupply D    (body-36: repGraph + grand + 2 regroup agreements)
  ⇐ (∀ x) ResolvedCoassocGrandFullSupply D (repGraph x)   (leaf-12a: ImageTerm + finite cover fields)
        ⇐ term_eq heart (product_eq + right_eq) + finite carriers/cover_on/inj_on
```

The regroup-agreement linearity half is PROVED (`regroupImageSum_eq_outerSum` / `regroupBranchSum_eq_outerSum`,
body-38); the finite-cover partition is the R-4-full `ResolvedFiniteBranchMapLayer.sum_reindex` (body-39
supplies the `cross` disjointness).

## Remaining primitive leaf groups (everything else is wiring or proved)

**MEASURE / power-counting** (`ResolvedMeasureLeafSupply D`, body-34):
* `cd_nonempty` — a connected-divergent subgraph has nonempty vertices;
* `contract_preserves_CD` — contracting an admissible subforest of a CD graph is CD (CK stability).

**STAR / ALLOCATION** — the star-allocation axiom system:
* *parent traceability* (`ResolvedStarGlobalGapSupply`, body-26): `star_avoids_outer_vertices`, `star_trace`,
  `contracted_nonempty` — global freshness + a shared star ⇒ equal parents;
* *retarget-left coherence* (`ResolvedLeftStarCompatibilitySupply`, body-47): `componentAt_agree`,
  `star_coherence` — one component's star is the same `VertexId` via `s.1.1` or the selected outer;
* *retarget-right sector inverse* (`ResolvedQuotientStarSymmRecoverySupply`, body-49): `symm_recovers`,
  `htwoInv` — `quotientStarEquiv.symm` returns the source index;
* *canonical local* (`ResolvedCanonicalStarFacts D`, leaf-1): `starOf_fresh`, `starOf_injective`
  (component-local; body-26 needs the GLOBAL strengthening `ResolvedStarGlobalGapSupply`).

**TRANSPORT / REGION** (bodies 2, 9, 10, 11; classification):
* `quotientForest_gvertices_subset` (body-9), `left_star_mem_quotientGraph` /
  `left_star_not_mem_quotientForest` (body-10, survival), `inside_not_selected_in_quotient` /
  `selected_star_survivor_is_left` (body-11, two-stage split), region `survivor_avoids` / `remnant_subset`
  (body-2, vertex cross), `TSV_not_survivor` (body-44), `freshA` / `freshB`.

**COVER / REINDEX** (bodies 39, 50):
* the four `OuterReindexInterface` adapters — outer-carrier / cover / weight / summand identifications to the
  R-4-full `concrete_sum_reindex` / `outer_sum_reindex` engines (`grandFull_forest_image_ne_mixed_image` = the
  `cross`).

**REMNANT / de-contraction** (bodies 7, 19–26):
* remnant containment / CD; occurrence parent injectivity — reduced to `parent_graph_inj` → `parentKey` →
  `vertices_determine_parent` (PROVED, body-24) → the STAR parent-traceability group above +
  `parent_disjoint` (PROVED from the proper-forest `pairwiseDisjoint`, body-25).

## Structural note

The primitive supplies live at DIFFERENT parameter levels — `D` (measure, canonical star, reindex), `(D, G,
imageOf)` (retarget star / transport), `(D, G, s)` (parent) — so they do NOT combine into a single `D`-level
record; they assemble per-representative when a `ResolvedCoassocGrandFullSupply D (repGraph x)` is built.  The
single top-level entry point over `D` is therefore `ResolvedOuterReindexInterfaceSupply D` (whose `grand`
field carries the per-representative heart+cover), re-exported below.

Landed:

* `resolved_coassoc_gen_of_outer_reindex` — the capstone, `Δᵣ`-coassociativity on every generator from the
  single top-level `D`-record (re-export of body-50).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-51 — the capstone.**  Resolved `Δᵣ`-coassociativity on every generator, from the single
top-level `D`-record `ResolvedOuterReindexInterfaceSupply` (whose fields are exactly the remaining primitive
leaf groups + the R-4-full-engine reindex interface).  Axiom-clean; no facade. -/
theorem resolved_coassoc_gen_of_outer_reindex
    (F : ResolvedOuterReindexInterfaceSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  F.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
