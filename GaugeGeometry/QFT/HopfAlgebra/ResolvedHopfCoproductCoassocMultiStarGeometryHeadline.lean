import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterCollectionCore

/-!
# R-6c-body-335 — DOCS: the faithful phase-1b geometry is rebuilt on multi-star de-contraction (5th headline)

Three-hundred-and-thirty-fifth genuine-body step — a docs-refresh anchor (no new geometry).  It fixes the FIFTH headline:
the faithful phase-1b path no longer uses the single-parent geometry floor (bodies 293-299); the multi-star de-contraction
geometry (bodies 306-334) is a completed arc that rebuilt the codomain-orphan region model from the ground up.  Reviewer
docs updated: `docs/CK_HOPF_FORMALIZATION_MAP.md` + `docs/CK_HOPF_DEPENDENCY_GRAPH.md`.

## Fifth headline

> The faithful phase-1b path no longer uses the single-parent geometry floor.  Multi-star de-contraction is now
> constructed through touched-component localization and collection-level promotion.  Forward outer reconstruction reduces
> to choice alignment and explicit concrete-model gates, with no parent-membership or singleton-collapse assumption.

## The corrections this arc records (bodies 306-315)

* **floor-297/298 are FALSE at a generic/orphan codomain `z`** (`forest_parent_mem_value` /
  `represented_forest_complete_value`): a multi-star quotient component has no single parent in `z.1.1.elements`.  The
  codomain-side analogue of the retired total `selectedOuter_mem` (body-128).
* **Codomain filtering is not allowed** — it deletes genuine RHS `Δᵣ` terms (multi-star `B` are valid carrier members), so
  it changes the coproduct.  Not a legitimate repair.
* **body-299 is a valid CONDITIONAL theorem**, but its geometry-floor interface (the eight local facts) is UNINHABITABLE in
  the faithful model — `forestComponentMem` (289's field) IS floor-297.  A dead concrete reduction, bypassed.
* **The singleton `promote_collapse` is FALSE for a multi-component `B`** (`promote_elements` emits a collection).
* **body-303's parent-image predicate is SUPERSEDED** by the touched predicate `representedByTouched` (a multi-star parent
  is not a single `z.1.1` component).
* **The external-leg gap is a structural CK datum, NOT a proof deficiency** — `δ.externalLegs` need not equal the
  contract-legs attaching to `δ.vertices` for a generic carrier member; the concrete carrier's quotient components are
  leg-complete (`legLift`).

## The new canonical chain (bodies 316-334, all PROVED axiom-clean)

```text
touchedOuterComponents / touchedOuterForest      (316-317)  the outer components a quotient component δ absorbs
→ localize δ into the touched-forest contraction  (318-321)  M1 (vertex/edge/leg + assembly)
→ touched-leg-lift parent                          (326)      localizedParentWithTouchedLegs (custom leg preimage)
→ toInner / innerRaw                               (327-328)  retype touched components inside the parent
→ promote-to-touched-collection                    (328)      M3: (promote parent innerRaw).elements = touched collection
→ parent disjointness / injectivity                (329-330)  D4 (consumes starOf_fresh + cd_nonempty)
→ concrete forestTag                               (331-333)  componentToForest := parent, forestTag := ⟨innerRaw, mem⟩
→ promotedTouchedUnion                             (334)      ⋃ promoted inner forests = represented outer components
→ leftResidual ∪ promotedTouched = original outer  (334)      D5+M3 forward-outer collection core, NO floor-297
```

## Two-layer status (reviewer distinction)

```text
PROVED mechanical geometry                         Explicit model / construction gates
--------------------------                         --------------------------------
M1 localization              (316-321)             legLift (δ-leg-completeness, structural CK)
M3 collection promotion      (322-328)             parentCD (M2b, power-counting)
D4 disjointness/injectivity  (329-330)             innerRaw_mem (ForestIdx carrier landing)
forest source/tag construction (331-333)           starOf_fresh / cd_nonempty (canonical star / measure providers)
collection-level forward-outer core (334)          choice alignment (leftOf/promotedOf = touched — NOT yet built)
                                                    cross-disjointness (right/left/forest regions)
                                                    recovered_raw_mem (Group-3 carrier closure)
                                                    Front-2 quotient/remnant coherence
```

**Crucial separation:** `forestTag` is now a CONSTRUCTION (body-333, via D4 uniqueness), NOT an arbitrary field.  Its
forward-image identity `forestTag_agrees` (`= occurrence.B`) is a THEOREM-pending leaf that confluences with Front-2
(V.Remnant occurrence), NOT a standing model datum — a strict improvement over the retired opaque-field status (body-295).

Per the HALT: docs-only anchor; no new geometry; the corrections/chain/status pin the reviewer map; no facade, no flat
term, no `forgetHopf`.  Full unconditional resolved coassociativity is STILL not claimed — choice alignment, the concrete
model gates, and Front-2 confluence remain — but the multi-star de-contraction geometry is a completed, axiom-clean arc.
-/
