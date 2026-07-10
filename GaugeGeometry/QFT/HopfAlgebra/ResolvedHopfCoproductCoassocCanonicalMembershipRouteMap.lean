import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalMembershipAdapters

/-!
# R-6c-body-234 — canonical membership route map: bodies 230–233 (docs anchor)

Two-hundred-and-thirty-fourth genuine-body step, a documentation anchor (no new geometry).  It fixes the completed
canonical membership route: `selectedOuter_mem` (128) and `recovered_outer_mem` (159) — two of the four carrier-closure
floor leaves — are now supplied from membership certificates, not raw hypotheses.  Imports body-233 so the map stays
type-checked.  Reader-facing narrative: `CK_HOPF_FORMALIZATION_MAP.md` §"R-6c bodies 230–233"; proof-dependency map:
`CK_HOPF_DEPENDENCY_GRAPH.md` §"R-6c bodies 230–233".

## The route (bodies 230–233)

```text
230  scout:  membership = isProper + canonical/section, NOT isProper alone.
     forget_complete gives EXISTENCE only; forget is not globally injective, so the constructed forest's identity
     must be supplied (the section condition A = ofForgetForest A.forget).

231  forget_union_elements (PROVED, infra):
     (A.union B).forget.elements = A.forget.elements ∪ B.forget.elements    (union_elements + forget_elements
     + Finset.image_union). The tool for building certificates on the constructed unions.

232  certificate:
     ResolvedCanonicalMembershipCertificate (C : ResolvedProperForestFiniteCover G) (A)
       isProper     : A.IsProperForest
       recovered_eq : ∀ Ares ∈ C.index.carrier, Ares.forget = A.forget → Ares = A   (section, generic form)
     cert_mem (PROVED) : certificate → A ∈ C.index.carrier

233  adapters:
     ResolvedCanonicalCarrierWiring D { cover ; carrier_eq : D.carrier G = (cover G).index.carrier }
       .selectedOuterMem      (PROVED) : ∀ s, cert (selectedOuterRawOf s) → selectedOuter_mem (128)
       .recoveredOuterSupply  (PROVED) : ∀ z, cert (region union) → ResolvedRecoveredOuterCarrierSupply (159)
```

## The canonical route

```text
forget_union infra (231)
  → certificate fields  isProper + recovered_eq  (232)
  → cert_mem                                     (232)
  → selectedOuter_mem / recovered_outer_mem      (233, via carrier_eq)
```

## Status table (the four closure floor leaves)

```text
carrier_isProperForest   grounded by 228 (proved from ResolvedProperForestFiniteIndex.mem_proper)
selectedOuter_mem        reduced to selectedOuter_cert + carrier_eq (body-233)
recovered_outer_mem      reduced to recoveredOuter_cert + carrier_eq (body-233)
region cross-disjoint    still construction-specific (158)
```

## Residual (refreshed)

* **grounded** — `carrier_isProperForest` (body-228);
* **certificate fields (the new residual for 128/159)** — `isProper` (five `IsProperForest` conjuncts) and
  `recovered_eq` (the section condition), each per constructed forest; plus the `carrier_eq` canonical-`D` wiring;
* **still construction-specific** — the region pairwise disjointnesses (158);
* **other floors** — the eight sector `sound` / `complete` directions (bodies 219–222), forward compatibility
  (`forestTag` / `promote_collapse` 188, `forestComponentMem` 185, `represented_cases` 180), and the non-region base
  (contract geometry, measure, survivor/remnant `Inj`/`Gen`, `rep`, and the heavy canonical fields).

## Note

The next front is to **fill a certificate field** — the first `IsProperForest` conjunct (e.g. `IsNonempty`) for
`selectedOuterRawOf` / the region union, via `forget_union_elements` (body-231) — reached through an
`IsProper conjunct` scout (body-235) that picks the conjunct that falls first (the difficulty may differ between the
selected outer and the region union).  No declarations beyond this docstring anchor; the import keeps the map honest
against the source.  No facade, no flat term, no `forgetHopf`.
-/
