import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalMembershipCertificate
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterIsProper

/-!
# R-6c-body-265 — `recovered_eq` scout: honest leaf, but the live sum bypasses the certificate (2026-07-13)

Two-hundred-and-sixty-fifth genuine-body step, the audit of the last certificate field `recovered_eq`.  **Verdict:
(3) HONEST LEAF for the generic `recovered_eq` — but the live sum does NOT need the certificate at all.**  Carrier
membership is already supplied on the forward image by the subtype fields, transported to the bare-subgraph statements
via `ext_elements` — the *same* extensionality route body-264 used, needing no forget-injectivity.

## The generic `recovered_eq` is an honest leaf

```text
forget is NOT globally injective — forget_injOn_elements (ResolvedCoproductIndex.lean:50) is single-subgraph only;
  forget collapses edgeIds across subgraphs (ResolvedCoproductIndex.lean:143-149). So Ares.forget = A.forget → Ares = A
  is FALSE for arbitrary Ares, A.
forget_injective (cover) needs BOTH args ∈ carrier (ResolvedCoproduct.lean:252) — circular via cert_mem.
forget_complete gives EXISTENCE only (∃ Ares ∈ carrier, Ares.forget = Aflat) — the witness is ofForgetForest Aflat,
  not the caller's A (ResolvedPayloadModel.lean:441).
NO section: forget_ofForgetForest (ResolvedPayloadModel.lean:354) is the RETRACTION (forget ∘ ofForgetForest = id);
  A = ofForgetForest A.forget does NOT hold for arbitrary resolved A (ofForgetForest re-lifts to constant ids; promote
  keeps δ's ids, ResolvedSubgraphPromote.lean:46). So recovered_eq's isCanonical section is not shape-free.
```

So generic `recovered_eq` has the **pre-migration status of `selectedOuter_mem` (128) / `recovered_outer_mem` (159)**:
a construction-specific carrier-closure leaf, dischargeable only against the canonical `ofForgetForest`-image carrier —
**not provable generically**.  (Verdict 1 DIRECT SECTION: no; verdict 2 SHAPE-SPECIFIC: possible but not the live
route; verdict 3 HONEST LEAF: yes.)

## But the live sum does NOT need the certificate — membership is free on the forward image

* **Y — the forward-image recovered outer is already a carrier member.**  `unionOuter z :
  {A' // A' ∈ D.carrier G}` (`OuterUnionConstruction.lean:85`), so `(unionOuter z).2` is membership **for free, for
  every z** — no certificate.  Likewise `selectedOuterOf : … → {A // A ∈ D.carrier G}` (`ImageSupply.lean:48`), its
  `.2` free.
* **The `ext_elements` bridge closes the bare-subgraph leaf (non-circular).**  `union_eq`
  (`OuterUnionConstruction.lean:88`): `(unionOuter z).1.elements = leftResidual ∪ rightRecovered ∪ forestRecovered`.
  `ResolvedAdmissibleSubgraph.ext_elements` on it gives `bareUnion = (unionOuter z).1`, then `(unionOuter z).2` gives
  `bareUnion ∈ D.carrier G` — discharging `recovered_outer_mem` (159) **without** `recovered_eq`, `forget_injective`,
  or any section.  This is exactly the extensionality route body-264 already used
  (`isProperForest_of_elements_eq`, `SelectedOuterIsProper.lean`).
* **Generic `z` never forces the certificate.**  `recovered_outer_mem` is typed `∀ z` (`RecoveredOuterMembership.lean:75`),
  but every `z` fed by the bijection is a forward-image element whose union coincides (by `union_eq`) with the
  free-membership `unionOuter z`.  No truly-generic codomain `z` (outside the `unionOuter` / `selectedOuterOf` image) is
  summed over.

## Assessment and plan

* **`recovered_eq` (generic certificate) is an honest leaf** — do not attempt to prove it (forget not globally
  injective).  The certificate route (body-232/233) is a *sufficient* interface, not the *necessary* one.
* **body-266 target: discharge `recovered_outer_mem` (159) via the `ext_elements` bridge**, not the certificate:
  from `unionOuter z` (carrier member by `.2`) + `union_eq` (elements equality) + `ext_elements`, the bare region union
  is a carrier member.  This mirrors body-264's `isProperForest_of_elements_eq` and needs no forget-injectivity, no
  section, no `recovered_eq`.
* **Split recorded**: Y on the forward image bypasses the certificate (free `unionOuter.2`); Y on a generic `z` outside
  the image would need the section, but no such `z` occurs in the live sum.

Per the HALT: no proof is entered; the verdict (honest leaf), the certificate-bypass (free `.2` membership +
`ext_elements`), and the body-266 target are named — the certificate route is not the critical path.  This is a
documentation / scout anchor (like body-257).  No declarations beyond this docstring.  No facade, no flat term, no
`forgetHopf`.
-/
