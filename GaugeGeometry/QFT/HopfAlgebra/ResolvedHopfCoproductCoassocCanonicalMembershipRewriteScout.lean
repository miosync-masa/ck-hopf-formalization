import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCanonicalCarrierProper
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredOuterMembership

/-!
# R-6c-body-230 — canonical membership-rewrite scout: `selectedOuter_mem` / `recovered_outer_mem` reduce to `isProper ∧ isCanonical`

Two-hundred-and-thirtieth genuine-body step, a scout of how to *rewrite* the two constructed-forest membership floor
leaves — `selectedOuter_mem` (body-128) and `recovered_outer_mem` (body-159) — into a certificate about the
constructed forest.  Body-228 grounded `carrier_isProperForest` (137) because the carrier *is* a proper-forest index
carrier and `mem_proper` runs `∈ carrier → IsProperForest`.  These two leaves run the **opposite** direction
(`want ∈ carrier`), so the scout asks which route supplies the intro.  Verdict: **the resolved-index route does not
discharge membership from `IsProperForest` alone** — it reduces `A ∈ carrier` to `A.IsProperForest ∧ (A = ofForgetForest A.forget)`,
a properness certificate **plus a canonicality / section condition**.  Records the certificate schema, the shared
adapter, and the true residual.  Imports 128/159/228 to keep the map honest against the source.

## The two routes (verbatim)

* **Resolved-index route.**  `ResolvedProperForestFiniteIndex` (`ResolvedCoproduct.lean:172`) has only
  `carrier : Finset _` and `mem_proper : ∀ A ∈ carrier, A.IsProperForest` — **no converse**, an opaque `Finset` with no
  intro rule.  `ResolvedProperForestFiniteCover` (`:243`) adds `forget_complete` (pure existence:
  `∀ Aflat ∈ flat filter, ∃ Ares ∈ carrier, Ares.forget = Aflat`) and `forget_injective` (**only over carrier
  members**).  Neither is a membership intro for an arbitrary constructed `A`.
* **Flat route.**  `forget_mem_properDisjointAdmissibleDivergentSubgraphs` (`ResolvedCoproductIndex.lean:130`) takes
  `A.IsProperForest` and lands `A.forget ∈ (G.forget).properDisjointAdmissibleDivergentSubgraphs` (the **flat** carrier
  of `G.forget`, not `D.carrier G`); the filtered `forget_mem_properDisjoint_filter_complement` (`:222`) adds
  `0 < A.forget.complementEdges.card`, landing in the flat-index filter that `forget_complete` consumes.

## Why the resolved route does not close (the key obstruction)

The canonical carrier (`ResolvedPayloadModel.lean:429`) is `carrier = (flat proper index filter).attach.image
(ofForgetForest …)` — the **image of `ofForgetForest`** over the flat index.  So `A ∈ carrier ↔ A = ofForgetForest Af`
for some flat `Af`.  The `forget_complete` + `forget_injective` chain fails at identification:

```text
1. forget_mem_properDisjoint_filter_complement A hA.isProper : A.forget ∈ flat filtered index.        ✓
2. forget_complete A.forget … : ∃ Ares ∈ carrier, Ares.forget = A.forget.                             ✓
   BUT that Ares is ofForgetForest A.forget (the canonical constant-id lift), NOT A.
3. To conclude Ares = A you need forget-injectivity at A. forget_injective needs A ∈ carrier as a
   PREMISE (circular); and forget is NOT globally injective — only forget_injOn_elements within one
   subgraph's components (ResolvedCoproductIndex.lean:50); across subgraphs forget collapses edgeIds.
   → step cannot close.
```

So `A ∈ carrier` reduces to the extra **section condition** `A = ofForgetForest A.forget` — the deferred canonicality
of the construction, NOT implied by `A.IsProperForest`.  Membership is effectively opaque for an arbitrary constructed
forest; the canonical carrier *re-expresses* the leaf, it does not discharge it (matches body-227).

## Certificate schema and the shared adapter (body-231 design)

```lean
structure ResolvedCanonicalMembershipCertificate (I : ResolvedProperForestFiniteIndex G)
    (A : ResolvedAdmissibleSubgraph G) where
  isProper    : A.IsProperForest                    -- flat-index membership via forget_mem_properDisjoint_filter_complement
  isCanonical : A = ofForgetForest A.forget _       -- the TRUE residual: A is in the ofForgetForest lift image

-- shared by 128 (selectedOuterRawOf s) and 159 (region union):
theorem cert_mem {A} (C : ResolvedProperForestFiniteCover G)
    (cert : ResolvedCanonicalMembershipCertificate C.index A) : A ∈ C.index.carrier
```

The adapter's input shape is uniform (`ResolvedAdmissibleSubgraph G`, both built from `.union`), so **128 and 159
share one `cert_mem`** — apply it to `selectedOuterRawOf s` and to `(leftResidual ∪ rightRecovered) ∪ forestRecovered`.
The flat route alternative is a one-liner (`forget_mem_properDisjoint_filter_complement`, no injectivity) but
**retargets** 128/159 to the flat carrier of `G.forget`, changing the leaf statements.

## The real residual after the rewrite

```text
selectedOuterRawOf s = (leftOf s).union (promotedOf s) (cross s)   [Promote.lean:61]
  proved/free : IsPairwiseDisjoint (union structure field via cross); selectedOuterRawOf_vertices_subset (a ⊆, not a conjunct)
  OPEN (all 5 IsProperForest conjuncts): IsNonempty, HasNonemptyComponents, 0<internalEdges.card,
    HasPositiveInternalEdgesComponents, 0<complementEdges.card
region union (leftResidual ∪ rightRecovered) ∪ forestRecovered   [RecoveredOuterMembership.lean:75]
  supplied : hcross_lr, hcross_lrf (cross-disjointnesses)
  OPEN : the same 5 conjuncts
plus (image-carrier route only) : isCanonical section condition A = ofForgetForest A.forget
missing infra either route needs : forget_union / Finset.image_union for (A.union B).forget
  (would follow from union_elements + forget_elements + Finset.image_union; not yet stated)
```

## Assessment and plan

* **The resolved-index certificate is `isProper ∧ isCanonical`**, not `isProper` alone; `isCanonical` (the section
  condition) is a genuine new residual, on top of the five open `IsProperForest` conjuncts.
* **128 and 159 can share one `cert_mem` adapter** — feasible; the constructed inputs have uniform shape.
* **Recommended body-231**: build the shared `ResolvedCanonicalMembershipCertificate` + `cert_mem` adapter (reshaping,
  not proof) so 128/159 are restated as `isProper ∧ isCanonical` on the constructed forest; then the residual is a
  clean list (five conjuncts + section), each a candidate for a later concrete body.  First infra prerequisite: a
  `forget_union` lemma for `(A.union B).forget`.
* **Do NOT take the flat route silently** — it retargets the leaves; if chosen, restate 128/159 against the flat
  carrier explicitly.

Per the HALT: no properness / section body is entered; the exact certificate fields, the shared adapter signature, and
the true residual (five conjuncts + `isCanonical` + the missing `forget_union`) are named.  This is a documentation /
scout anchor (like body-227).  No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
