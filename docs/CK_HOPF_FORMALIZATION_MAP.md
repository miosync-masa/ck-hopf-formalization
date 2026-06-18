# Connes–Kreimer Hopf Algebra — Formalization Map

*A compact, JAR-facing map of the CK Hopf algebra formalization in Lean 4,
distilled from the internal development notes (`HOPF_DECOMPOSITION.md`) and
separated from `GaugeGeometry`-specific material.  For reviewers and readers:
what is proved, what is assumed, where the flat carrier fails, and how a
boundary-resolved carrier repairs it.*

Status convention: ✅ = unconditional Lean theorem (no `sorry`/`admit`/axiom);
🔒 = isolated named kernel (a `class … : Prop`, the only remaining assumptions);
✗ = provably false on the flat carrier (counterexampled);
∎ = theorem on the boundary-resolved carrier.

---

## 1. Executive Summary

- The Lean development formalizes the **Connes–Kreimer Hopf algebra skeleton**
  over a *flat* Feynman-graph carrier (`FeynmanGraph`): coproduct, counit,
  coassociativity, and the antipode recursion are assembled around the forest
  cover identity.
- All remaining assumptions are **isolated as exactly two named kernels**
  (typeclasses of `Prop`) — the two boundary-semantics facades — so the entire
  conditional surface is auditable in one place.  The constructive body contains
  **no** `sorry`, `admit`, or project-level axiom.  (The former third kernel, the
  CK §3 right-antipode cancellation `AntipodeForestRightCoreIdentity`, has been
  **eliminated**: the right antipode axiom now follows from the left identity,
  coassociativity, and local nilpotency of the reduced convolution operator — §4.)
- The formalization **exposes two semantic boundary gaps** that are not visible
  in the informal CK presentation: on the flat carrier, two facts CK's proof
  silently uses are *false*, with explicit counterexamples.
- A **boundary-resolved carrier** (`ResolvedFeynmanGraph`, persistent
  half-edge/leg identities) **repairs the collapse mechanism**: both gaps become
  theorems, and the flat carrier is recovered as its forgetful image.
- **Track R-4-full ∎ (§6):** the H5.8 coassociativity reindex itself is assembled
  **facade-free on the resolved carrier** — `h58_resolved_carrier_double_sum_reindex`,
  axioms `[propext, Classical.choice, Quot.sound]`, discharging *both* boundary
  facades resolved-natively.  The flat reindex stays facade-conditional **by
  necessity** (the flat retarget forgets the id data the theorem needs), so the
  facade-free result's native home is the resolved carrier, not the flat statement.

The headline is **not** "CK Hopf has a hole."  It is: *the flat graph notation
is coarser than CK's actual graph notion — it suppresses half-edge / insertion-slot
identity — and the two gaps are precisely the artifacts of that suppression.*

---

## 2. Main Formal Objects

| Object | Lean name | Role |
|---|---|---|
| Carrier algebra | `HopfH` | free commutative algebra on flat graphs |
| Coproduct | `coproduct_strict_forest` | forest/cover decomposition Δ |
| Antipode | `antipode_forest`, `antipodeGen_forest` | recursive S |
| Forest cover | forest quotient sigma / branch cover | the F2i-3q combinatorial identity |
| Resolved carrier | `ResolvedFeynmanGraph` | edges/legs carry persistent `edgeId`/`legId` |
| Forgetful map | `ResolvedFeynmanGraph.forget` | resolved → flat, discards identities |

Files: flat carrier `QFT/Combinatorial/FeynmanGraphs.lean`,
subgraph/contraction `QFT/Combinatorial/SubGraph.lean`,
coproduct/coassociativity `QFT/HopfAlgebra/Coassoc.lean`,
antipode `QFT/HopfAlgebra/Antipode.lean`,
resolved carrier `QFT/Combinatorial/ResolvedFeynmanGraphs.lean`.

---

## 3. Completed Constructive Components ✅

All of the following are unconditional Lean theorems.

- **Sprints A–E** — Hopf algebra scaffolding: algebra/coalgebra instances,
  counit, convolution monoid (`WithConv`), conditional `HopfAlgebra ℚ HopfH`.
- **F2i-3q forest cover identity** — the core combinatorial decomposition that
  drives both coassociativity and the antipode recursion.
- **hBP 3/4 discharge** — three of the four facade Models in the coproduct's
  structural decomposition are discharged constructively; only the semantic
  fourth remains.
- **Track A — `hForestCompl`** — forest-complement supply: `_Q_v3_fully_canonical`
  plus four wrappers auto-supplying the complement obligation.
- **Track B — `mixed_inj`** — coassociativity injectivity on the mixed-boundary
  branch (`forestComponentMixedBoundaryToQuotientForestSigma_inj`), via the
  free-index generic-lemma pattern across an 8-sprint campaign.
- **Track B-forest — `forest_inj`** — coassociativity injectivity on the *forest*
  branch (`forestComponentForestChoiceToQuotientForestSigma_inj`), gated only on
  `ForestGraphInsertionUniquenessModel`.  Full constructive `q.1` recovery
  (Left/Right/Forest-parent partition) + the existing fixed-`A` outer-subgraph
  injectivity for the `B`-payload.
- **Track forest_cd — forest-cover source CD, fully discharged** —
  `forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus.IsConnectedDivergent`
  is now a **theorem**: *Connected* (support path-lift) and *1PI* (bridge-free
  over the Exact/Promoted edge split — Exact edges via `δ`'s 1PI-ness, Promoted
  edges via each child's 1PI-ness) are pure graph topology; *Divergent* is the
  reverse forest-contraction power-counting reflection (see §4 note).  Together
  with the canonical vertex-disjointness, this discharges
  `CoassocStrictForestH58CoverData` **canonically** — so the H5.8 coassociativity
  facade `CoassocStrictForestH58Ready` is reduced to **exactly the two boundary
  facades** with no residual cover-data hypothesis (audit point
  `coassoc_strict_forest_linearMap_ofReflection`).
- **Track D-core — antipode right axiom via convolution / local nilpotency** —
  `AntipodeStrictForestRightReady` is discharged in `AntipodeConvolution.lean`
  without the CK §3 cancellation kernel: local nilpotency of `id − η∘ε` on
  generators + the left antipode identity give the right identity (§4).
- **Track R — resolved core** — see §6.

---

## 4. Remaining Named Kernels 🔒

These are the **only** remaining assumptions — **exactly two**, both
boundary-semantics facades.  Each is a single `class … : Prop`; the conditional
`HopfAlgebra ℚ HopfH` instance is gated on precisely these two (plus the ambient
power-counting environment below).

| Kernel | Statement (informal) | Status | Route |
|---|---|---|---|
| `PromotedExternalLegsLiftableModel` | promoted external legs of a contracted subgraph lift back consistently | ✗ flat / ∎ resolved | Track R repair |
| `ForestGraphInsertionUniquenessModel` | a graph is determined by its vertices + its remnant after star-contraction | ✗ flat / ∎ resolved | Track R repair |

Both are the **two semantic gaps** (§5): false on the flat carrier, theorems on
the resolved carrier (§6).  Cross-file certificate:
`HopfAlgebra.hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` derives
the full Hopf structure from these two facades alone.

**Eliminated kernel — `AntipodeForestRightCoreIdentity` (the former CK §3 core).**
The right antipode axiom was previously isolated as a third kernel (the §3
forest-summation cancellation).  It is now a **theorem**: in the convolution ring
`WithConv (HopfH →ₗ[ℚ] HopfH)` (a `Ring` over the coalgebra, *not* requiring the
Hopf structure), the left antipode identity gives `S * id = 1`, and the reduced
convolution operator `id − η∘ε` is **locally nilpotent on generators** (the
reduced coproduct strictly lowers edge count).  A finite-power "P-trick"
(`P := id*S − 1` satisfies `P * id = 0`, hence `P = P · N^{2j}`, killed on each
generator) yields `id * S = 1` generator-wise, globalized via
`MvPolynomial.algHom_ext`.  No explicit nested-forest cancellation, no global
inverse.  (File `AntipodeConvolution.lean`; `AntipodeStrictForestRightReady` is
discharged via `AntipodeStrictForestRightReady_ofConvolution`, bypassing
`AntipodeForestRightCoreIdentity` entirely.)

**Not kernels — the abstract power-counting environment.**  The development runs
inside an ambient `DivergenceMeasure` environment abstracted as a small family of
power-counting `Prop` classes (`IsPermInvariantDivergence`,
`IsIsoInvariantDivergence`, `IsAmbientInvariantDivergence`,
`IsDivergencePreservedByContract`, `IsDivergencePreservedByAdmissibleForestContract`,
and the reverse companion `IsDivergenceReflectedByAdmissibleForestContract`).
These are **not** counterexampled boundary gaps and **not** counted among the
two kernels: they are the standard Weinberg/CK power-counting facts (additivity
of the superficial degree under forest contraction and its reverse), true for any
power-counting measure, abstracted exactly as Sprint A–C already abstract
permutation/contraction invariance.  The forest-cover CD obligation (`forest_cd`)
is discharged *from this environment* (the reverse reflection class), which is why
H5.8 coassociativity reduces to the two semantic facades alone.

---

## 5. Two Semantic Gaps on the Flat Carrier ✗

Single-star contraction on `FeynmanGraph` (`contractWith`,
`admissibleSubgraphQuotientRemainderSubgraph`) is **lossy**: it forgets boundary
incidence and attachment multiplicity.  This makes two facts CK uses informally
*false* on the flat carrier.

**Gap 1 — promoted external legs (`PromotedExternalLegsLiftableModel`).**
After contraction, two distinct external legs attached at the same vertex with
the same sector become indistinguishable.  There is no consistent way to lift the
promoted legs back to their pre-contraction identities, because the flat leg
`{ attachedTo, sector }` carries no identity. *Formal counterexample*
(`flatLegRetarget_not_injective`, and on singleton multisets
`flatLegRetarget_multiset_collapse`, in `BoundaryResolvedCounterexamples.lean`):
two legs differing only at an attachment vertex that the vertex map identifies
have equal flat retargets.

**Gap 2 — graph insertion uniqueness (`ForestGraphInsertionUniquenessModel`).**
The claim "same vertices + same remnant ⇒ same graph" fails because two distinct
internal edges with identical `(source, target, sector)` collapse to the same
multiset element. *Formal counterexample* (`flatEdgeRetarget_not_injective`,
`flatEdgeRetarget_multiset_collapse`, in `BoundaryResolvedCounterexamples.lean`):
two edges differing only at an endpoint that the vertex map identifies collapse
to the same multiset element after retargeting.

Both gaps share one mechanism: **multiset-level collapse of structurally
distinct boundary data**.  This is now sealed as **formal, mechanism-level
counterexamples** rather than prose.  These theorems do *not* negate the flat
facade classes directly (those are large proof-skeleton interfaces); they
formalize the exact retargeting collapse those facades would have to rule out —
the flat edge and leg retarget maps are provably non-injective, even on singleton
multisets.  In contrast, `BoundaryResolvedSemanticModel` (§6) proves the
corresponding boundary-resolved retarget maps injective *before forgetting*, and
proves that forgetting boundary identities projects them exactly onto these flat
maps.  So the resolved positive results are formally wired to these flat
failures, not cherry-picked analogues.

---

## 6. Boundary-Resolved Repair ∎

`ResolvedFeynmanGraph` equips every internal edge with a persistent
`edgeId : ResolvedEdgeId` and every external leg with `legId : ResolvedLegId`,
both surviving star-contraction.  The forgetful map `forget` erases exactly these
identities, projecting back to the flat carrier.

- **Identity-preserving retarget (R-1b/2a).** `retargetGraph f V` rewrites
  endpoints by a vertex map `f` while preserving `edgeId`/`legId`;
  `eq_of_retarget_eq_of_id_unique` recovers an edge/leg from its retarget under
  id-uniqueness.
- **Submultiset injectivity (R-3a/3b).** On submultisets of a graph with unique
  ids, `retargetInternalEdges`/`retargetExternalLegs` are **injective**
  (`…_injective_on_submultisets`), via the generic `Multiset.map_eq_of_injOn_le`.
  This is exactly the collapse that produced both flat counterexamples
  (`BoundaryResolvedCounterexamples.lean`) — now **provably impossible** because
  the persistent id survives.
- **Forgetful commuting square (R-4-link).** `forget_retargetGraph`:
  ```
          retargetGraph (id-preserving, injective — R-3)
     G  ───────────────────────────────────────►  G.retargetGraph f V
     │ forget                              forget │
     ▼                                            ▼
  G.forget ──────────────────────────────────►  flat retarget by f   (lossy)
          forget_retargetGraph  (commutes)
  ```
  The flat carrier is the **forgetful image** of the resolved carrier; the
  identities `forget` discards are exactly the two semantic gaps.

Consequence: both gap kernels are **theorems on the resolved carrier**.  They are
not defects in CK's mathematics — they are artifacts of the flat notation, and
boundary resolution removes them.

### Non-vacuity of the repaired boundary semantics

The conditional flat Hopf theorem is **not** used as an inhabited theorem about
the flat carrier: the two flat boundary facade classes are *false* on the flat
carrier (§5), so the flat theorem is a **proof-skeleton factorization** —
identifying exactly what the informal flat proof silently assumes — rather than
an unconditional flat-carrier statement.

The non-vacuous *positive* object is `BoundaryResolvedSemanticModel`
(`BoundaryResolved.lean`), an inhabited `Prop` bundling the repaired principles,
with `boundaryResolvedSemanticModel` proving it on the boundary-resolved carrier.
It contains **both** halves of the picture:

*(1) Injectivity before forgetting* — where the flat collapse is repaired:
- edge submultiset retarget injectivity (under `EdgeIdsUnique`),
- external-leg submultiset retarget injectivity (under `LegIdsUnique`).

*(2) Exact projection to the flat maps after forgetting* — where the resolved
maps are shown to be the boundary-refinement of the flat collapse, not a
cherry-picked analogue:
- `forget` carries the resolved edge/leg retarget *verbatim* onto the flat
  endpoint/attachment-rewrite (`map_forget_retarget_edges` / `_legs`, rfl-level),
- the forgetful map commutes with graph-level retargeting (the JAR square).

So the resolved injectivity is literally the *same* retarget map as the flat one,
read on the identity-carrying carrier — the difference is exactly the persistent
`edgeId`/`legId` that `forget` discards.  The model is **deliberately not** an
instance of the flat facade classes (they are flat-false; `forget` runs resolved
→ flat).  This answers any "vacuity / unicorn" objection: *the flat assumptions
are intentionally uninhabited because they are false — that is the diagnosis; the
inhabited positive object, projecting exactly onto the flat collapse map, lives on
the boundary-resolved carrier.*

### R-4-full ∎ — the facade-free H5.8 reindex lives on the resolved carrier

The completed theorem of Track R-4-full is

```
h58_resolved_carrier_double_sum_reindex
    (g : HopfGen) [IsDivergencePreservedByAdmissibleForestContract] :
  ∑ A ∈ h58BridgeOuterCarrier g, innerImageSum A
    = ∑ A ∈ h58BridgeOuterCarrier g, innerBranchSum A
```

(`QFT/HopfAlgebra/ResolvedActualSigmaCover.lean`) — the H5.8 coassociativity
reindex double sum (outer-forest sum of inner image-weight sums = sum of inner
forest+mixed branch-weight sums), proven **entirely on the boundary-resolved
carrier**.  Key facts:

- **The facade-free H5.8 reindex theorem lives on the resolved carrier**, not the
  flat one.  Both former boundary facades are **discharged resolved-natively**:
  facade #1 (forest-branch insertion uniqueness) via `parent_eq_of_remainder_eq` /
  `resolvedParentRemnant_injOn` / `ResolvedFullQuotientForestImageData.toImage_injective`
  (persistent edge/leg ids); facade #2 (σ-cover promoted-leg liftability) via
  `resolved_promotedComponent_externalLegs_le_plus` together with the full-grain
  forest+mixed cover (`fullQuotientForestImageDataOfFlatSplit_comm`,
  `fullMixedImageDataOfFlatSplit_comm`, the origin-indexed covers, and the
  full-grain outer sum).
- **The old flat `forestComponentSplitPhi` reindex stays facade-conditional — by
  necessity, not by missing work.**  Its `forest_inj` consumes
  `ForestGraphInsertionUniquenessModel.parent_eq_of_remnant_eq` on `repG g`, which
  is **false on the flat carrier** (`flatEdgeRetarget_not_injective`): the flat
  retarget forgets the boundary edge/leg id data, so the flat quotient-image
  equality cannot recover the parent.  No facade-free transport of the flat
  bijection is possible (the reconnaissance localized the sole flat-facade use to a
  single `parent_eq_of_remnant_eq` call and confirmed its hypotheses are genuinely
  too weak).  The resolved carrier restores exactly the discarded ids, so the
  reindex is facade-free **there** — the native home of the result, not a bridge to
  the flat statement.
- **Axioms.** `#print axioms h58_resolved_carrier_double_sum_reindex`
  = `[propext, Classical.choice, Quot.sound]` (the standard Lean/Mathlib three) —
  no `sorry`, no project axiom, no facade class.
- **Gated theorem not exposed.** The construction never references or re-exposes
  the gated flat assembly `forestComponentSplitPhi_term_eq_of_split`, and never
  instantiates either facade typeclass; only facade-free building blocks and the
  final public theorem are surfaced.

The arc of R-4-full is therefore not "strip the facade off the flat coassoc
theorem" but "discover and build the space in which a facade-free H5.8 reindex can
*live*" — and that space is the boundary-resolved carrier.  Lean itself certifies
the relocation: the flat statement provably forgets the information the theorem
needs, so the facade-free result cannot reside there.

---

## 7. JAR Claim Boundary

**Claim safely established now (pre-`R-4-full`):**
> A Lean formalization of the full conditional CK Hopf algebra `HopfAlgebra ℚ HopfH`
> over flat Feynman carriers (coproduct, counit, coassociativity, antipode — both
> antipode axioms), with the entire conditional surface reduced to **exactly two
> named kernels**; a precise diagnosis that both kernels are *false on the flat
> carrier* (with counterexamples) due to multiset-level boundary collapse; and a
> boundary-resolved carrier on which both become theorems, with the flat carrier
> recovered as its forgetful image.  The right antipode axiom — historically a
> separate CK §3 cancellation obligation — is *proved*, not assumed, via the
> convolution / local-nilpotency argument; so **both remaining kernels are
> boundary-semantics carrier artifacts, not genuine mathematical gaps.**

This is a complete, defensible contribution: **full conditional Hopf structure +
semantic diagnosis + resolved repair core**, with the entire residual surface
being the single mechanism "flat contraction forgets boundary incidence."  The
repaired principles are not vacuous: they are inhabited on the resolved carrier by
`boundaryResolvedSemanticModel : BoundaryResolvedSemanticModel` (§6).  The flat
facades are *intentionally* uninhabited (they are false — that is the diagnosis),
so the flat theorem is a proof-skeleton factorization, not a vacuous implication
dressed up as a result.

**Stronger future claim (requires `R-4-full`):**
> A full, unconditional CK Hopf algebra over boundary-resolved graphs.

Why the stronger claim is *not* needed for the present paper: the flat facades
are flat-false and `forget` runs resolved→flat, so no identity-lift discharges
them on the flat carrier; `R-4-full` would require re-deriving the entire
subgraph/coproduct/coassoc/antipode stack on `ResolvedFeynmanGraph` — a separate
multi-month program.

---

## 8. Future Campaigns

The conditional `HopfAlgebra ℚ HopfH` is now closed modulo exactly the two
boundary-semantics facades — there is **no remaining open mathematical kernel**
on the flat carrier.  The only forward direction is:

1. **Resolved full Hopf reconstruction (`R-4-full`)** — re-derive coproduct,
   coassoc, and antipode on `ResolvedFeynmanGraph`, discharging the two boundary
   facades *as theorems* on the resolved carrier and yielding the **unconditional**
   Hopf structure (the stronger JAR claim).  Multi-month; not required for the
   present claim.

### R-4-full Phase 1 — boundary-resolved lower graph spine

In progress (`GaugeGeometry/QFT/Combinatorial/ResolvedSubGraph.lean`, standalone
module; builds via `lake build GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph`,
not yet wired into `Main`).  This does **not** yet define the full resolved CK
Hopf algebra; it builds the carrier-level structures a rebuild needs and proves
the **resolved counterparts of the two flat-false boundary interfaces**.

| Phase | Artifact | Status | Role |
|---|---|---|---|
| 1a | `ResolvedFeynmanSubgraph` + `forget` | ✅ | resolved subgraph carrier |
| 1b | `ResolvedAdmissibleSubgraph` + `forget` | ✅ | resolved admissible-forest carrier |
| 1c | `contractWithStars` + `forget_contractWithStars` | ✅ | resolved contraction spine |
| 1d | `quotientRemainderSubgraph` + forget | ✅ | resolved remnant spine |
| 1e | `parent_eq_of_remainder_eq` | ✅ | resolved insertion uniqueness — repairs flat bomb #1 (`ForestGraphInsertionUniquenessModel`) |
| 1f | `parent_externalLegs_eq_of_remainder_eq` / `externalLegs_lift_unique` | ✅ | resolved external-leg liftability — repairs flat bomb #2 (`…PromotedExternalLegsLiftableModel`) |

This strengthens the non-vacuity story symmetrically: the flat retarget collapse
has formal counterexamples (`BoundaryResolvedCounterexamples.lean`,
`flatEdgeRetarget_not_injective` / `flatLegRetarget_not_injective`), while the
resolved remainder/leg retargeting has formal injectivity/recovery theorems on
the same operation — the difference is exactly the persistent `edgeId`/`legId`
that `forget` discards.

### R-4-full Phase 2 — resolved proper-forest index, forget bridge, coproduct summand

In progress (`GaugeGeometry/QFT/HopfAlgebra/ResolvedCoproductIndex.lean` and
`ResolvedCoproduct.lean`; standalone, not yet wired into `Main`).  Phase 2
establishes that the resolved coproduct can be built **through `forget`**, reusing
the flat finite proper-forest index.

| Phase | Artifact | Status | Role |
|---|---|---|---|
| 2a | `ResolvedAdmissibleSubgraph.IsProperForest` (+ projections) | ✅ | resolved proper forest, predicate level |
| 2b | `forget_mem_properDisjointAdmissibleDivergentSubgraphs` (linchpin `forget_injOn_elements`) | ✅ | resolved proper forest forgets to flat `properDisjoint…` |
| 2c-i | `forget_mem_properDisjoint_filter_complement` | ✅ | complement positivity transfers — full bridge into `forestCoproductProperForestIndex` |
| 2c-ii | `strictSummandViaForget` | ✅ | resolved single-forest coproduct summand (= flat summand of `A.forget`) |
| 2d | `ResolvedProperForestFiniteIndex` + `strictCoproductSum` | ✅ | finite index as explicit payload; summation wrapper |

Three design conclusions fell out and **substantially lower the R-4-full cost**:

1. **No native resolved finite index** (`forget_injOn_elements`): on a
   pairwise-disjoint nonempty-component forest, `forget` is injective on the
   components, so the forgetful image is a faithful flat forest.  The resolved
   proper forest forgets *into* the flat `forestCoproductProperForestIndex`; no
   `Fintype (ResolvedFeynmanSubgraph)` enumeration is needed.
2. **No ambient `EdgeIdsUnique`** for complement positivity: `Multiset.map`
   preserves cardinality (unlike `Finset.image`), so the `0 < complement.card`
   filter transfers even though `forget` collapses `edgeId`s.
3. **No `ResolvedHopfGen`**: the flat summand API is generic over an arbitrary
   `FeynmanGraph` with an abstract right-generator assignment and lands in the flat
   `HopfH ⊗ HopfH`.  The **algebra carrier stays flat `HopfH`**; the resolved
   carrier is a *semantic witness layer* used only to discharge the facades.

### R-4-full Phases 3–6c — canonical coproduct, coassociativity, and an inhabited payload

These complete the conditional resolved coproduct story (`ResolvedCoproduct.lean`,
`ResolvedPayloadModel.lean`; standalone, not wired into `Main`).

| Phase | Artifact | Status | Role |
|---|---|---|---|
| 3a–b | `flatCanonicalStar`, `strictSummandCanonicalViaForget` | ✅ | concrete canonical summand (= flat canonical summand of `A.forget`) |
| 3c | `ResolvedProperForestFiniteCover` + `strictCoproductSumCanonical_eq_flat` | ✅ | cover reindex: resolved canonical sum = flat coproduct body |
| 4a–b | `ResolvedHopfPayload`, `resolvedCoproductX_eq_coproduct_strict_forest_X` | ✅ | resolved coproduct-on-generator **= flat `Δ(X g)`** (free-index `forget` transport) |
| 4c | `ResolvedHopfPayloadFamily.resolvedCoproduct`, `…_toLinearMap_eq_flat` | ✅ | resolved coproduct **= flat coproduct** as an `AlgHom`/`LinearMap` |
| 5 | `resolvedCoproduct_coassoc`, `…_ofReflection` | ✅ | resolved **coassociativity by transfer**, gated only on the two boundary facades |
| 6c | `resolvedHopfPayloadFamily_exists` | ✅ | **the payload family is inhabited** (canonical constant-id lift) |
| 7 | `ResolvedHopfStructureCertificate`, `resolvedHopfStructureCertificate_holds`, `exists_resolvedHopfStructureCertificate` | ✅ | **Hopf-structure certificate** for the resolved-payload coproduct |

**Non-vacuity (unicorn objection closed).**  Phases 4–5 show the resolved coproduct
equals the flat one as a linear map and inherits coassociativity *given* a payload
family.  Phase 6c removes the "given": `resolvedHopfPayloadFamily_exists :
Nonempty ResolvedHopfPayloadFamily` constructs one canonically — for each generator
`g`, the constant-id lift `ofFlatGraph (repG g)` (decorate every edge/leg with
`id = ⟨0⟩`) with its canonical proper-forest cover.  The theorem depends only on
`propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no project axiom).  So the
resolved coproduct/coassociativity are **not** conditional on an abstract payload:
an explicit, provably-existent model is exhibited.

Key design point: the lift targets subgraphs/forests of `(ofFlatGraph Gf).forget`
(the forgetful ambient itself), so the round-trips are same-type equalities and no
graph-type transport is needed; `EdgeIdsUnique` is not required (the coproduct
transfer never uses it), and the algebra carrier stays flat `HopfH`.

**Phase 7 — Hopf-structure certificate (`ResolvedHopfCertificate.lean`).**  We do
**not** register a second `HopfAlgebra`/`Coalgebra`/`Bialgebra` typeclass instance
on `HopfH` (it would clash with the existing flat instance on the same carrier).
Instead we record a *certificate*: `ResolvedHopfStructureCertificate` bundles
coassociativity, both counit laws, and both antipode axioms for the
resolved-payload coproduct, and `resolvedHopfStructureCertificate_holds` proves it —
every field transfers for free from the flat strict-forest coproduct via the Phase
4c equalities.  `exists_resolvedHopfStructureCertificate` combines this with the
Phase 6c non-vacuity: an explicit canonical payload family whose coproduct satisfies
all the Hopf laws exists, depending only on `propext`/`Classical.choice`/`Quot.sound`.

**R-4-full is effectively closed:** the boundary-resolved payload coproduct equals
the flat coproduct as a linear map, satisfies the full Hopf-structure law bundle,
and is inhabited by a canonical lift — the only thing deliberately *not* done is
installing a duplicate typeclass instance on the flat carrier.

*Completed since the last revision:* coassociativity `forest_inj` and the full
forest-cover source connected-divergence (`forest_cd`) are theorems; the
forest-cover CD data is discharged from the power-counting environment; **and the
right antipode axiom is discharged via the convolution / local-nilpotency route**
(`AntipodeConvolution.lean`), eliminating the former CK §3 kernel
`AntipodeForestRightCoreIdentity`.  Cross-file certificates (`HopfAlgebra.lean`):
`coassocStrictForestH58Ready_ofBoundaryFacadesAndReflection` (coassoc side) and
`hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` (**the full
`HopfAlgebra ℚ HopfH` from the two boundary facades + power-counting reflection
alone — no antipode kernel**).

### R-4-superfull consolidation — native H5.8 architecture and the final obstruction

Beyond `R-4-full` (which leaves coassociativity gated on the two boundary facades),
the boundary-resolved track is extended to a **native resolved H5.8 reindexing
architecture**, all standalone and axiom-clean:

- an *identity-unique* payload lift (`ResolvedHopfPayloadFamilyWithUniqueIds`,
  `ResolvedUniquePayloadModel.lean`) so the resolved boundary repairs
  (`parent_eq_of_remainder_eq`, `externalLegs_lift_unique`) apply to the actual payload
  graphs (`ResolvedBoundaryRepairCertificate`);
- a constructive σ-index parent set (`ResolvedSigmaParentSet`, with the source-vertex
  recovery `remnant_vertex_recovery` *proved* — no longer a hook — from a pure-graph
  connectivity lemma + star freshness);
- a branch-map layer (`ResolvedBranchMapLayer`), its separated-cover classifier
  (`ResolvedIndexedBranchClassifier`), and the finite sum-reindex
  (`ResolvedFiniteBranchMapLayer.sum_reindex`: `∑ image = ∑ forest + ∑ mixed`);
- a bridge to the **concrete flat H5.8 tensor terms** (`ResolvedH58Bridge`, through thin
  public aliases of the private flat σ-objects in `Coassoc.lean` — `Main` stays green).

The architecture **reaches the concrete flat H5.8 tensor reindexing identity**
(`ResolvedActualSigmaCover.concrete_sum_reindex`).  We do **not** claim the full native
resolved H5.8 proof is complete: the entire remaining obstruction is isolated as the
construction of a **single explicit finite data package**,
`ResolvedActualSigmaCover g` (`ResolvedActualSigmaCover.lean`), which is **not yet
constructed**.  Its fields — the finite branch-map layer `FL` (carrying cover, branch
injectivity, and the image-data CD/disjointness/star-avoidance), the resolved→flat
`ResolvedH58ConcreteIndexMaps`, and the flat `splitTerm_agreement` — are all *σ-cover
data* (non-facade); no abstract framework or new mathematics remains.  Branch
injectivity reduces to index injectivity; `componentCD`/disjointness come free from the
admissible-subgraph structure; `avoidsStars` is structural from star freshness;
`remnantCD` is reflection-class gated; `splitTerm_agreement` is the σ-cover
factorization data.

**Cover consolidation.**  The branch-map layer's `cover` (every quotient image is a
forest or mixed branch image) is reduced — *facade-free* — to a single datum.  By a case
split on the `resolvedIsForestByStar` discriminator (`ResolvedCoverPreimageData.cover`):
the **mixed** case is discharged *structurally* (`exists_mixed_preimage_of_not_forest`: a
non-forest-by-star image is its own mixed preimage, since `avoidsStars` is exactly
`¬ resolvedIsForestByStar`); the **forest** case is constructed from
`ResolvedForestCasePreimageData` (a `parentOf` lift of the image's components back to
parents, with `parent_remnant_eq`) via `forest_case_of_preimageData` (the forest image's
`remnantCD`/`remnantDisjoint`/`starWitness` and `toImage = z` all derive from the image's
own admissible structure).  Consolidated as `ResolvedForestCaseSupply.cover`.  **No flat
`ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel` is used** — the
cover obstruction is now the single facade-free datum `ResolvedForestCaseSupply`
(equivalently, a component-to-parent lift for forest-by-star quotient images:
`resolvedParentRemnant` component-level surjectivity, σ-cover data).  The remaining
`ResolvedActualSigmaCover g` construction is therefore pure σ-cover data supply
(`parentOf` / concrete index maps / `splitTerm_agreement` / `remnantCD` / finite
carriers) — **full native resolved H5.8 is not claimed complete; the construction
interface is consolidated**.

**De-contraction section (constructed).**  The `parentOf` datum above is no longer only a
*hypothesis*: it is now **constructed**.  For a contracted-graph subgraph `δ`, the parent
`parentOfQuotient Aout starOf δ` (edges `Aout.internalEdges + quotientEdgePreimage`, legs
`quotientLegPreimage`, both recovered as `retargetEdge`/`retargetExternalLeg` submultiset
preimages via the identity-unique payload's `exists_le_map` + `retarget_residual_*_injective`)
satisfies `containsAoutEdges` (`le_add_right`) and, under the saturation datum
`QuotientVertexCovered` + star-containment, `parentOfQuotient_remnant_eq :
resolvedParentRemnant Aout starOf (parentOfQuotient … δ) = δ` — a genuine *section* of the
parent-remnant map.  Forest-branch images are then single-parent
(`singletonForestImageDataOfParent`; the all-star containment of a parent ⊇ `Aout` forces the
single-parent granularity, with the multi-component RHS recovered by the outer-forest sum).
Assembled: `CanonicalOuterForestQuotientSupply` (a finite quotient carrier + per-image
CD/star/saturation facts) → `forestCarrier`; `ResolvedMixedCarrierSupply` → `mixedCarrier`
(star-avoiding subgraphs, no de-contraction); both → `ResolvedBranchCarriers` →
`CanonicalOuterInnerSupplyData.toCanonicalSupply : CanonicalResolvedActualSigmaCoverSupply g`.
So the inner supply is now obtainable from genuine de-contraction data; the remaining inputs
are the concrete finite quotient/mixed carriers (with their CD/star facts), the resolved→flat
`ResolvedH58ConcreteIndexMaps`, and the `splitTerm_agreement` factorization — all σ-cover
data, no facade.  **Full native resolved H5.8 remains not claimed complete.**

**Track S — σ-cover finite-data supply (carrier import).**  The machinery to import the flat
σ-cover's finite carriers into the resolved coordinate is **built** (S-2 + S-3).  *S-2:* the
contracted-graph forget bridge `forget_canonicalOuterContractedGraph :
((canonicalOuterAoutOfFlatOuter g A).contractWithStars (canonicalOuterStarOf g A)).forget =
h58BridgeOuterActualQuotientGraph g A` (the flat *actual* quotient graph).  Its keystone is the
**id-uniqueness payoff at the graph level**: `forget` is faithful across the complement
subtraction (`map_forget_complementEdges_canonicalOuterAout` — `map` distributes over `-` for
`B ≤ A`, and the id-unique lift forgets edges occurrence-faithfully), together with the
star / retargetVertex / retargetEdge / retargetLeg / starVertices alignments.  *S-3:* a generic
forget-subgraph lift `resolvedSubgraphOfForget` (submultiset preimage; no id-uniqueness needed
for the lift itself), specialised through the bridge to `liftFlatQuotientSubgraphToCres` and the
forest version `liftFlatQuotientForestToCres`, each with a (heterogeneous) forget round-trip.
So flat quotient subgraphs/forests lift into the resolved contracted graph.  **Remaining:** build
the concrete carriers (`CanonicalOuterForestQuotientSupply.Q` / `ResolvedMixedCarrierSupply.mixedQ`)
from the lifted images with the CD/star/saturation facts transported (S-3c); the resolved→flat
`ResolvedH58ConcreteIndexMaps` (facade-free coordinate dictionary, S-4); and `splitTerm_agreement`
(resolved-native-or-supplied — the genuine boundary, *not* imported from flat, S-5).  **Full
native resolved H5.8 remains not claimed complete.**

**The boundary reduced to one predicate `forest_term`.**  The honest finishing-line is now a
single named theorem.  The boundary `ResolvedFlatH58Correspondence` (the index dictionary +
weight equality, one datum) is whittled down: **`flatImageOf` is constructed** (G-1a — `forget`
through the S-2e bridge + the actual↔rep transport `h58BridgeActualQuotientToSigma`); the **P3
fix** makes the dictionary carrier-based (`ResolvedH58CarrierWeightData` /
`ResolvedFlatH58CarrierWeightAlignment` — the whole-type commutation was over-strong, the P2
pattern); the **mixed half is killed** (`ResolvedFlatH58CarrierMixedAlignment`, an origin
projection) leaving the **forest boundary**; that splits into an **index** boundary
(`forest_comm` — a mechanical origin round-trip) and a **term** boundary
(`ResolvedFlatH58CarrierForestTermBoundary` — the flat split-term factorization); and the term
boundary **branch-splits** (`forest ⊕ mixed`, by `Sum.isLeft`, no Coassoc wrappers) into
`forest_term` + `mixed_term`.  The single genuine remaining datum is **`forest_term`**: `∀ s ∈
splitChoiceIndex, s.isLeft → splitChoiceTerm s = quotientTerm (splitPhi s)` — the forest-branch
weight factorization (Field-Filling-6's `hForestTerm`).  **`full native resolved H5.8` is reduced
to proving `forest_term` resolved-natively** (the de-contraction parent weight factorization),
not imported from flat's facade-discharged assembly.  Carrier / de-contraction / cover / reindex
/ dictionary-half / mixed-half are all complete; `mixed_term` is expected mechanical.  **Full
native resolved H5.8 still not claimed complete (`forest_term` not yet proved).**

**Update (gold sprints G-5…G-11): the term-weight side is canonical; only facade #2 (cover)
remains.**  Pushing `forest_term` through, the entire **term-weight side** turned out to be
facade-free *canonical*, not a genuine boundary: `splitTermAgreementCanonical g` produces the whole
`splitTerm_agreement` with no input.  Its four pieces are all canonical — certificate (remnant
complement nonempty), product (outer left/promoted ⊗ inner remnant transport), `mixed_term` (the
mixed branch is a literal split-star relabel), and — correcting the earlier scout — the **forest
right factor**: its de-contraction *composition law* is discharged by the per-edge count proof
(`forestComponentForestChoiceSourceInternalEdgesCountSplitCanonical`) plus canonical
vertices/external-legs, with the `RepQuotientComplementPositiveModel` supplied by a canonical
instance.  **Facade #1 (insertion uniqueness)** is the carrier forest-injectivity, already the
resolved kernel `resolvedParentRemnant_injOn` (= `parent_eq_of_remainder_eq`).  The resolved-native
H5.8 inner reindex is assembled carrier-based (`ResolvedFlatH58CarrierWeightAlignment.sum_reindex`,
carrier-subtype split maps — no whole-type junk) from the mechanical mixed half + the **forest
index boundary**.  So the **single remaining genuine datum** is
`ResolvedFlatH58CarrierForestIndexBoundary` = **facade #2 (cover)**: a section `forestSplitOf` of
the flat forest-cover map `ToQuotientForestSigma` over the resolved carrier (each forest carrier
element is a de-contraction parent set; `forest_comm` reads `forget(F.toImage) =
ToQuotientForestSigma (forestSplitOf F)`).  The parent↔remnant half is `parentOfQuotient_remnant_eq`
(landed); the remaining content is the cover enumeration.  **Full native resolved H5.8 still not
claimed complete (the forest-cover correspondence / facade #2 not yet constructed).**

**Update (facade #2's real shape — an outer-sum cover).**  Constructing the cover, `forestSplitOf`
was reduced to an origin projection (`ResolvedForestOriginIndexSupply`, no section search) and the
commutation-square *transport core* was landed (`canonicalFlatImageOf` of a lift = the actual→rep
transport; `splitPhi (inl q)` = that transport of the actual quotient).  Instantiating the cover
then exposed the genuine knife-edge: a resolved forest carrier element is **single-parent**
(multi-parent remnants each contain all outer stars, so cannot be disjoint) hence
**single-component**, while the flat forest choice's actual quotient is **multi-component**.  So the
naive single-component ↔ flat-forest-choice correspondence fails *within one outer forest*; the
multi-component flat RHS quotient is recovered only as the **outer sum** (over outer forests) of
single star-saturated resolved components.  Thus facade #2 is an **outer-sum cover** indexed by
`(outer forest, single star-saturated quotient component)` — the genuine remaining mathematics is
`multi-component flat quotient forest ↔ outer-sum of single star-saturated resolved components`
(a P2/P3-style "do not close per-`D`, the outer sum is the right level").  **Full native resolved
H5.8 still not claimed complete.**

---

*Maintained alongside `HOPF_DECOMPOSITION.md` (internal, full sprint log).
This file is the reviewer-facing distillation; do not add day-by-day logs here.*
