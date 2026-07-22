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

### Facade dependency audit — what (if anything) still gates `HopfAlgebra ℚ HopfH`

A full audit of every use of the two boundary facades down to the final instance
(`hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution`,
`QFT/HopfAlgebra/HopfAlgebra.lean`) settles "what remains":

```
HopfAlgebra ℚ HopfH
  ├ [ForestGraphInsertionUniquenessModel]                         (facade #1)
  ├ [ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel]  (facade #2)
  └ [IsDivergenceReflectedByAdmissibleForestContract]   (NOT a facade — ambient power-counting)
       │
       ▼  both facades enter through ONE channel only
  CoassocStrictForestH58Ready_ofBoundaryFacades   (Coassoc.lean)
       │
       ▼
  Bialgebra coassoc field  := coassoc_strict_forest_linearMap     (antipode = convolution route, facade-free)
```

Every facade *consumption* site — facade #1's 14 forest-branch injectivity /
parent-remnant / split-`φ` sites, facade #2's `forestQuotientForestSigmaForestCover_*`
cover cluster, and the `resolvedCoproduct_coassoc_ofReflection` transfer — lies in
the **H5.8 coassociativity reindex** chain.  Classified:

- **A — H5.8-reindex content:** all facade consumption.  Has a facade-free
  resolved-carrier realization: `h58_resolved_carrier_double_sum_reindex`
  (axioms `[propext, Classical.choice, Quot.sound]`).
- **B — flat-only shadow:** the flat `coassoc_strict_forest_linearMap`,
  `forestComponentSplitPhiBranchReindexing`, and the flat `CoassocStrictForestH58Ready`
  typeclass — **cannot** be made facade-free (flat insertion uniqueness is *false*
  via `flatEdgeRetarget_not_injective`); the resolved theorems are their native
  replacements.
- **C — non-H5.8 genuine facade dependency: EMPTY.**  The antipode (convolution
  route) and counit/coalgebra structure use **no** facade; `CoassocStrictForestH58CoverData`
  is auto-derived from the power-counting reflection (non-facade); the gated
  `forestComponentSplitPhi_term_eq_of_split` is never called outside `Coassoc.lean`
  and never exposed.

**Conclusion.**  There is **no remaining unsolved mathematics** gating a facade-free
Hopf statement: the *only* facade consumer is the H5.8 reindex, whose facade-free
content already lives on the resolved carrier.  The old flat `HopfAlgebra ℚ HopfH`
instance stays facade-conditional **by the shape of its own statement** (its coassoc
field genuinely needs the flat-false facade), not by missing work.

### R-5 frontier — why a facade-free coassoc needs a different *carrier*, not a better proof

The natural next move — "state coassociativity on the resolved coproduct" — does **not**
escape the facade, and the reason is sharp.  `resolvedCoproduct.toLinearMap =
coproduct_strict_forest.toLinearMap` (facade-free, Phase 4c), so the resolved coassoc
linear-map equality on `HopfH` *is literally* the flat coassoc.  The flat coassoc
reduces, facade-free, to the term-sum equality `∑ split-choice term = ∑ quotient term`
over the flat indices (both side-partitions are facade-free `Finset.sigma`/`disjSum`
over `h58BridgeOuterCarrier`, and the carriers align exactly).  The single irreducible
step is the **quotient side**: identifying the per-`A` resolved cover image carrier with
the flat per-`A` quotient index via `flatImageOf` — which is exactly the flat
`forestComponentSplitPhi` bijection, i.e. the two facades.  The facade-free resolved
reindex sums over the *resolved* image carriers; the moment the statement is read on the
flat `HopfH` quotient index, the bijection (hence the facade) is re-demanded.

This boundary is pinned as a theorem,
`h58_resolved_carrier_coassoc_termSum_frontier`
(`ResolvedActualSigmaCover.lean`; axioms `[propext, Classical.choice, Quot.sound]`): it
closes the flat term sum from the facade-free reindex **plus one explicit hypothesis**
`hQuotBij` — the flat-index bijection — making the facade content the sole remaining
input.  So:

> **Facade-free H5.8 reindex exists.  A facade-free `HopfH` coassociativity does *not*
> follow without changing the algebra carrier.**

`HopfH` is the flat carrier, so its coproduct's quotient index is flat, and the facade is
precisely what compensates the lost half-edge/leg ids in that coordinate.  A genuinely
facade-free Hopf/coassoc statement therefore requires moving the algebra carrier itself to
the resolved generators (a `ResolvedHopfGen`-style carrier where the quotient index is
resolved) — a separate, larger track (**R-6**) that the project has so far deliberately
de-scoped (`algebra carrier stays flat HopfH`).  R-5 fixes the boundary; R-6 would cross
it.

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

### R-6c heart — native resolved coassociativity, the term boundary fully decomposed

The decisive turn since the gold sprints: rather than importing the flat σ-cover term agreement, the
resolved coassociativity of `Δᵣ` is reconstructed **natively** on `ResolvedHopfH`.  The entire
coassociativity wiring is now closed to a single capstone `coassoc_gen` — produced from one bundled
`ResolvedCoassocFullCompatibilitySupply` — whose unfilled fields are *exactly* the genuine geometric
data.  The headline result of this stretch: **the whole "heart" (the term agreement `term_eq` and its
right factor `right_eq`) is reduced to a finite, named list of parametric supply obligations — with no
open-ended structural or algebraic gap remaining.**  All files axiom-clean
(`propext`/`Classical.choice`/`Quot.sound`); no facade, no flat term, no `forgetHopf`, no rep/perm.

**The heart equation.**  `term_eq : resolvedSplitChoiceTerm s = imageWeight (imageOf s)` is the
facade-free replacement of the *gated* flat `forestComponentSplitPhi_term_eq_of_split`.  A pure-tensor
anatomy (`term_eq_of_factorization`, **proved**) splits it into two genuine facts plus an `assoc_tmul`
assembly:

- **`product_eq`** — the branch product `∏ γ localChoiceTerm(choiceAt γ)` factors as
  `resolvedSelectedOuterTerm ⊗ resolvedForestLeftTerm(quotientForest)`;
- **`right_eq`** — `(D.supply G).rightTerm s.1 = innerRightTerm (imageOf s)` (the outer forest's quotient
  generator equals the inner quotient-of-quotient generator).

**De-contraction objects, made concrete (the R-6 payoff).**  The selected-outer and quotient forests are
no longer abstract supplies but `Right ⊔ Remnant`-style constructions from the per-component local
choices (`isLeftPrimitive`/`isRightPrimitive`/`isForestChoice` partition of the input outer components):
`selectedOuterRaw = leftOf ∪ promotedOf`, `fullQuotientOf = remnantForest ⊔ rightSurvivorForest`
(`ResolvedConcreteFullQuotientSupply.toFullQuotientSupply`).  The flat rep/perm transport layer
**vanishes**: because ids are kept, a forest choice already lives in component coordinates, so promote is
pure inclusion and `resolvedComponentGen (γ.promote δ) = resolvedComponentGen δ` holds **by `rfl`**.

**`product_eq` — conditionally complete.**  Pure algebra (`splitChoiceProduct_eq_factor_tmul` via
`resolvedTensorProduct_prod_tmul`) reduces it to two factor equalities, each proved by a component-
partition split:

- *left factor* `leftFactorProduct = resolvedForestLeftTerm(selectedOuterRaw)` — the engine is
  `resolvedForestLeftTerm_union` (the forest-generator product splits over a disjoint union) plus the
  promote-generator equality; the right region drops out (`= 1`), left = `leftOf` term, forest =
  `promotedOf` term (`leftFactorProduct_eq_selectedOuterRawTerm`);
- *right factor* `rightFactorProduct = resolvedForestLeftTerm(remnant ⊔ rightSurvivor)` — the symmetric
  split, with the right-survivor / remnant regions identified with the quotient forest via the embedding
  generator equalities (`rightSurvivor_region_eq`, `remnant_region_eq`).

Assembled in `product_eq_of_region_data`, conditional only on parametric supply hypotheses
(forest/union disjointness, the survivor/remnant generator equalities + injectivities, and two
abstract-image connectors).

**`right_eq` — reduced to one class equality, then three graph fields.**  Both sides are
`X (graph.toResolvedHopfGen _)`, so (`right_eq_of_contract_class_eq`, term-mode `congrArg X ∘ Subtype.ext`)
`right_eq` reduces to the **contract-twice = contract-once** class equality
`(A.contractWithStars).toResolvedClass = ((A'.contractWithStars).contractWithStars).toResolvedClass`.
A resolved class equality is an id-preserving iso, so this reduces in turn to a **star permutation `σ`**
matching the one-step and two-step contractions, plus three graph-field equalities
(`ResolvedContractTwiceOnceGeometrySupply`).  The field equalities are driven by the **retarget
composition** `A.retargetVertex = σ ∘ (B'.retarget ∘ A'.retarget)` (a supply at the vertex level; the
edge/leg lifts are *free*, since resolved edges/legs are endpoint retargets preserving id/sector):
`externalLegs_eq` is **fully proved** (legs are never removed, so both contractions retarget all of
`G.externalLegs`); `internalEdges_eq` follows from a single complement-edge domain correspondence; only
`vertices_eq` (the star-vertex sets) and the vertex retarget composition stay as the final
star-geometry fields.

**Survivor embedding — concrete.**  A right-survivor component (`choiceAt = inl false`) is disjoint from
the selected outer, so it survives the contraction untouched: `ResolvedFeynmanSubgraph.reembed`
re-interprets its data in the quotient graph with the **same intrinsic graph and the same generator**
(`resolvedComponentGen_reembed := rfl`), and `survivorReembed` discharges the three support facts from
disjointness + an edge-domain bound.  (The remnant embedding — a genuine `localizeRemnantComponent`
de-contraction — stays a supply for now.)

**Net position.**  `term_eq = product_eq + right_eq` is now a finite list of named **parametric supply**
obligations: the survivor/remnant embeddings (and their generator equalities/injectivities), the
star-geometry triple (`retargetVertex_eq` / `internalEdges_domain` / `vertices_eq`), and the
nonemptiness/carrier-properness data (forest/union disjointness).  These are concrete-construction and
discharge tasks — heavy, but **no longer open-ended**.  The downstream wiring (`term_eq` field →
heart-6 finite cover/inj + the two regroup agreements + the `∀ x` lift → `coassoc_gen` →
`HopfAlgebra ℚ HopfH`) is already in place.  **Full unconditional resolved coassociativity still not
claimed complete (the parametric supply obligations not yet all discharged).**

### R-6c reduction campaign — leaf/body supply isolation (in progress, 2026-07-03)

The heart's "finite list of named supply obligations" above is being discharged by a systematic
**one-file-per-task** campaign (each file axiom-clean `[propext, Classical.choice, Quot.sound]`; no facade,
no flat term, no `forgetHopf`, no rep/perm).  Two phases:

- **Leaves 1–38** — structural / connector reductions (bundling, adapters, transport-`rfl` lemmas,
  id-bearing `ext` adapters).  These carry no genuine geometry; they wire the supply records so every
  downstream obligation is a single named field flowing `FinalLeafInventory → GrandFull →
  GlobalCoverSupply → (∀x) FullCompatibilitySupply → coassoc_gen`.
- **Bodies 1–35** — the genuine geometry / measure content, each reduced to (or proved from) named
  irreducible supplies.  Highlights:

  - **Product / Sector / Codomain element shapes** (bodies 1–16) — the branch-weight combinatorics.  The
    Codomain forests are the *transported* Product forests, so the Sector element shapes and forest
    unions collapse to `elements_transport` / `elements_disjoint_transport` (`subst h; rfl`) plus the
    Product forest elements (existing `@[simp]` `rfl` lemmas).  Sector surjectivity/injectivity reduce to
    the shared de-contraction kernel `occurrence_inj`.
  - **De-contraction uniqueness kernel** (bodies 7, 19–26) — the biggest thread.  `occurrence_inj`
    (powers Product `remnantInj` + Sector `forest_forward_injective`) → `parent_inj` (parent component
    recovery) → `parent_graph_inj` (intrinsic-graph recovery, via `ResolvedFeynmanSubgraph.ext`).  A
    scout (body-20) established `contractWithStars` is **lossy** (discards `B.vertices` / `B.internalEdges`,
    collapses complement endpoints to stars) so the raw graph does *not* recover the parent — but the
    id-bearing legs/edges are **preserved** by `retarget` ("shape is lost, ids remain", body-21).  A
    second scout (body-23) found leg-ids alone insufficient (leg-empty components) and re-scoped to the
    **vertex** key.  Body-24 then **proves** `vertices_determine_parent` by a surviving-vs-star vertex
    chase, and body-25 **proves** `parent_disjoint` from the proper-forest `pairwiseDisjoint`.  Net: the
    entire kernel reduces to a compact **star-traceability** supply (`ResolvedStarGlobalGapSupply` —
    inter-component star freshness + cross-parent traceability + contracted-nonempty), which body-26
    shows is *strictly stronger* than the codebase's component-local `ResolvedCanonicalStarFacts` and is
    the honest minimal star hypothesis for a parametric `D`.
  - **Finset-subtype permutation** (body-18) — the one nonlocal but purely combinatorial leaf
    (`FinsetSubtypePermExtensionSupply`, extend a subtype bijection to a global `Equiv.Perm`) is
    **constructed**, not fielded: `Equiv.extendSubtype` on the finite carrier `↥(s ∪ t)` lifted by the
    identity outside.
  - **Retarget three-route** (bodies 27–32) — `retarget_corr_on_vertices` (contract-twice = one-stage in
    correspondence coordinates) is split into survivingOriginal / inner-left / inner-right routes.  The
    outer route is **proved concrete** (body-28/29b) via the packaged `invFun` value lemmas (body-29);
    the two inner routes are proved through `threeRoute_invFun_leftStar_val` / `_star_val` modulo fielded
    star recoveries; all three bundle into one record (body-32).
  - **Measure leaves** (bodies 33–34) — `innerCD_forget` (doubly-contracted CD) reduces to the CK
    power-counting stability `contract_preserves_CD` plus the carrier CD `D.hCD` (ambient discharged by
    defeq).  Bundled with `cd_nonempty` into `ResolvedMeasureLeafSupply` — a compact 2-field
    *measure*-only record, cleanly separated from the geometry supplies.
  - **Quotient = full-quotient** (body-35) — `(imageOf s).quotientForest = fullQuotientOf.toImage =
    remnant ⊔ right` holds **by `rfl`** for the concrete image side (the sigma-cover `Aout`/`starOf` are
    definitionally the selected outer + star), discharging body-17's `quotientForest_union` residual.
  - **Support-9 / OUTPUT reindex** (bodies 36–57) — the `coassoc_gen` wiring and the outer-forest ↔
    splitPhi-cover double sum.  Bodies 36–39 fix the support-9 chain (`RepresentativeFamilySupply →
    RegroupAgreementSupply → RegroupReindexSupply`, all `rw`-thin) and **prove** the finite-cover cross
    disjointness (`grandFull_forest_image_ne_mixed_image`).  Bodies 40–49 discharge the retarget star
    recoveries into the coherence/traceability/sector-inverse split.  Bodies 50–57 then reduce the OUTPUT
    reindex itself.  A decisive scout (body-52) found `ResolvedHopfH ≠ HopfH` (not `rfl`): R-4-full's
    **concrete** flat reindex engines do NOT transport, but the reindex *patterns* re-prove resolved-natively
    — the **partition** engine (`grandFull_partition_reindex`, body-53, from the GrandFull cover + body-39
    cross) and the **fibration** engine (`resolved_outer_cover_fibration`, body-55, generic `AddCommMonoid`).
    Body-54 named the last obstruction as a resolved σ-cover skeleton (`ResolvedOuterCoverSigmaSupply`), and a
    unification scout (body-55) **decided** the image and branch reindexes share the fibration *form* but need
    **two different fiber maps** (one bijection is impossible — it would force `image summand A = branch
    summand A`, which is the coassoc content).  Body-56 **types** those two fiber maps as named supplies
    (`ResolvedOuterImageFiberSupply` via the quotient / coassoc-RIGHT decomposition,
    `ResolvedOuterBranchFiberSupply` via the coassoc-LEFT), each carrying only `forestFiber` / `mixedFiber` +
    two `maps_to` + one fiberwise agreement — the cover / disjoint work is absorbed inside the engine's
    `Finset.sum_fiberwise_of_maps_to`.  Body-57 fixes the final map: `resolved_output_reindex_of_fibers`
    re-exports the two fiber families through `toOuterCoverSigmaSupply` → body-38's `RegroupReindexSupply` →
    `coassoc_gen`.  **Net: the entire OUTPUT reindex is proved except the two fiber-construction supplies.**

**Net position (R-6c campaign).**  The heart obligations now split into a small, honest set of *named
irreducible* supplies: the **measure** pair (`cd_nonempty` + `contract_preserves_CD`), the **star**
kernel (`ResolvedStarGlobalGapSupply` for parent recovery; the fresh/traceable star assumption), the
**retarget** star recoveries (left/right one-stage-star recovery + inner applicability), the **support-9**
representative lift, and — for the OUTPUT double sum — the **two fiber-construction supplies**
(`ResolvedOuterImageFiberSupply` / `ResolvedOuterBranchFiberSupply`), the resolved-native H5.8 outer × inner
coverage geometry.  Everything else — the support-9 wiring, the finite-cover partition, the σ-cover fibration
form, and all structural / transport-shaped steps — is `rfl` or proved.  Every remaining field is a
recognized geometry/measure assumption, not an open-ended gap.  **Full unconditional resolved coassociativity
still not claimed complete.**

### R-6c bodies 88–136 — the inner term/index double sum folded into two bundles (2026-07-04)

The OUTPUT reindex (bodies 52–57) handles the *outer-forest* double sum; the remaining content is the per-`A`
**inner** term/index bijection `∑_p splitChoiceTerm ⟨A,p⟩ = ∑_B leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)`.  Bodies
88–136 reduce it (one axiom-clean file each) to a **two-bundle assembly** that reaches `coassoc_gen` directly —
one bundle for the per-term *product agreement*, one for the index *bijection*.

- **PRODUCT side — the four factor products (bodies 92–129), all closed to base supplies.**  Each split term
  factors as `splitTerm = (∏ localLeftFactor) ⊗ ((∏ localRightFactor) ⊗ rightTerm)`, and the summand agreement
  `resolvedSplitChoiceTerm = leftTerm(selectedOuterOf) ⊗ (leftTerm B ⊗ rightTerm B)` reduces to three identities
  (left factor, right factor, contract-twice `quot_eq`) assembled by `Sigma`-free `rw` (bodies 100/108/109/111/127).
  The **four** factor products are all closed: `left_primitive` (body-119, unconditional), `promoted` (body-122,
  from the nonemptiness `hPD`), `right_primitive` (bodies 120+125) and `remnant` (bodies 123+126) — the last two
  discharged against the **existing** `rightSurvivor_region_eq` / `remnant_region_eq` (`RightFactorGen`), reducing
  each to the honest survivor/remnant `Inj` + `Gen` reembed facts.  A **forward-map coherence** step (body-128)
  makes the concrete `resolvedConcreteSelectedOuterImageSupply`'s ambient contract graph *definitionally* equal to
  `q.selectedOuterContractGraph`, so the transport forests slot into the summand bundle with **no cast**.  Body-129
  bundles the whole product side into `ResolvedConcreteSummandBundleSupply` = forward coherence + measure leaf +
  survivor + remnant + fielded quotient data; its `.summand_agree` streams the proved left-factor / disjointness
  lemmas by *defeq*.
- **BIJECTION side — fully skeletonized (bodies 130–136).**  Body-130 folds the summand bundle plus the index/cover
  bijection into body-113's assembly supply → `coassoc_gen`, so the *entire* `Δᵣ`-coassociativity flows from two
  bundles.  Body-131 pulls the bijection's nine fields (`invConstruct` + 8 membership/inverse laws) into their own
  provider and classifies each against the existing sector backward machinery (`componentToRight` / `componentToForest`
  + the `SectorLeafBundle` round-trips).  Bodies 132–133 prove the four *membership* fields are pure `Finset.sigma`
  plumbing over the codomain/domain carriers, reducing them to the star-touch classifier (`resolvedIsForestImage`)
  and the choice `p`-tag.  Body-134 gives `invConstruct` a **structured** form `⟨recoverOuter, recoverChoice⟩` (no
  longer opaque), body-135 grounds it into three tagged regions (left residual / survivor via `componentToRight` /
  remnant via `componentToForest`), and body-136 proves the four inverse laws are `Sigma.ext` adapters — an outer
  forest equality plus a heterogeneous second-component round-trip, decomposable region-wise against the four sector
  laws.

**Net (bodies 88–136).**  `Δᵣ`-coassociativity now rests on exactly two things: (1) the concrete
`recoverOuter`/`recoverChoice` **backward reconstruction** — the resolved port of the flat
`forestComponentSplitPhiInverseConstruction`, whose per-`s` sector-map `s`-dependence is the last genuine
combinatorial obstruction — together with its two outer round-trip equalities, two heterogeneous round-trips and the
four fielded star/tag facts; and (2) the **non-bijection providers** — the contract-twice geometry (bodies 27–49),
the survivor/remnant `Inj`/`Gen` reembed facts, the measure leaf, and the base (`carrier_isProperForest`,
`selectedOuter_mem`, representative lift).  All wiring, decomposition, membership plumbing and inverse-law splitting
are complete and axiom-clean; only concrete geometry/reconstruction provider proofs remain.  **Full unconditional
resolved coassociativity still not claimed complete.**

### R-6c bodies 137–148 — the backward map built, proof-shape complete (2026-07-05)

Bodies 137–148 close the *proof-shape* phase.  The backward reconstruction is built branch-by-branch down to
region-local geometry, and the recurring base leaves are banked into single provider records.  What remains is a
finite, named list of local geometry / measure / kernel facts — no structural or proof-shape obligation is left
anywhere in the coassociativity proof.

- **The backward map is one map, built in two branches (bodies 138–147).**  A scout (body-138) found the decisive
  type identity `ResolvedCoassocSplitChoice = ForestBlockDomType` (definitionally), so the whole inverse is a single
  `witnessSplit : (A,B) ↦ (A',p)` — the source split choice `s` is the *output*, not something reconstructed
  per-component (the apparent per-`s` obstruction dissolves).  This mirrors the flat backward map exactly: one `inv`
  built from a branch-decision cover.  Body-141 gave `witnessSplit` its concrete branch shape
  `if resolvedIsForestImage A B then forestPreimage else mixedPreimage` and **proved** the two whole round-trips from
  four branch-local specs (`apply_dite` + `split_ifs`).  The **mixed** branch (body-142, `B` avoids the star) is the
  primitive-only relabelling — its `¬ isForestCarryingChoice` tag is proved from the all-`inl` witness; the
  **forest** branch (body-143, `B` touches the star) is the de-contraction reassembly — its `isForestCarrying` tag
  is proved from the `∃`-`inr` witness.  Body-144 combines the two branches into the full backward map.  Finally the
  recovered outer forest is realised as a **three-region union** `A' = leftResidual(A) ∪ rightRecovered(B) ∪
  forestRecovered(B)` (body-145), from which the branch `p`-tags (body-146, via `Finset.ext_iff` on the union) and
  the four forward/backward specs (body-147, via `Sigma.ext` on two `Sigma`-level round-trips) are **proved**.  So
  the entire index/cover bijection now flows from one region-round-trip supply whose residual is purely region
  geometry.
- **The base providers are banked (bodies 137/140/148).**  `carrier_isProperForest` (body-137, a field for abstract
  `D`, a theorem `ofFlatForest_isProperForest` for the canonical carrier), the contract-twice geometry (body-140,
  bundling the bodies-27–49 vertex/edge/retarget layer whose `vertices_eq` is the three-route star correspondence),
  and the four survivor/remnant `Inj`/`Gen` leaves (body-148, bundling bodies 125/126; the injectivities rest on the
  shared star kernel via `occurrence_inj`) are each pinned to one provider record, alongside the measure leaf
  (body-124).

**Net (bodies 88–148).**  The coassociativity proof is now *entirely* reduced to a short list of named local
geometry / measure / kernel providers, with all scaffolding in place and axiom-clean:

* **region geometry** — the outer union (`leftResidual` / `rightRecovered` = `componentToRight` / `forestRecovered`
  = `componentToForest` / `unionOuter` / `union_eq`), the three region tags with `forestRecovered` empty (mixed) /
  nonempty (forest), and the two `Sigma`-level round-trips (`forward_outer` / `forward_quotient` / `backward_outer` /
  `backward_choice`);
* **star facts** (`mixed_avoids_star` / `forest_touches_star`) and `forestChoiceCarrier` membership;
* **contract geometry** (`vertices_eq`, the three-route star correspondence);
* **measure** (`cd_nonempty` + `contract_preserves_CD`);
* **star / global-gap kernel** (`ResolvedStarGlobalGapSupply`, powering the survivor / remnant injectivities);
* **base** — `carrier_isProperForest`, the representative lift, and `selectedOuter_mem`.

The σ-cover common-cover route (bodies 36–87) is the *other* formulation and stays separate (its `cover_on` /
`inj_on` are not reused for the outer-mixing route); the `boundary_tail_eq` induction (body-89) is superfluous once
the nested-forest bijection is direct.  **Full unconditional resolved coassociativity still not claimed complete** —
but every remaining obligation is a recognised local geometry / measure fact, not proof-shape.

### R-6c bodies 149–154 — the region geometry localised (2026-07-05)

Bodies 149–154 localise the backward map's remaining content onto the **three concrete regions** of the recovered
outer forest and four round-trip facts, and prove out the classifier / assembly layer.  After this pass the only
open obligations are the region contents themselves (built from the sector backward maps) and the four
`selectedOuterOf` / `quotientForest` region decompositions.

- **The recovered outer as a concrete union (body-153).**  The recovered outer forest is the literal
  admissible-forest union `A' = (leftResidual ∪ rightRecovered) ∪ forestRecovered`, and its elements decomposition
  `union_eq` is **proved** (`Finset.ext` + `union_elements`, absorbing a `Finset` `DecidableEq` instance diamond).
  The three regions are named by their sources: `rightRecovered` = the survivors of `B` pulled back by the sector
  `componentToRight`, `forestRecovered` = the remnants of `B` pulled back by `componentToForest`, `leftResidual` =
  the components of `A` not represented by `B`.
- **The choice tagging made definitional (body-152).**  `recoverChoice` is the region-priority function
  `leftResidual ↦ inl true`, `rightRecovered ↦ inl false`, `forestRecovered ↦ inr Bᵧ`, so body-146's three region
  tags are **proved** from the definition (given the regions are mutually exclusive on each component).
- **The classifiers proved from the region data (bodies 150/151).**  The `toFun_mem` star facts reduce to
  "survivors avoid the star" + "the remnant is empty in the mixed case" (mixed, proved via the summand bundle's
  `union_eq`) and a touching remnant (forest).  The `invFun_mem` `p`-tags reduce to `forestChoiceCarrier`
  membership = `piCarrier` membership (**always** true, since every choice value is a valid local choice) plus
  non-extremality; the forest side is proved outright from the `inr` witness, the mixed side reduces to the
  primitive-mixture nontriviality.  So all four membership fields of the bijection provider are now local classifier
  facts.
- **The round-trips named as region facts (body-154).**  The two `Sigma`-level round-trips are isolated into four
  named obligations — A-reconstruction (`forward_outer`), B-reconstruction (`forward_quotient`), A'-recovery
  (`backward_outer`), p-recovery (`backward_choice`) — each local to the three regions.

**Net (bodies 88–154).**  The entire proof-shape of `Δᵣ`-coassociativity is complete and axiom-clean, and the
backward map is localised onto three concrete regions.  The residual is: the **region construction** (the three
region forests from the sector maps + the "not represented" filter, their cross-disjointnesses and carrier
membership), the **four round-trip decompositions** (`selectedOuterOf` / `quotientForest` restricted to the
regions), the **region classifiers** (survivors-avoid-star / remnant-touches-star / mixed non-extremality /
`forestTag` / region exclusivities), and the non-region base (contract `vertices_eq`, measure, star/global-gap
kernel, survivor/remnant Inj/Gen, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).  **Full unconditional
resolved coassociativity still not claimed complete** — the next front is the region contents proper.

### R-6c bodies 155–160 — the region contents built (2026-07-05)

Bodies 155–160 build the three regions concretely and reduce the union assembly and the outer round-trips to their
element-level content.  After this pass every region has an explicit `Finset`-of-components shape, and the only
open region obligations are the two element partitions, the two heterogeneous quotient / choice round-trips, the
pairwise disjointnesses, and the carrier closure.

- **The three regions, concrete (bodies 156/157).**  For `z = (A, B)` (with `B` split by the outer star into
  survivors and remnants), `rightRecovered` / `forestRecovered` are the `ofElements` images of the survivor /
  remnant components under the sector backward maps `componentToRight` / `componentToForest`, and `leftResidual`
  is the filter of `A`'s components by "not represented in `B`".  All three element shapes hold by `rfl`; this is
  the backward mirror of the forward survivor forest.
- **The union assembly reduced (bodies 158/159).**  The union's two cross-disjointnesses reduce to the three
  pairwise region disjointnesses, and its carrier membership is pinned to a single named leaf (`recovered_outer_mem`),
  parallel to `selectedOuter_mem` — a theorem for a canonical carrier, a genuine primitive for an abstract one.
- **The outer round-trips reduced to element equalities (body-160).**  The two `{A // A ∈ carrier}` round-trips
  (`forward_outer` / `backward_outer`) are proved from the element partitions `selectedOuterOf(recovered) = A` and
  `unionOuter(forward) = A'` (`Subtype.ext` + `ResolvedAdmissibleSubgraph.ext_elements`); the two heterogeneous
  quotient / choice round-trips (`forward_quotient` / `backward_choice`) are kept as fielded `HEq`.

**Net (bodies 88–160).**  The region construction is fully localised.  The residual is: the two **element
partitions** (`selectedOuterOf(recovered) = A`, `unionOuter(forward) = A'`), the two **heterogeneous round-trips**
(quotient / choice, each needing the sector round-trip), the **pairwise disjointnesses** and **carrier closure**,
the **sector maps** (`componentToRight` / `componentToForest` + their well-formedness) and `representedInQuotient`,
the **region classifiers**, and the non-region base.  **Full unconditional resolved coassociativity still not
claimed complete** — the next front is the element partition proofs and the sector round-trips.

### R-6c bodies 161–165 — the four round-trips localised (2026-07-05)

Bodies 161–165 close the round-trip proof-shape.  Each of the four round-trip obligations is reduced to a single
region partition or region-`HEq` leaf, so no round-trip is opaque any more.  The two OUTER round-trips are proved
from element partitions; the two heterogeneous ones (quotient / choice) are pinned as named region leaves.

- **Forward outer (A-reconstruction, body-162).**  `selectedOuterOf(recovered).elements = A.elements` reduces,
  via the structural `selectedOuterOf = leftOf ⊔ promotedOf` membership (proved by unfolding + `Finset.mem_union`),
  to the single partition `leftOf ∪ promotedOf = A` — the left-selected components plus the promoted forests are `A`.
- **Backward outer (A'-recovery, body-163).**  `unionOuter(forward).elements = A'.elements` reduces, via the union's
  `union_eq`, to the region partition `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` — the three regions of
  the forward image reconstruct the original outer.
- **Backward choice / forward quotient (bodies 164/165).**  The two heterogeneous round-trips are pinned as named
  region-`HEq` leaves: `recoverChoice(forward) = q.2` (the region tags read back recover the original choice) and
  `quotientForest(recovered) = B` (the survivor / remnant regions reconstruct `B`).

**Net (bodies 88–165).**  The entire round-trip proof-shape is closed.  The residual is now a short list of local
region / sector / base facts: the two **region partitions** (`leftOf ∪ promotedOf = A`, `leftResidual ∪
rightRecovered ∪ forestRecovered = A'`), the two **`HEq` transports** (choice / quotient), the **pairwise
disjointnesses** and **carrier closure**, the **sector maps** (`componentToRight` / `componentToForest`) with
`representedInQuotient`, the **region classifiers**, and the non-region base.  **Full unconditional resolved
coassociativity still not claimed complete** — the next front is splitting the region partitions into region-local
sector facts.

### R-6c bodies 166–168 — the outer partitions split into region facts (2026-07-05)

Bodies 166–168 split the two outer round-trip partitions into region-local facts, so both outer partitions are now
in region vocabulary.  The forward-outer partition `leftOf ∪ promotedOf = A` (body-162) reduces to `leftOf =
leftResidual`, `promotedOf = forestRecovered`, and `leftResidual ∪ forestRecovered = A` (body-167) — the
right-primitive region does not contribute to the outer, since it went into the quotient.  The backward-outer
partition `leftResidual ∪ rightRecovered ∪ forestRecovered = A'` (body-163) reduces to the component membership
partition — the three recovered regions of the forward image classify the original outer's components by their
choice tags (body-168).  Both are proved by `Finset.ext` at the membership level.

**Net (bodies 88–168).**  The two outer partitions are region-local; the residual is: the region equalities
(`leftOf = leftResidual`, `promotedOf = forestRecovered`, the target partition, and the recovered-region
membership), the two `HEq` transports, the **sector bridge** (`rightRecovered` / `forestRecovered` = the
`componentToRight` / `componentToForest` images, `representedInQuotient`, and the sector round-trips linking regions
to the choice tags), the pairwise disjointnesses and carrier closure, the region classifiers, and the non-region
base.  **Full unconditional resolved coassociativity still not claimed complete** — the next front is the sector
bridge (starting with the survivor / right side).

### R-6c bodies 169–175 — the sector bridges close, backward trichotomy, forward asymmetry (2026-07-06)

Bodies 170–172 fielded the three **sector bridges** — each recovered region of a *forward image* is exactly a
choice-tag class of the source split choice `q`: `rightRecovered ↔ inl false`, `forestRecovered ↔ inr`,
`leftResidual ↔ inl true`.  Body-173 then closed the **backward-outer partition**: rewriting the three bridges into
the region disjunction turns `recovered_region_membership` into `choice_tag_trichotomy` — the pure statement that
every component of `q.1` carries exactly one tag, proved by `Sum` / `Bool` case analysis.  So the backward outer is
no longer fielded; it stands on the three sector bridges plus a proved trichotomy.

Bodies 174/175 opened the **forward-outer partition** and found its two halves are *different in kind*.  Body-174
**proved** `leftOf_recovered_eq` (`leftOf recovered = leftResidual`) from the region tags alone: `leftOf` is the
`filter` of the recovered outer by the `inl true` predicate, so it matches `leftResidual` by the same
`union_eq` case-split + tag-contradiction pattern used for `all_inl` / `exists_inr` — no new geometry.  But
`promotedOf_recovered_eq` does **not** follow from tags: `promotedOf` is the **de-contracted** promoted forest
(the `biUnion` of `promote γ Bᵧ`), while `forestRecovered` is the forest-choice **parents** (`componentToForest`
images) — their equality is a promotion / de-contraction sector round-trip.  Body-175 isolates that as its own
named geometry leaf `promoted_region_eq`, so the forward-outer residual is now, structurally, **one tag fact
(proved) + one de-contraction round-trip + one coverage partition**.

> **The key distinction (bodies 174/175).**  `leftOf` is tag-level; `promotedOf` is geometry-level.
> `promotedOf.elements` is the promoted / de-contracted components, whereas `forestRecovered.elements` is the
> `componentToForest` **parent** components.  Their equality is a sector promotion / de-contraction round-trip, not
> a tag lemma — the first place the resolved reconstruction forces a genuinely geometric (non-combinatorial) leaf
> on the forward side.

**Net (bodies 88–175).**  Backward outer: PROVED to `choice_tag_trichotomy` on the three sector bridges.  Forward
outer: `leftOf` PROVED from tags, leaving two named leaves — `promoted_region_eq` (de-contraction round-trip) and
`target_outer_partition` (coverage `leftResidual ∪ forestRecovered = A`).  Plus the two `HEq` transports, the
sector-bridge internals (`componentToRight` / `componentToForest` round-trips, `representedInQuotient`, `promote`),
the disjointnesses and carrier closure, the region classifiers, and the non-region base.  **Full unconditional
resolved coassociativity still not claimed complete** — the next front is `target_outer_partition`, which will
fully separate the promotion side from the coverage side.

### R-6c bodies 177–181 — the forward outer coverage assembled to its floor (2026-07-06)

Bodies 177–181 took the forward-outer partition down to its floor.  Body-177 recast the coverage half
(`target_outer_partition`) as a **represented-classification**: `A`'s components are the not-represented ones
(`leftResidual`) or the remnant parents (`forestRecovered`), never the bare survivors (which live in the quotient) —
which is exactly why the target is a two-region union.  Bodies 178–180 then discharged or isolated the three
classification facts, and body-181 assembled them:

* body-178 **proved** `leftResidual_mem` — `leftResidual` was defined as `A.filterElements (¬ representedInQuotient)`,
  so its membership is `Finset.mem_filter`, over a fielded wiring bridge to the abstract union region;
* body-179 bundled the **forest-recovery geometry** — `forestRecovered_mem` (coverage view) and `promoted_region_eq`
  (selected-outer view) are two faces of the same `componentToForest` de-contraction round-trip, so they share one
  provider;
* body-180 **proved** `coverage` from a one-directional `represented_cases` (a represented `A`-component is a
  forest/remnant parent) by excluded middle;
* body-181 wired 178 + 179 + 180 into body-177's coverage supply — predicates pinned to `representedInQuotient` and
  `representedByForest` — and ran it out `177 → 174 → 167 → 162`, closing the forward-outer chain.

> **Forward outer floor (bodies 174–181).**  The forward-outer partition is proved except for three genuinely
> geometric/fielded leaves: the **forest-recovery geometry** (`forestRecovered_mem` + `promoted_region_eq`, the
> `componentToForest` / `promote` de-contraction round-trip), the **star/remnant classifier** (`represented_cases`),
> and the **wiring bridge** (`leftResidual_eq`).  `leftOf`, `leftResidual_mem`, and `coverage` are all proved.

**Net (bodies 88–181).**  Both outer partitions are down to their floors.  Backward outer: the three sector bridges
+ a proved trichotomy.  Forward outer: the forest-recovery geometry + the star/remnant classifier + the wiring
bridge, with `leftOf` / `leftResidual_mem` / `coverage` proved.  Plus the two `HEq` transports, the disjointnesses
and carrier closure, the region classifiers, and the non-region base.  **Full unconditional resolved coassociativity
still not claimed complete** — the next front is the forest-recovery geometry (the `componentToForest` inverse /
promotion de-contraction), the genuinely geometric remaining leaf of the outer partition.

### R-6c bodies 183–186 — the forest-recovery deep leaf isolated (2026-07-06)

Bodies 183–186 open the forest-recovery box and drive it down to a single geometric obstruction, split into two
inclusions.  Body-183 split the box into three leaves (`forestRecovered_eq`, `parent_mem_carrier`,
`promoted_eq_forestRecovered`) and proved the glue.  Body-184 made `forestRecovered_eq` (and body-178's
`leftResidual_eq`) `rfl` by *building* the outer union from the concrete region constructions — closing the
abstract-union ↔ concrete-construction gap by construction.  Body-185 reduced `parent_mem_carrier` to a
componentwise membership (each `componentToForest` parent lands in `A`).  Body-186 audited and split the deep leaf.

> **The forest-recovery deep leaf (body-186).**  `(promotedOf recovered).elements = (forestRecovered z).elements`
> is *not* supplied by the sector inverse laws alone.  Sector inverse relates `componentToForest` to the
> quotient-side remnant components (`forestToComponent` / `remnantComponent`); it does **not** connect
> `componentToForest` with `promote` / de-contraction into `G`.  The remaining proof therefore requires concrete
> `componentToForest` / `forestTag` / `promote` compatibility — the genuinely fresh geometric fact.  It splits into
> `forestRecovered_subset_promoted` (light: a parent is a de-contracted component of its own promoted subforest) and
> `promoted_subset_forestRecovered` (heavy: every de-contracted component is a forest parent), with the equality
> proved by `Finset.Subset.antisymm`.

**Net (bodies 88–186).**  The forward-outer geometry is one leaf in two inclusions, gated on making
`componentToForest` / `promote` concrete; the forest membership (`forestComponentMem`) and the classifier
(`represented_cases`) sit beside it.  Backward outer: the three sector bridges + a proved trichotomy.  Plus the two
`HEq` transports, the disjointnesses and carrier closure, the region classifiers, and the non-region base.  **Full
unconditional resolved coassociativity still not claimed complete** — the next front is the `componentToForest`
concretization scout (how far it can be made concrete from `ForestPrimitiveIndex.toOccurrence` / `forest_surj` /
`Classical.choose`) before the inclusion proofs.

### R-6c bodies 188–190 — the forward outer geometry closed to compatibility leaves (2026-07-06)

Bodies 188–190 close the forward-outer partition to its irreducible geometry, verified in one chain to body-162.
Body-188 found the *semantic* content of the deep leaf: for a forest-tagged parent `γ`, the promoted contribution
`(promote γ Bᵧ).elements` is the de-contracted **sub-pieces** of `γ` (vertices `⊆ γ`), while `forestRecovered` is
the set of **parents** — so `promotedOf recovered = forestRecovered` holds iff each promoted subforest collapses to
its parent, `(promote γ Bᵧ).elements = {γ}` (the recovered forest tag is the whole component).  It named the
compatibility (`forestTag`, `recoverChoice_forest_eq`, `promote_collapse`) and proved the per-component collapse.
Body-189 then proved `promoted_region_eq` by a biUnion collapse (the `inl`-tagged left/right regions contribute `∅`,
each forest parent contributes `{γ}`).  Body-190 assembled the whole forward outer — the compatibility (188), the
componentwise membership (185), the star/remnant classifier (180), the region constructions, and the wiring bridges
— out to body-162's `ResolvedSelectedOuterPartitionSupply`.

> **Forward outer, closed (bodies 174–190).**  The forward-outer partition `leftOf ⊔ promotedOf = A` is proved
> except for the irreducible geometric leaves: `forestTag` / `recoverChoice_forest_eq` / `promote_collapse`
> (body-188), `forestComponentMem` (body-185), `represented_cases` (body-180), and the region constructions +
> wiring bridges.  `leftOf`, `leftResidual_mem`, `coverage`, `forestRecovered_mem`, and `promoted_region_eq` are all
> proved.  Verified in one chain: `190 → 181 → 177 → 174 → 167 → 162`.

**Net (bodies 88–190).**  The forward outer is closed to its irreducible geometric compatibility.  Backward outer:
the three sector bridges + a proved trichotomy.  Remaining: the two `HEq` transports (`backward_choice_heq`,
`forward_quotient_heq`), the sector-bridge internals, the disjointnesses and carrier closure, the region
classifiers, and the non-region base.  **Full unconditional resolved coassociativity still not claimed complete** —
the next front is the `HEq` transports, splitting the remaining round-trip content into component/sector facts.

### R-6c bodies 192–194 — the backward-choice HEq reduced to a forest value equality (2026-07-06)

Bodies 192–194 retire the backward-choice `HEq` type mismatch and drive its content down to a single forest value
fact.  Body-192 scouted the two `HEq` leaves: `backward_choice_heq` is light (at each component both sides have the
*same* codomain `Bool ⊕ (D.supply γ.…).ForestIdx`, so under the already-proved outer partition it reduces to a
homogeneous componentwise `Eq`), while `forward_quotient_heq` is heavy (a `ForestIdx`-over-contract-graph
reconstruction).  Body-193 proved the reusable transport `heq_of_index_eq` — two choice functions over equal index
Finsets that agree pointwise are `HEq` (`subst` + `heq_of_eq` + `funext`) — and assembled `backward_choice_heq` from
it.  Body-194 split the componentwise `Eq` by tag: the `inl true` / `inl false` cases close by the left/right sector
bridges (bodies 172/170) + the region tags, and the `inr` case reduces to the single fresh `forest_value_eq` (the
recovered forest tag on a forward image equals `q`'s original forest index).

> **Backward-choice, retired (bodies 192–194).**  The heterogeneous `backward_choice_heq` is now a homogeneous
> component agreement, split into three tag cases; two are proved from the sector bridges + tags, leaving only the
> `inr` value equality `forest_value_eq` — the choice-value de-contraction.  Verified: `194 → 193 → 164 → 160`.

**Net (bodies 88–194).**  Forward outer: closed to compatibility leaves.  Backward outer: three sector bridges + a
proved trichotomy.  Backward-choice: retired to `forest_value_eq`.  Remaining: `forest_value_eq`, the heavier
`forward_quotient_heq`, the sector-bridge internals, the disjointnesses and carrier closure, the region classifiers,
and the non-region base.  **Full unconditional resolved coassociativity still not claimed complete** — the next front
is the `forest_value_eq` scout (the choice-value de-contraction).

### R-6c bodies 196–200 — the backward-choice closed to a forest parent recovery (2026-07-06)

Bodies 196–200 drive the backward-choice residual all the way down to a single homogeneous geometry leaf — the
milestone body-200.  Body-196 split `forest_value_eq` into the body-188 tag pinning plus the fresh
`forestTag_forward_eq`; body-197 scouted whether that shares a root with `forward_quotient_heq` and found them
**dual** (domain-`q` vs codomain-`z` siblings) — attack separately; body-198 reduced `forestTag_forward_eq` by
`Sum.inr.inj` to the choice-value identity `forest_choiceAt_eq`; body-199 wired the whole backward-choice chain down
to that leaf; and body-200 **proved** `forest_choiceAt_eq` from a recovered forest-choice occurrence.

> **Backward-choice, closed (bodies 192–200).**  The heterogeneous `backward_choice_heq` is now supplied by a single
> homogeneous `Eq` of outer components — the forward round-trip **parent recovery** `parent_recovered : occ.γ = γ` —
> plus the occurrence construction.  A forest-region component `γ` of the forward image is the parent of a recovered
> occurrence `occ` carrying its own choice witness `occ.hchoice : choiceAt q occ.γ = inr occ.B`; the dependent
> `ForestIdx` transport `heq_transport_choice` (a `cases` on the parent `Eq`) then closes `forest_choiceAt_eq`.  No
> `HEq`, no choice-value abstraction remains — just Feynman-graph geometry.  Verified: `200 → 198 → 196 → 194 → 193
> → 164`.

**Net (bodies 88–200).**  Forward outer: closed to compatibility leaves.  Backward outer: three sector bridges + a
proved trichotomy.  Backward-choice: closed to `parent_recovered` (`occ.γ = γ`) + the occurrence construction.
Remaining: `parent_recovered`, the dual `forward_quotient_heq`, the sector-bridge internals, the disjointnesses and
carrier closure, the region classifiers, and the non-region base.  **Full unconditional resolved coassociativity
still not claimed complete** — the next front is the `parent_recovered` scout (the sector forest round-trip /
occurrence parent injectivity).

### R-6c bodies 202–208 — all four round-trips reduced to local bridges (2026-07-06)

Bodies 202–208 finish reducing the resolved coassociativity backward-map round-trip to local sector bridges.
Body-202 collapsed the backward-choice `parent_recovered` to `rfl` (the recovered occurrence is body-171's forest
bridge witness, so its parent is definitionally `γ`).  Bodies 203–208 reduced the forward-quotient `HEq`: a `ForestIdx`
transport (`heq_forestIdx`) over the already-proved ambient partition takes it to a component-Finset `HEq`, the
survivor ⊔ remnant `union_eq` split and the star `filter` split take that to the two membership bridges `survivor_mem`
/ `remnant_mem`, and body-208 assembled them out to body-165.

> **All four round-trips at their floor (bodies 88–208).**  Every round-trip obligation of the backward map now
> consumes only *local* sector / compatibility bridges: backward outer → the three sector bridges + a proved
> trichotomy; forward outer → the compatibility leaves; backward choice → `parent_recovered = rfl` from the forest
> bridge; forward quotient → the survivor / remnant membership bridges.  The `witnessSplit` round-trip proof-shape is
> complete — **no global `HEq` or `Sigma` proof-shape remains.**

**Net (bodies 88–208).**  The resolved-coassociativity backward map is closed to local bridges.  The remaining
genuine content is: the **sector bridge internals** (left / right / forest, bodies 170/171/172, and the
recovered-side `survivor_mem` / `remnant_mem`, bodies 206/207 — the `componentToRight` / `componentToForest`
round-trips); the **forward compatibility** (`forestTag` / `recoverChoice_forest_eq` / `promote_collapse`,
`forestComponentMem`, `represented_cases`); the disjointnesses and carrier closure; the region classifiers; and the
non-region base (contract geometry, measure, survivor/remnant `Inj`/`Gen`, carrier-proper / `rep` /
`selectedOuter_mem`).  **Full unconditional resolved coassociativity still not claimed complete** — the next front is
the sector bridge internals, starting with the lighter survivor / right side.

### R-6c bodies 210–211 — the right / survivor sector bridge floor (2026-07-07)

Bodies 210/211 open the lighter right / survivor sector bridge.  Body-210 (scout) found the two right leaves —
body-170's `rightRecovered_forward_membership` (G-level, backward `componentToRight`) and body-206's `survivor_mem`
(quotient-level, forward `survivorComponent = survivorReembed`) — are *dual but not identical*: opposite halves of
one right-sector round-trip over different graphs, so no shared provider (attack separately).  The abstract
sector-index right inverse (`right_left_inv` / `right_right_inv`, `ResolvedRightSectorEquivSupply`) is already proved
and underlies body-170.  Body-211 then reduced `survivor_mem` to a single image correspondence.

> **Survivor side, reduced (body-211).**  Since `survivorComponent = survivorReembed` preserves vertices at `rfl`,
> `survivor_mem` unfolds (`rightSurvivorForest_elements`, `rightDomain` filter) to the pure tag correspondence
> `survivor_image_correspondence`: the `recoverChoice z γ = inl false` components of `unionOuter z`, reembedded, are
> exactly `B`'s star-avoiding (`Disjoint · (starOfZ z)`) components.

**Net (bodies 88–211).**  The round-trip proof-shape is closed to local bridges; the survivor side is now a tag
correspondence (`survivor_image_correspondence`) and the right / G side a `componentToRight` round-trip
(`rightRecovered_forward_membership`).  The remnant / forest side (`remnant_mem`, `forestRecovered_forward_membership`)
is heavier (de-contraction), plus the forward compatibility, disjointnesses / carrier closure, region classifiers,
and non-region base.  **Full unconditional resolved coassociativity still not claimed complete** — the next front is
`rightRecovered_forward_membership` (the G-level right side, where the proved `rightEquiv` may apply).

### R-6c bodies 210–213 — the right sector reduced to two image correspondences (2026-07-07)

Bodies 211/213 reduce *both* right-sector leaves to image correspondences (after body-210's duality scout).  Body-211
reduced the quotient-side `survivor_mem` (via the `rfl`-level `survivorReembed`) to `survivor_image_correspondence`;
body-213 reduced the G-side `rightRecovered_forward_membership` to `right_image_correspondence`.

> **The `rightEquiv` negative finding (body-213).**  The proved abstract right-sector inverse
> (`RightPrimitiveIndex D G s ≃ (rightForest s).elements`) does **not** directly discharge either leaf: it lives at
> the sector-index / quotient-graph level (forward `survivorComponent`), while the region maps use abstract
> `componentToRight` fields disconnected from it.  So the right sector's remaining content is the correspondence
> between `B`'s **star-avoiding quotient components** and `q`'s **`inl false` source choices** — fielded fresh on each
> side, over a wiring bridge, not routed through `rightEquiv`.

**Net (bodies 88–213).**  The round-trip proof-shape is closed to local bridges; the right sector is now two image
correspondences (`survivor_image_correspondence`, `right_image_correspondence`).  The heavier remnant / forest sector
(`remnant_mem`, `forestRecovered_forward_membership`) — the de-contraction bridges — remains, plus the forward
compatibility, disjointnesses / carrier closure, region classifiers, and non-region base.  **Full unconditional
resolved coassociativity still not claimed complete** — the next front is the remnant / forest sector, where the
de-contraction may share the promotion compatibility (bodies 188/189).

### R-6c bodies 211–216 — all sector leaves reduced to image correspondences (2026-07-07)

Bodies 211/213/215/216 reduce all four sector bridge leaves to image correspondences, each by the same
`ofElements`-image + wiring / filter scaffolding: the survivor quotient side (211,
`survivor_image_correspondence`), the right G-side (213, `right_image_correspondence`), the forest G-side (215,
`forest_image_correspondence`), and the remnant quotient side (216, `remnant_image_correspondence`).

> **All sector bridges are image correspondences (bodies 211–216).**  Three are pure tag correspondences — the
> `G`-side maps are abstract `componentToRight` / `componentToForest` fields, and `survivorReembed` preserves vertices
> at `rfl`, leaving only the `inl false` / `inr` ⟷ star-avoiding / star-touching tag content.  The **remnant**
> correspondence is the one genuine de-contraction leaf: `remnantComponent` lands in the contracted graph with a
> nontrivial `remnantClass_eq`, so its `HEq` bridges different vertex sets.

**Net (bodies 88–216).**  The round-trip proof-shape is closed to local bridges, and the four sector bridges are now
four image correspondences (three tag, one de-contraction).  The remaining content is these four correspondences,
the forward compatibility (`forestTag` / `recoverChoice_forest_eq` / `promote_collapse`, `forestComponentMem`,
`represented_cases`), the disjointnesses / carrier closure, the region classifiers, and the non-region base.  **Full
unconditional resolved coassociativity still not claimed complete** — the next front is to bundle the three light tag
correspondences, then attack the single heavy `remnant_image_correspondence` (the de-contraction).

### R-6c bodies 219–222 — the sector correspondences reduced to sound / complete directions (2026-07-07)

Bodies 219–222 reduce all four sector image correspondences to two `Finset.mem_image` directions each — a uniform
`sound` / `complete` proof-shape: right (219, `componentToRight` ↔ `inl false`), forest (220, `componentToForest` ↔
`inr B`), survivor (221, `survivorComponent` ↔ star-avoiding, `HEq`-linked), remnant (222, `remnantComponent` ↔
star-touching, `HEq`-linked, de-contraction).

> **All four sector correspondences share one proof-shape (bodies 219–222).**  `image correspondence = sound +
> complete`, proved by term-mode `Finset.mem_image.mp` / `.mpr`, with the quotient-side pair (survivor / remnant)
> closing the cross-graph `HEq` via `eq_of_heq`.  Three are tag round-trips; the remnant pair alone carries the
> de-contraction (`remnantComponent` into the contracted graph, `remnantClass_eq`).

**Net (bodies 88–222).**  The round-trip proof-shape is closed to local bridges, and the sector bridge layer is now
eight uniform `sound` / `complete` directions (three tag pairs, one de-contraction pair).  The remaining content is
these eight directions, the forward compatibility (`forestTag` / `recoverChoice_forest_eq` / `promote_collapse`,
`forestComponentMem`, `represented_cases`), the disjointnesses / carrier closure, the region classifiers, and the
non-region base.  **Full unconditional resolved coassociativity still not claimed complete** — the next front is the
deeper sector-inverse wiring, starting with the lightest G-side `right_sound` / `right_complete` (where the proved
`right_surj` / `right_left_inv` / `right_right_inv` may apply).

### R-6c body 224 — the sector-inverse wiring stops at the abstract-region floor (2026-07-07)

Body-224 (scout) found the eight sector `sound` / `complete` directions **cannot** be discharged by wiring the
abstract region maps to the proved sector inverse: the region `componentToRight` / `componentToForest` are abstract
fields (never instantiated); the sector index over `fwdMap q` gives a parent in the recovered outer `(selectedOuterOf
q).1`, not `q.1.1`; and the sector `inl false` / `inr` tag is over `fwdMap q`'s `recoverChoice`-derived structure, not
`q.2`.  So the sector inverse is a red herring, and discharging the eight directions (not just fielding them) would
require concretizing the whole region construction (a large lift in the region / `recoverChoice` layer).

> **The sector-inverse route is retired (body-224).**  The eight `sound` / `complete` leaves are the honest floor for
> the abstract region construction; no further abstract reduction of the sector bridges is available.  Near-term
> progress pivots to the residuals that do not depend on concretizing the region map.

**Net (bodies 88–224).**  The round-trip and sector layers are fully mapped to their floors (eight `sound` /
`complete` directions).  The remaining reducible candidates are the **forward compatibility** (`forestTag` /
`recoverChoice_forest_eq` / `promote_collapse`, `forestComponentMem`, `represented_cases`) and the **disjoint /
carrier** (pairwise disjointnesses, recovered-outer carrier closure, bodies 158/159); beyond them lies the non-region
base (contract geometry, measure, survivor/remnant providers, `carrier_isProperForest` / `rep` / `selectedOuter_mem`).
**Full unconditional resolved coassociativity still not claimed complete** — the next front is the disjoint / carrier
candidates.

### R-6c bodies 226–228 — canonical carrier grounding begins (`carrier_isProperForest` proved) (2026-07-09)

Bodies 226/227 (scouts) examined the disjoint / carrier candidates; body-228 (proof) grounded the one genuine win into
a canonical model instance.  Body-226 found the recovered-outer pairwise disjointnesses (158) and carrier closure
(159) are both abstract floor obligations against an arbitrary carrier `D` (`recovered_outer_mem ≡ selectedOuter_mem`).
Body-227 found that instantiating `D` to the *canonical* carrier is a **repackaging, not a discharge** —
`mem_properDisjointAdmissibleDivergentSubgraphs` only re-expresses `∈ carrier` as `IsProperForest ∧ disjoint ∧ …`, so
for a *constructed* object the obligation is still the properness / disjointness of the construction (which loops back
to the abstract `componentToRight` / `promote` geometry).  Only `carrier_isProperForest` (137) is a genuine free win,
and no canonical `D` existed yet.  Body-228 builds `ResolvedCanonicalCarrierProperSupply`: a wrapper carrying the heavy
carrier ingredients (a per-graph proper-forest `index : ResolvedProperForestFiniteIndex G`, the star assignment, the
contraction CD, the two `mapPerm` naturalities) whose assembled carrier `G := (index G).carrier` makes
`carrier_isProperForest := fun G A hA => (index G).mem_proper A hA` a **theorem** (via `.toCarrierProperProvider`).

> **Canonical carrier grounding has begun (body-228).**  The canonical carrier is not merely repackaging: it genuinely
> discharges `carrier_isProperForest` (137), now proved from the proper-forest index's `mem_proper`.  But
> `selectedOuter_mem` (128) / `recovered_outer_mem` (159) and the region cross-disjointnesses (158) remain
> construction-specific — the constructed regions must still be shown proper / disjoint / admissible canonical members.

**Net (bodies 88–228).**  The four closure floor leaves now split: **`carrier_isProperForest` is grounded** (body-228),
while `selectedOuter_mem`, `recovered_outer_mem`, and the region pairwise disjointnesses stay construction-specific.
The other floors are unchanged (eight sector `sound` / `complete` directions, forward compatibility, and the non-region
base — now including the heavy canonical fields `index` / `starOf` / `hCD` / `mapPerm` naturalities).  **Full
unconditional resolved coassociativity still not claimed complete** — the next front is a `mem_rewrite` adapter
reshaping `selectedOuter_mem` / `recovered_outer_mem` into "the constructed forest is proper / disjoint / admissible".

### R-6c bodies 230–233 — canonical membership route established (2026-07-10)

The `mem_rewrite` adapter is built and connected: the two constructed-forest carrier-closure leaves are now supplied
from membership certificates rather than kept as raw hypotheses.  Body-230 (scout) established that carrier membership
of a constructed forest reduces to `IsProperForest` **plus** a section / canonicality condition (`forget_complete`
gives existence only; `forget` is not globally injective).  Body-231 proved the reusable infrastructure lemma
`forget_union_elements` (`(A.union B).forget.elements = A.forget.elements ∪ B.forget.elements`).  Body-232 defined the
certificate `ResolvedCanonicalMembershipCertificate` (fields `isProper : A.IsProperForest` and `recovered_eq`, the
section condition in generic form) and proved the adapter `cert_mem : certificate → A ∈ carrier` against the generic
`ResolvedProperForestFiniteCover` interface.  Body-233 wired it to the actual leaves via
`ResolvedCanonicalCarrierWiring` (a per-graph cover plus `carrier_eq : D.carrier G = (cover G).index.carrier`):
`.selectedOuterMem` proves `selectedOuter_mem` (128) from a certificate per `selectedOuterRawOf s`, and
`.recoveredOuterSupply` builds the body-159 supply from a certificate per region union.

> **The canonical membership route is established (bodies 230–233).**  `selectedOuter_mem` (128) and
> `recovered_outer_mem` (159) are no longer raw supply obligations: they are proved from membership certificates via
> `cert_mem` and the `carrier_eq` wiring.  Their residual is now exactly the certificate fields — `isProper` (the five
> `IsProperForest` conjuncts) and `recovered_eq` (the section) — per constructed forest.

**Net (bodies 88–233).**  Two of the four closure floor leaves are now **routed through certificates**
(`selectedOuter_mem`, `recovered_outer_mem`), joining the grounded `carrier_isProperForest` (body-228); only the region
pairwise disjointnesses (158) stay construction-specific among the closure leaves.  The other floors are unchanged
(eight sector directions, forward compatibility, non-region base).  **Full unconditional resolved coassociativity still
not claimed complete** — the next front is to fill a certificate field: the first `IsProperForest` conjunct (e.g.
`IsNonempty`) for the constructed forests, via `forget_union_elements`.

### R-6c bodies 235–242 — certificate `isProper` conjuncts, and the `selectedOuter_mem` domain defect (2026-07-12)

Filling the certificate's `isProper` field (the five `IsProperForest` conjuncts) for the two constructed forests
`X = selectedOuterRawOf s` and `Y = recovered-outer region union`.  The two *universal* conjuncts are proved
generically: `HasNonemptyComponents` (body-236, from the supplied `cd_nonempty`) and
`HasPositiveInternalEdgesComponents` (body-238, from a new sibling measure leaf `cd_positiveInternalEdges` — body-237
established that `IsConnectedDivergent` does not force positive edges, since `IsOnePI`'s bridge clause is vacuous on
zero edges).  Both discharge `X`, `Y`, and every future construction at once.

The *piece-specific* `IsNonempty` conjunct splits sharply.  For `Y`, body-241 proves it on the forward image
(`recoveredOuter_isNonempty`) **membership-independently** — from the domain outer's carrier membership + the body-168
region partition + `union_eq`, never touching the recovered carrier membership `unionOuter.2` (which would be circular).
For `X`, the audit (body-242) surfaced a **design defect, not a hard leaf**:

> **`selectedOuter_mem : ∀ s` is false at the all-right split (body-242, verdict THREADING OBSTRUCTION).**
> `selectedOuterRawOf p_R = ∅` (both `leftOf` and `promotedOf` empty when every tag is `Sum.inl false`), and
> `∅ ∉ D.carrier G` for the canonical carrier, so the *total* obligation is genuinely false at `s = p_R`.  But the
> real image-side sum is indexed over `forestChoiceCarrier` (which filters out `p_R`), and `EmptyPivot` already carries
> the all-right boundary **cover-external**.  The fix is a **domain correction** — state the membership on the filtered
> domain `∀ A, ∀ p ∈ forestChoiceCarrier A, selectedOuterRawOf ⟨A,p⟩ ∈ D.carrier G` — not a stronger proof.  (Body-151's
> `mixed_ne_pR` does not substitute: it excludes `p_R` only for reconstructed mixed codomain elements.)

**Net (bodies 88–242).**  The certificate `isProper` conjuncts stand as: `HasNonemptyComponents` and
`HasPositiveInternalEdgesComponents` proved generically for both forests; `IsNonempty` proved for `Y` (forward image)
and, for `X`, reduced to a **filtered-domain re-typing** of `selectedOuter_mem` (the all-right `p_R` is a genuine
`∅` counterexample of the *total* statement, carried cover-external by `EmptyPivot`); `0 < internalEdges.card` (depends
on `IsNonempty`) and `0 < complementEdges.card` (strict properness) unstarted.  **Full unconditional resolved
coassociativity still not claimed complete** — the next front is a filtered-domain `X.IsNonempty` local theorem, then a
restricted membership adapter that removes the false total membership field while keeping the total helper functions.

### R-6c bodies 244–246 — domain defect repaired at source; four of five `isProper` conjuncts discharged (2026-07-12)

Two things landed together.  **The selected-outer domain defect is repaired at its source:** the carrier-tagged
selected outer is now defined only on the filtered forest-block domain.  Body-244 proves `X.IsNonempty` on that domain
(`selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier`) from `p ≠ p_R` alone — a non-`inl false` component is
either left-selected (`leftOf` nonempty) or `inr B`-tagged (`promotedOf` nonempty, via `carrier_isProperForest` on the
carrier member `B`) — using no `EmptyPivot`, no body-151, no `promote_collapse`, and crucially not the false total
`selectedOuter_mem`.  Body-245 plants the **new root** `ResolvedSelectedOuterFilteredMemSupply` (total-supply-
independent): its `selectedOuter_mem` is the honest filtered obligation `∀ A p, p ∈ forestChoiceCarrier A →
selectedOuterRawOf ⟨A,p⟩ ∈ D.carrier G`, with a carrier-tagged `selectedOuterOfForestChoice` on the filtered sigma
(`.1 = selectedOuterRawOf` by `rfl`) and a `mem_of_mem_forestBlockDomFinset` reconnection to the sum consumer (which
already carries the summand's filter membership).

**And four of the five `IsProperForest` conjuncts are now discharged for both constructed forests:**
`HasNonemptyComponents` (236), `HasPositiveInternalEdgesComponents` (238), `0 < internalEdges.card` (246, from a
witness component via `mem_internalEdges`), and `IsNonempty` (244 filtered for `X`, 241 forward image for `Y`).

> **The total `selectedOuter_mem : ∀ s` is retired, not merely unproved** — it is *false* at the all-right split
> `p_R` for the canonical carrier (`selectedOuterRawOf p_R = ∅ ∉ D.carrier G`).  The honest obligation is the filtered
> new root (body-245); `EmptyPivot` carries the `p_R` boundary cover-external.

**Net (bodies 88–246).**  Only one `IsProperForest` conjunct remains — `0 < complementEdges.card` (strict properness,
`A.internalEdges < G.internalEdges`) — plus the certificate section `recovered_eq`.  The chain still references the
retired total root at `fwdMap` and the backward / bijection layer, a **migration boundary** (re-typing, not new
mathematics — `p_R` is never applied in any live sum).  **Full unconditional resolved coassociativity still not claimed
complete** — the next front is a `fwdMap` filtered-domain migration scout, then the strict `complementEdges` conjunct.

### R-6c bodies 248–254 — interface/statement migration completed (2026-07-13)

The `fwdMap` filtered-domain migration is carried out at the interface/statement level.  Body-248 (scout) found it is a
shallow **provider-retype**: every proof ports verbatim by `Subtype.ext rfl` (proof irrelevance on the carrier tag).
Body-249 defines `fwdMapFiltered` (carrier tag from the body-245 filtered root, not the total root); body-250 the
filtered witnessSplit cover interface, body-251 a legacy-bridge-free `dite` assembly of it.  Body-252 plants an
**independent, `Forward`-free value root** `ResolvedConcreteSummandValueSupply` (dropping the total-root field
`Forward`, retyping `quotientForest` / `quot_eq` via `selectedOuterRawOf`); body-253 re-points the round-trip cover and
branch data onto that value root; body-254 restates the summand agreement over it.

> **The retired total selected-outer root no longer appears in any canonical migration interface.**  It survives only
> in explicitly marked legacy-comparison adapters (`fwdMapFiltered_eq_legacy`, the several `.ofLegacy`).  The interface
> migration is complete; **canonical proof inhabitants remain** for witnessSplit membership, the branch geometry, and
> the value-side summand agreement.

**Migration status (statement vs canonical proof):**

| Layer | Statement | Canonical proof |
|---|---|---|
| filtered forward map | complete | membership root (body-245) |
| witnessSplit cover | `Forward`-free | branch specs / `witnessSplit_mem` remain |
| value bundle | complete | geometry fields remain |
| summand agreement | `Forward`-free | factor-equality discharge remains |
| legacy total root | retired | comparison adapters only |

**Net (bodies 88–254).**  The interface migration is complete (the retired total root is off every canonical
interface); the isProper conjuncts stand at four of five (only strict `complementEdges` remains).  A hidden domain
defect to audit next: `ResolvedSummandFactorBundle.selected` is **total** — the last place the filtered-domain
correction must reach.  **Full unconditional resolved coassociativity still not claimed complete** — the next fronts are
`witnessSplit_mem` canonical instantiation, the `summand_agree_value` factor-equality discharge (and the `selected`
audit), then the strict `complementEdges` conjunct.

### R-6c bodies 256–259 — filtered-domain migration complete at BOTH levels (2026-07-13)

The proof-level inhabitants are now built.  Body-256 proves canonical `witnessSplit_mem` (`q ∈ forestBlockDomFinset G`
from the reconstruction tags alone, `Finset.mem_sigma` — no `selectedOuter_mem`).  Body-258 re-keys the last term-path
helper to raw admissible subgraphs (`resolved_selectedOuter_left_factor_eq_of_parts_raw`, no `S` in its type).  Body-259
constructs the canonical `summand_agree_value_of_value (F) (V) : ResolvedSummandAgreeValueSupply F V` `.ofLegacy`-free
from `V + F` alone — `resolved_splitChoice_summand_agree_of_factor_eqs` fed the raw `hL` (258), the `S`-free `hR`, and
`hQ := V.quot_eq`; every gap closes by `rfl`/defeq, and the geometry leaves `hLdisj`/`hPD` are theorems on `V.Measure`,
not fields.

> **The filtered-domain migration is complete at both the interface and proof levels.**  The retired total
> selected-outer root is absent from the canonical forward map, witnessSplit cover, membership proofs, value bundle,
> and summand agreement; it survives only in explicitly marked legacy-comparison adapters.  **This was a domain
> correction, not a stronger proof of the false total theorem** — the case `p_R` remains cover-external through
> `EmptyPivot`.

**Net (bodies 88–259).**  Migration residual: **none** (the retired total root is confined to `.ofLegacy` comparison
lemmas).  What remains is purely mathematics-derived: among `IsProperForest`, only strict `0 < complementEdges.card`;
the certificate section `recovered_eq`; and the original geometry (branch specs, the eight sector directions, forward
compatibility, region cross-disjointnesses, non-region base).  **Full unconditional resolved coassociativity still not
claimed complete** — the next front is the strict `complementEdges` conjunct, the last `IsProperForest` piece, purely
geometric and independent of the (now complete) migration.

### R-6c bodies 262–267 — `IsProperForest` completed; carrier closure is an honest parametric-model obligation (2026-07-13)

The last `IsProperForest` conjunct is proved, and the certificate route is resolved into its true status.  Body-262
proves the complement-edge monotonicity infrastructure; body-263 discharges `0 < complementEdges.card` for both
constructed forests by **global monotonicity** (each has `internalEdges ≤` the domain outer, whose complement is
positive because the domain outer is a proper carrier member) — no per-component missing-edge witness, no deep leaf.
Body-264 assembles `IsProperForest` (all five conjuncts) for both: `X = selectedOuterRawOf` as a 5-tuple on the
filtered domain, `Y` via the generic elements-equality transfer `isProperForest_of_elements_eq`.  Bodies 265–267
resolve the certificate section: the generic `recovered_eq` / `ofForgetForest` section is an **honest leaf** (forget is
not globally injective); body-265's claim that `unionOuter.2` supplies membership "for free" was **circular** and is
**superseded by body-266** (`unionOuter z = ⟨rawRegionUnion z, recovered_outer_mem z⟩`; its `.2` *is* the leaf).
Body-267 plants the independent `rawRecoveredOuter` root (value from region maps + disjointness alone, no carrier tag)
and records the carrier-closure verdict.

> **All five `IsProperForest` conjuncts are proved for the relevant constructed forests, but properness does not imply
> membership in the supplied finite resolved carrier.  Carrier closure is therefore an honest parametric-model
> obligation, not a remaining coassociativity proof-shape gap.**

**Carrier-closure route table:**

| Route | Verdict |
|---|---|
| all resolved proper forests via `Finset.univ` | **impossible** — no global `Fintype (ResolvedAdmissibleSubgraph G)` |
| payload carrier extension | possible concrete-model work, **not free** (owes generic-`z` raw `IsProperForest` + `carrier_mapPerm` / `hCD`) |
| forget-image section | **obstructed** by non-injective `forget` / promoted-component ids |
| parametric carrier-closure supply | the **canonical current interface** |

**Net (bodies 88–267).**  `IsProperForest` (all five conjuncts) is complete; the migration residual is none.  Carrier
membership (the recovered / selected-outer closure) is an **honest parametric-model supply**, not a proof-shape gap:
`selectedOuter_mem` is filtered (body-245), `recovered_outer_mem` and the cross-disjointnesses are supplied.  **Full
unconditional resolved coassociativity still not claimed complete** — the next front is the top-level parametric
carrier-closure supply consolidating these (with the original geometry), not the concrete carrier-enumeration
construction, which is a separate phase.

---

### R-6c bodies 268–270 — the parametric layer completes as a single conditional coassociativity theorem (2026-07-14)

The parametric coassociativity layer is closed.  Body-268 fixes the carrier-closure verdict (docs anchor).  Body-269
consolidates the model's carrier-closure assumptions into one honest interface `ResolvedParametricCarrierClosureSupply`
(filtered selected-outer closure + three region pairwise disjointnesses + the **raw** recovered-outer membership, stated
on the bare region union — never the carrier-tagged `unionOuter`), with three converters.  Body-270 then inhabits the
raid-boss `ResolvedForestBlockBijectionSupply` (body-97) **directly from the filtered / value chain** and chains it to
`coassoc_gen`.  Every one of the twelve `sum_bij'` fields is supplied from the migrated chain (bodies 252/253/259)
except the forward codomain membership `toFun_mem`, which unfolds (via `Finset.mem_sigma` + `Finset.mem_attach`) to the
one genuinely new leaf — the forward quotient membership over the value root (`selectedOuterRawOf`), isolated as
`ResolvedForwardQuotientMemValueSupply.quotient_mem`.  The summand agreement is **derived** from `F + V` (body-259), not
assumed.

**The chain:**

```text
ResolvedParametricCarrierClosureSupply          (269)
  + filtered value bundle                       (252, Forward-free)
  + filtered witnessSplit cover                 (253)
  + forward quotient membership                 (270, the sole new leaf)
  + explicit base / geometry leaves             (carrier_isProperForest, rep / repCD / rep_gen)
→ ResolvedForestBlockBijectionSupply            (97, inhabited directly)
→ coassoc_gen                                    (270, coassoc_gen_of_parametric_model)
```

**The 12-field supply table (all Forward-free, no `.ofLegacy`):**

| `ResolvedForestBlockBijectionSupply` field | supplied by |
|---|---|
| `toFun` | `fwdMapFilteredValue F V ⟨q,hq⟩` (252) |
| `invFun` | `cover.witnessSplit` (253) |
| `toFun_mem` | `forwardMem.quotient_mem` + `mem_attach` (270, **new leaf**) |
| `invFun_mem` | `cover.witnessSplit_mem` (253) |
| `left_inv` | `cover.backward_witness` (253) |
| `right_inv` | `cover.forward_witness` (253) |
| `summand_agree` | `summand_agree_value_of_value F V` (259, **derived**) |
| `carrier_isProperForest` | base model leaf (96) |
| `rep` / `repCD` / `rep_gen` | representative base leaves |

> **The R-6c parametric layer is complete as a single conditional coassociativity theorem.**
>
> **The theorem path is entirely filtered-domain, value-rooted, Forward-free, and legacy-adapter-free.**

**Residual — separated exactly.**

| Kind | Status |
|---|---|
| theorem-level migration residual | **none** — no total `selectedOuter_mem`, no `.ofLegacy` on the path |
| new local leaf | `ResolvedForwardQuotientMemValueSupply.quotient_mem` (the only new obligation) |
| construction boundary | the concrete value cover's region / backward chain (bodies 156/157/173/184), still total-forward-phrased — a construction detail *below* the theorem, not a gap in it |
| model instance phase | carrier enumeration / permutation closure / `hCD` (phase 1b, separate) |
| original geometry / base leaves | explicit hypotheses of `coassoc_gen_of_parametric_model` |

`coassoc_gen_of_parametric_model` is Forward-free / `.ofLegacy`-free **as a theorem**: it takes the migrated value-root
`cover` (body-253) as a hypothesis.  **Full unconditional resolved coassociativity is still not claimed complete** — a
concrete model instance must discharge the new forward leaf, migrate the concrete cover construction off the total
forward map, and (phase 1b) build the concrete carrier.  But the parametric *layer* — model assumptions + geometry
leaves → `Δᵣ`-coassociativity on generators — is now one honest conditional statement.

---

### R-6c bodies 271–286 — the value-root construction migration completes; the concrete cover is built off the filtered root (2026-07-15)

The named construction boundary (body-273) is closed.  The concrete `witnessSplit` cover — the last piece feeding the
top-level theorem — is now built **entirely from the filtered value root**, with no total forward map, `Forward` supply,
legacy adapter, or phantom `S` on the canonical path.

> **The R-6c value-root construction migration is complete.**
>
> **The concrete `witnessSplit` cover and the top-level coassociativity theorem are constructed entirely from the
> filtered value root.  No total forward map, `Forward` supply, legacy adapter, or phantom `S` remains on the canonical
> path.**

**Two audit corrections were decisive (recorded so they are not re-litigated):**

* **body-273** — the quotient component of a codomain pair is NOT `rfl`-portable from the total root to the value root:
  `rightDomain`/`forestDomain` read `z.2` (the quotient), which is `V.quotientForestRaw` at the value root but
  `S.quotientForest` at the total root.  The migration is therefore **MEDIUM**, reconstructed from `V`'s own
  survivor/remnant split (`V.union_eq`), not a mechanical re-key.
* **body-284** — the backward round-trip residual is **three** leaves, not two: the forest-component `backward_choice`
  HEq needs the EXACT value `forestTag = B` (`forestChoiceSelected` forgets `B`) — a third genuine leaf, the value
  analog of `forest_choiceAt_eq` (body-200's forward occurrence-recovery), S-keyed in the total root.

**The canonical chain (all value-root, S-free):**

```text
S-free region cores + bridges (left/right/forest)     274–280   (rightPrimSelected / forestChoiceSelected / leftSelectedConcrete membership)
→ region coherence + raw closure + preimage root       281–283   (unionOuterValue / recoverChoiceValue / recoveredPreimageValue ∈ forestBlockDomFinset)
→ backward outer (pure) + exact 3-leaf audit           284
→ 3 leaves produce 2 whole round-trips                 285       (heq_of_index_eq + backward_outer + tags + leaf 3)
→ filtered concrete branch data + concrete cover       286       (ResolvedWitnessSplitFilteredValueConcreteData → .toCover)
→ ResolvedForestBlockBijectionSupply                   97
→ coassoc_gen
```

`coassoc_gen_of_recovered_preimage_value` (body-286) is the S-free top-level statement: `F` / `V` / `R.toCover` /
`forwardQuotientMemValueOfValue F V` (free, body-272) + base leaves → `Δᵣ`-coassociativity, **never** mentioning
`ResolvedParametricCarrierClosureSupply D S`.

**Final status.**

| Kind | Status |
|---|---|
| proof-shape residual | **none** |
| migration residual | **none** |
| construction boundary | **closed** (concrete value cover, body-286) |
| value round-trip geometry | **3 explicit leaves** (`forward_outer_value`, `forward_quotient_value`, `forest_value_eq`) |
| region geometry | sound/complete + classifier leaves (`mixed_ne_pR`/`mixed_ne_pL`, `forest_nonempty`) |
| carrier closure | honest model supply (`recovered_raw_mem` + pairwise disjoint, body-269) |
| concrete carrier instance | separate phase 1b (enumeration + permutation + `hCD`) |

The total-forward machinery is **not "unused"** — it is **retired from the canonical path**: it survives only in the
comparison / migration-check modules (`.ofLegacy`, `.toValueCore`, `.toParametricCarrierClosure`), never on the route to
`coassoc_gen_of_recovered_preimage_value`.  **Full unconditional resolved coassociativity is still not claimed
complete** — the three value round-trip geometry leaves + the region/carrier model supplies remain honest obligations,
to be discharged by a concrete phase-1b model instance.

---

### R-6c bodies 288–291 — the three round-trip leaves reduced to component-level geometry; every abstract HEq obligation eliminated (2026-07-15)

The three value round-trip leaves (`forward_outer_value`, `forward_quotient_value`, `forest_value_eq` — body-285) are
re-keyed onto the total-root forest-recovery / quotient-HEq machinery (bodies 174-208), all of which was already proved
and S-free where it matters.  Each reduces to LOCAL, component-level geometry; the abstract dependent-type / global-`HEq`
obligations are gone.

> **All abstract `witnessSplit` round-trip and global heterogeneous-equality obligations have been eliminated from the
> canonical R-6c path.**
>
> **The round-trip layer now depends only on six component-level geometry facts.**

**The reduction chain:**

```text
288 exact forest choice     → forestTag_agrees                                        (occurrence compatibility)
289 forward outer           → promote_collapse + forestComponentMem + represented_cases
290 forward quotient (HEq)  → survivor_mem_value + remnant_mem_value                   (via generic S-free HEq transports)
291 six local facts         → the three former global leaves → two whole round-trips → concrete cover → coassoc_gen
```

Body-288 builds the forest occurrence from `q`'s own `choiceAt` (breaking the `forestTag`-cycle) and reduces the forest
exact-`B` match to the single `forestTag_agrees`.  Body-289 mirrors the total-root `selectedOuterRawOf = leftOf ∪
promotedOf = leftResidual ∪ forestRecovered = A` (leftOf is pure-tag, no leaf).  Body-290 reduces the quotient `HEq`
through the reusable `heq_forestIdx` / `heq_of_membership_split` / `heq_finset_of_mem_iff` transports **without
circularity** (the RHS is the pure complementary star-filter partition; the LHS is `V.union_eq`; the graph transport is
body-289's outer equality — never `fwd q = z`).  Body-291 assembles all six over ONE shared `Data`.

**Two-layer status (the distinction matters for review).**

| Scope | Residual |
|---|---|
| round-trip layer | **exactly six component-level geometry leaves** |
| complete theorem | those six + (inside `Data`) the region sound/complete leaves, the carrier closure, `F` / `V`, and the base leaves |

So it is **not** "the whole theorem has six hypotheses" — it is the **round-trip geometry residual** that is six facts;
the model / carrier / base assumptions remain explicit and separate.  The six round-trip leaves:

```text
forestTag_agrees    forestTag = the occurrence-recovered index                       (288)
promote_collapse    (promote γ (forestTag …)).elements = {γ}                          (289, de-contraction singleton)
forestComponentMem  forest-recovered parent ∈ target outer A                          (289)
represented_cases   represented A-component ∈ forestRecovered                         (289)
survivor_mem_value  survivor ⟷ rightDomain  (tag-reducible: inl false ⟷ star-avoiding) (290)
remnant_mem_value   remnant  ⟷ forestDomain (genuine de-contraction)                  (290)
```

**Headline status.**

```text
proof-shape residual        none
migration residual          none
global HEq residual         none
abstract round-trip residual none
round-trip geometry         six local component facts
model / base assumptions    explicit and separate
```

`coassoc_gen_of_local_value_geometry` (body-291) is the S-free top-level theorem taking these six + the base leaves.
**Full unconditional resolved coassociativity is still not claimed complete** — the six component-level geometry leaves +
the region / carrier model supplies remain honest obligations, to be discharged by a concrete phase-1b model instance;
but the entire *abstract* round-trip / global-identity layer is now closed.

---

### R-6c bodies 293–299 — the round-trip layer reaches its final geometric floor: eight local model facts (2026-07-15)

The six component-level leaves (body-291) are each audited: four reduce to strictly more local facts (bodies 293/294/297/298)
and two are pinned as honest floors (bodies 295/296).  Body-299 assembles the result: **eight local model-geometry facts
imply resolved coproduct coassociativity.**

> **The canonical R-6c round-trip layer is complete at its final geometric floor.  Eight local component-level model
> facts imply resolved coproduct coassociativity; no proof-shape, migration, global-`HEq`, or abstract round-trip
> obligation remains.**

**The six-leaf → eight-fact map:**

| body-291 leaf | audit (body) | final floor fact(s) |
|---|---|---|
| `survivor_mem_value` | reduced (293) | `survivor_sound_value` + `survivor_complete_value` (`inl false` ⟷ star-avoiding bijection) |
| `remnant_mem_value` | reduced (294) | `remnant_sound_value` + `remnant_complete_value` (`inr` ⟷ star-touching bijection) |
| `forestComponentMem` | reduced (297) | `forest_parent_mem_value` (`componentToForest z δ ∈ z.1.1.elements`, pointwise) |
| `represented_cases` | reduced (298) | `represented_forest_complete_value` (a represented `A`-component has a `componentToForest` preimage) |
| `forestTag_agrees` | floor pin (295) | `forestTag_agrees` (opaque `forestTag` = the occurrence-recovered `B` at forward images) |
| `promote_collapse` | floor pin (296) | `promote_collapse` (de-contracting a parent by its forest index returns the parent singleton) |

Bodies 293/294 mirror the total-root survivor/remnant image correspondences (bodies 205-222) **z-locally** — never using
the forward bridge at `q := recoveredPreimageValue z` (which would presuppose the round-trip `fwd (recoveredPreimageValue
z) = z`).  Bodies 297/298 reduce the two set-membership leaves to pointwise `componentToForest` facts via the image
structure of `forestRecovered`.  Bodies 295/296 pin the two genuine floors: `forestTag` is honestly arbitrary (the region
core keeps no `B`/occurrence for a generic `z`), and `promote_collapse` needs the exact whole-component forest index —
neither is derivable from the abstract supplies.

`coassoc_gen_of_geometry_floor` (body-299) bundles the eight facts over ONE `Data` and chains through body-291/286: the
old six leaves are gone from its arguments; only the eight floor facts + the base leaves remain.

**These eight facts are an interface, not a backlog.**  They are the honest geometry that any concrete region / carrier
*model* must supply — de-contraction (`promote_collapse`), parent membership (`forest_parent_mem_value`,
`represented_forest_complete_value`), tag occurrence (`forestTag_agrees`), and the survivor/remnant star sound/complete
directions.  They are NOT unfinished proof-shape obligations.

**Two-layer status (reviewer distinction).**

| Scope | Residual |
|---|---|
| round-trip geometry layer | **exactly eight local model facts** |
| complete theorem | those eight + (inside `Data`) region sound/complete, carrier closure, `F` / `V`; + the base leaves (`carrier_isProperForest`, proved 5/5 bodies 264/266; `rep`/`repCD`/`rep_gen`) |

The canonical path to `coassoc_gen_of_geometry_floor` is entirely **S-free, `Forward`-free, and legacy-adapter-free**.
The four completion nodes now read: **body-271** parametric theorem · **body-287** construction migration · **body-292**
global-identity elimination · **body-299** final local-geometry floor.  **Full unconditional resolved coassociativity is
still not claimed complete** — a concrete phase-1b model instance must discharge the eight local facts + the region /
carrier supplies — but the round-trip layer is now closed at its final, irreducible geometric floor.

### R-6c bodies 306–334 — the faithful phase-1b geometry is rebuilt on multi-star de-contraction (2026-07-17)

> **The faithful phase-1b path no longer uses the single-parent geometry floor.**  Multi-star de-contraction is now
> constructed through touched-component localization and collection-level promotion.  Forward outer reconstruction reduces
> to choice alignment and explicit concrete-model gates, with no parent-membership or singleton-collapse assumption.

The eight-fact geometry floor (bodies 293–299 above) is a valid **conditional** interface, but bodies 306–315 established
that it is **uninhabitable in the faithful model**, and bodies 316–334 rebuilt the codomain-orphan region from the ground
up.  The corrections this arc records:

* **floor-297/298 are FALSE at a generic/orphan codomain `z`** (`forest_parent_mem_value` /
  `represented_forest_complete_value`): a multi-star quotient component has no single parent in `z.1.1.elements` — the
  codomain-side analogue of the retired total `selectedOuter_mem` (body-128).
* **Codomain filtering is not allowed** — it deletes genuine RHS `Δᵣ` terms (multi-star `B` are valid carrier members).
* **body-299 stays a valid conditional theorem**, but its floor interface (`forestComponentMem` = floor-297, a field of
  body-289's supply) cannot be inhabited faithfully — a dead concrete reduction, now bypassed.
* **The singleton `promote_collapse` is FALSE for a multi-component `B`** (`promote_elements` emits a collection).
* **body-303's parent-image predicate is superseded** by the touched predicate `representedByTouched`.
* **The external-leg gap is a structural CK datum, not a proof deficiency** — the concrete carrier's quotient components
  are leg-complete (`legLift`).

The new canonical chain (bodies 316–334, all PROVED axiom-clean `[propext, Classical.choice, Quot.sound]`):

```text
touchedOuterComponents / touchedOuterForest      (316-317)
→ localize δ into the touched-forest contraction  (318-321)  M1
→ touched-leg-lift parent                          (326)      localizedParentWithTouchedLegs
→ toInner / innerRaw                               (327-328)
→ promote-to-touched-collection                    (328)      M3
→ parent disjointness / injectivity                (329-330)  D4 (starOf_fresh + cd_nonempty)
→ concrete forestTag                               (331-333)  forestTag := ⟨innerRaw, innerRaw_mem⟩
→ promotedTouchedUnion = represented outer          (334)
→ leftResidual ∪ promotedTouched = original outer  (334)      forward-outer collection core, NO floor-297
```

**Two-layer status.**

| PROVED mechanical geometry | Explicit model / construction gates |
|---|---|
| M1 localization (316–321) | `legLift` (δ-leg-completeness, structural CK) |
| M3 collection promotion (322–328) | `parentCD` (M2b, power-counting) |
| D4 disjointness / injectivity (329–330) | `innerRaw_mem` (`ForestIdx` carrier landing) |
| forest source / `forestTag` construction (331–333) | `starOf_fresh` / `cd_nonempty` providers |
| collection-level forward-outer core (334) | choice alignment · cross-disjointness · `recovered_raw_mem` · Front-2 quotient/remnant coherence |

**Crucial separation.**  `forestTag` is now a **construction** (body-333, via D4 uniqueness), NOT an arbitrary field; its
forward-image identity `forestTag_agrees` (`= occurrence.B`) is a **theorem-pending** leaf confluent with Front-2, NOT a
standing model datum — a strict improvement over the retired opaque-field status (body-295).  **Full unconditional
resolved coassociativity is still not claimed** — choice alignment, the concrete model gates, and Front-2 confluence
remain — but the multi-star de-contraction geometry is a completed, axiom-clean arc.

---

### R-6c bodies 335–364 — the faithful multi-star value construction reaches `coassoc_gen` (2026-07-18)

> **The faithful multi-star value construction now produces a concrete filtered `witnessSplit` cover and reaches
> `coassoc_gen`.  The proof architecture is complete; all remaining hypotheses are explicit concrete-model inhabitants.**

Body-334 closed the forward-outer collection *core*; this arc carries the faithful multi-star construction all the way
to the raid-boss.  `coassoc_gen_of_multiStar_model` (body-364) is the S-free / value-root top-level theorem — the same
proof term as body-286, with its `R.toCover` replaced by body-363's canonical `toMultiStarCover`.  All bodies PROVED
axiom-clean `[propext, Classical.choice, Quot.sound]`.

```text
337-341  concrete right region · left/right/forest cross geometry · touched-choice alignment · forward-outer value wiring
343      occurrence inversion + ForestIdx transport   (forestTag_agrees_multi = the exact-B geometric identity, HEq)
345-347  survivor collection HEq   (tag partition · round-trip · heq_finset_of_mem_iff)
348-359  remnant machinery         (tag partition · star coherence · inner-source selector · re-contract data
                                     · hardcoded-star swap · component round-trip · collection HEq)
360      forward-quotient assembly  (heq_of_membership_split fed by V.union_eq + survivor 347 + remnant 359)
361      recovered-identity root    (forward-outer + forward-quotient + exact-B under ONE shared Tags)
362      forest-tag identity adapter (Tags.forestTag = forestTag_fwd_value — the one vocabulary boundary; rfl/proof-irrel)
363      multi-star concrete cover   (toMultiStarCover = R.toCover over one shared Data — no Tags/Data transport)
364      conditional coassoc_gen     (body-286 raid-boss proof term, R.toCover ↦ toMultiStarCover)
```

**The false floor is not on the canonical path.**  The eight-fact geometry floor (bodies 293–299) — `floor-297`
(`forest_parent_mem_value`), the singleton `promote_collapse`, `represented_forest_complete_value` — is FALSE at a
multi-star orphan codomain and is **not used** anywhere on this path.  No `.ofLegacy`, no `Forward`, no phantom
total-root `S`, no `forgetHopf`, no facade.  (Body-364's occurrence-inversion binder is the *forest* inversion supply;
downstream wrappers name it `OccInv` to avoid confusion with the retired total-root phantom `S`.)

**Residual — proof-shape vs model inhabitant.**

```text
proof-shape residual        none
remaining hypotheses        explicit concrete-model inhabitants, discharged one socket at a time (Front-3)
```

| Front-3 bank | Sockets |
|---|---|
| 1. definitional wiring (rfl for multi-star `Tags`) | `hForest` · `hFT` · `hRight` |
| 2. derived geometry | `hround` (via 358) · 6 sound/complete bridges · `hSurvivor` |
| 3. structural CK inhabitants | `legLift` · `innerStar_agrees` (349) · occurrence inversion (343, `OccInv`) |
| 4. power-counting / carrier | `parentCD` · `innerRaw_mem` · `recovered_raw_mem` |
| 5. base model | `P` (carrier proper) · `Fstar` · `Measure` · `rep` / `repCD` / `rep_gen` |
| 6. unconditional wrapper | assembles 1–5 into an unconditional statement |

**Full unconditional resolved coassociativity is still not claimed** — the Front-3 model inhabitants remain honest
obligations.  But the *proof architecture* is complete: from the touched-localization geometry (body-334) through the
raid-boss (body-97 / body-286) to `coassoc_gen`, the faithful multi-star path is closed, and what remains is plugging a
concrete model into a finished socket, not building a proof DAG.

### R-6c bodies 403–425 — the canonical supported carrier gets a genuine inhabitant (2026-07-19)

One of those Front-3 sockets — the **canonical carrier** `W` (`ResolvedCanonicalCarrierProperSupply`) — is now
**closed with a real inhabitant**, and the way it closed is the point.

The carrier's `rightTerm_mapPerm` field looked like it needed a *strict fresh-star equivariance*
(`starOf (G.mapPerm σ) … = σ (starOf G …)`).  Body-403 did not assume it — it **proved that law impossible**: on a
graph with two swappable fresh names, ambient-support pins the configuration but the strict law forces the star to move,
a contradiction (a nominal-set / fresh-name obstruction).  So the honest move was not "assume the certificate" but
"replace the mechanism that needed it."

That is what bodies 405–425 did:

- **the law was relaxed to a *class* invariant** and then *derived* from a **finite correcting permutation** `τ` that
  fixes the ambient vertices and only relabels the fresh stars (bodies 405–411).  `τ` does the equivariance work that no
  single star assignment could;
- **the ownership cycle was cut**: the geometry was refactored onto a `rightTerm`-free *raw core*, so a full carrier can
  be assembled *from* the raw facts rather than presupposing itself (body-412);
- **the global proper-forest carrier was proven finite** — `Fintype (ResolvedFeynmanSubgraph G)` is *constructible* (the
  subgraph data is bounded by the ambient graph; enumerate vertex subsets and edge/leg sub-multisets), overturning a
  long-standing "no `Fintype` by design" design note and unlocking a saturated `Finset.univ.filter IsProperForest`
  carrier (body-415);
- **naturality, and two orthogonal emptyings** (ambient-support and connected-divergence) were proven, with the ambient
  connected-divergence *recovered from carrier membership*, never reverse-engineered from properness (bodies 416–418);
- the **resolved contraction was identified with the flat one** (bodies 419–422), so the flat Connes–Kreimer
  connected-divergence theorem could be reused, transported back through a same-forest star renaming (bodies 423–424);
- body-425 assembles all of it into `canonicalSupportedCarrierProperSupply`.

| Result | Status |
|---|---|
| `W` inhabitant | **constructed** (axiom-clean; full build ✔) |
| strict `star_mapPerm` | **retired** (proven inconsistent, body-403) |
| `rightTerm_mapPerm` | **derived** from the finite correcting permutation |
| global carrier finiteness | **proved** (overturning "no `Fintype` by design") |
| raw-carrier `hCD` | **proved** from the flat canonical CD theorem, no strict equivariance |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| unconditional coassociativity | **not yet claimed** |

The carrier root is closed *constructively*: strict fresh-star equivariance is gone, replaced by finite correcting
permutations.  The multi-star coassociativity line's *other* payload inhabitants remain separate honest obligations.

### R-6c bodies 426–439 — the canonical carrier closes both multi-star membership obligations (2026-07-20)

With `W` built, the coassociativity chain still needed the model to *assert* two carrier-membership facts as opaque
supply fields: that a de-contracted inner forest (`innerRaw`) and that the recovered outer union (`recovered_raw_mem`)
land back in the carrier.  These bodies **prove both**, and — the point again — how they prove them.

The key that unlocks everything is body-415's decision to make the carrier a **finite saturated
`Finset.univ.filter IsProperForest`** rather than an opaque `Finset`.  Membership in it is now an `iff` (body-426):
a forest is in the carrier exactly when the ambient graph is support-well-formed and connected-divergent and the forest
is *proper*.  So a carrier-membership obligation becomes a properness obligation — checkable geometry, not an axiom.

- **`innerRaw_mem` falls immediately** (body-427): the inner forest's properness is already a theorem (body-378), and its
  ambient conditions come from the parent's own connected-divergence.  The closure supply is now a *derived
  construction*.
- **`recovered_raw_mem` is the deep one.**  The recovered union is a proper forest iff five conjuncts hold; four of them
  reduce to generic facts or to the quotient forest's own properness (bodies 428–429) — with **no forward-outer
  round-trip**, so no circularity.  The single genuine residual is *strict properness*: the union does not consume all of
  the ambient's internal edges.
- That residual is settled by **`count` geometry, never by set non-membership** (bodies 430–438).  A subtle but decisive
  point: `EdgeIdsUnique` is **not** `Nodup` — distinct edges have distinct ids, but that says nothing about a single
  edge's multiplicity — so the honest primitive is a strict *count* inequality, exactly as the flat theory already does.
  A residual edge of the quotient is lifted back to the ambient (the contraction's internal edges are *definitionally*
  the outer complement retargeted), and each of the three recovered regions (left survivor / right survivor / forest
  remnant) is shown to under-count it, the counts summing safely because a pairwise-disjoint forest gives every edge at
  most one owner (body-432).
- The forest region's alignment — where the recovered geometry is expressed through a *touched* localization rather than
  the whole outer — is closed **entirely inside that touched/M1 geometry** (body-437): the two `Classical.choose` edge
  preimages are never reconciled, and no occurrence / promotion / wiring value-supply is pulled in; the whole↔touched
  retarget agreement is proven on the preimage's support alone, its one impossible case ruled out by star freshness.
- Body-439 classifies the union's edge-owner into the three regions and assembles the
  `ResolvedMultiStarCarrierClosureBundleSupply` in full.

| Result | Status |
|---|---|
| `innerRaw_mem` | **theorem** (body-427, over `W`) |
| `recovered_raw_mem` | **theorem** (body-439, count-safe region separation) |
| carrier-closure bundle | **fully derived** from `W` + value core + measure leaves + `EdgeIdsUnique` |
| forward-outer round-trip | **not used** anywhere in the closure line |
| `Core` / `DivergenceMeasure` / `Ids` | **not** unconditionalized (honest inputs) |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| unconditional coassociativity | **not yet claimed** |

The canonical saturated carrier now closes **both** multi-star carrier-membership obligations.  The remaining
`coassoc_gen` inputs are genuinely elsewhere: value geometry (`VBuild`, the value core's `legComplete` / `parentCD`), the
star / occurrence / split supplies, and the base-model representatives.

### R-6c bodies 440–534 — the residual purge: `coassoc_gen` reduced to two CK model laws

With the canonical carrier `W′` in hand and both carrier-membership obligations closed (bodies 426–439), the campaign
turned to the remaining `coassoc_gen` inputs — a long tail of *construction artifacts* (bijection/transport supplies that
are, in principle, provable from the geometry) mixed with a few genuine *model laws* (power-counting / measure facts).
Bodies 440–534 discharge every construction artifact and isolate the genuine floor to **two** named CK-model laws.  Each
body is one axiom-clean file; all depend only on `[propext, Classical.choice, Quot.sound]`.

**What "discharged" means here.**  A construction artifact was previously an opaque field the `coassoc_gen` supply *asked
for*; discharging it means proving it as a theorem of the resolved geometry so it disappears from the capstone's
signature.  The endpoint is a `coassoc_gen` whose hypotheses are only the honest model laws plus the base-model
representatives (`rep` / `repCD` / `rep_gen`) — nothing structural, nothing transport-shaped.

The purge, in order:

1. **Strict star obligations become theorems (446–468).**  The promoted-star / inner-star raw obligations
   (`StarProm` / `InnerStarRaw`), historically a strict-law socket, are discharged via a *correcting permutation*: the
   raw star assignment is repaired to the canonical one, so the obligations become proofs rather than assumptions.
2. **Native conditional coassociativity (469–495).**  The faithful filtered value layer plus the α forward map and its
   round-trip close the membership geometry completely (`canonicalMultiStarAlphaRoundTripLeafSupply_closed`).
3. **Residual purification (496–510).**  `Fmem`, `Split`, `survivorInj` + `survivorGen`, `quotient_mem`, and the
   occurrence supply `OccRaw` are **all discharged**, yielding
   `coassoc_gen_of_canonicalMultiStar_alpha_quotEq_occurrence_discharged` — whose only remaining non-representative
   inputs are `quot_eq`, `ValueGeometry`, and the measure leaves.
4. **The `quot_eq` campaign — the mathematical core (511–529).**  `quot_eq` (the outer forest's quotient generator
   equals the inner quotient-of-quotient generator, `rightTerm A′ = rightTerm B` under the doubly-contracted geometry)
   was the last construction artifact.  It is **derived, not assumed**, by building the *corrected two-stage* contraction
   geometry and proving the one-stage and two-stage corrected contraction graphs equal — crucially, **never** the vertex
   permutation itself, only the corrected contraction *graphs*.  The delicate steps: a re-encounter with the
   body-446-grade fact that `sourceLeftStar ≠ targetLeftStar` (body-519), the surviving-vertex partition
   "input-outer survivor **or** corrected `targetLeftStar`" (body-521), a three-route vertex correspondence inhabiting
   the body-513 whole-vertex socket (bodies 522–523), a scope repair keeping the retarget field on `G`'s own vertices
   (∀v ∈ G.vertices, not unrestricted — body-524, catching the same trap as 519), and the exact edge-residual identity
   `Q.internalEdges = (A.I − S.I).map f` (bodies 527–528).  At **body-529, `quot_eq` is discharged**: the capstone
   `coassoc_gen_of_canonicalMultiStar_alpha_construction_discharged` now depends on `Measure / E / ValueGeometry / rep*`
   **only** — every pure construction artifact is gone.
5. **`ValueGeometry` decomposed into two CK model laws (530–531).**  The surviving `ValueGeometry` aggregate is not one
   opaque record but two honest laws.  Its `legComplete` half splits: the *upper* leg inclusion is **derived** from the
   earlier touched-localization geometry (body-320), and the *lower* conjunct (`touchedLegSaturated`) is **derived** from
   a single primitive carrier property — `LegModel`, the multiplicity-safe *external-leg saturation* law (every live
   carrier component's boundary legs are covered by the component's own external legs).  Its `parentCD` half is `Parent`,
   the *inverse-decontraction* connected-divergence law.  The result
   `coassoc_gen_of_canonicalMultiStar_alpha_model_laws` has inputs `Measure / E / LegModel / Parent / rep*`.
6. **The frontier verdict (532), and the fourth emptying axis `W″` (533–534).**  The two laws are sharply different in
   nature:
   - **`LegModel` is combinatorial and `mapPerm`-invariant** (`resolvedExternalLegSaturated_mapPerm_iff`): saturation
     survives vertex relabeling, so a *saturation-filtered* sub-carrier of `W′` is still `mapPerm`-closed — a genuine
     new emptying axis, not an ad-hoc restriction.  This is realized as **`W″`** (`canonicalLegSaturatedCarrier…`,
     body-533): `W′` filtered by intrinsic forest saturation, on which `LegModel` is no longer an input but a **theorem
     of carrier membership**.  Body-534 then proves the saturation *algebra* (union and nested-promote closures,
     multiplicity-safe) and applies it so that the first major construction, `selectedOuter`, passes the axis: its `W″`
     membership — hence the `Fmem` supply — is canonically derived, reading no target membership.
   - **`Parent` is physics.**  Every ambient power-counting class runs parent→quotient; the law needed is the *inverse*
     (a quotient component plus an inserted divergent forest de-contracts to a divergent parent), and since the
     superficial degree is arbitrary it is genuinely not derivable from the forward-preservation environment.  It stays
     an honest divergence typeclass — the same status as the Weinberg/CK power-counting facts in §4.

| Milestone | Result |
|---|---|
| all pure construction artifacts (`Fmem`/`Split`/`survivor*`/`quotient_mem`/`OccRaw`/`StarProm`/`InnerStarRaw`/`quot_eq`) | **discharged** — gone from the capstone (bodies 496–529) |
| `quot_eq` | **derived** from corrected two-stage contraction geometry (body-529), not assumed |
| `ValueGeometry` | **decomposed** into `LegModel` (external-leg saturation) + `Parent` (inverse-decontraction CD) (530–531) |
| `LegModel` | `mapPerm`-invariant → **absorbed** by the `W″` saturation carrier; `selectedOuter` already passes (533–534) |
| `Parent` | honest physics divergence law (not derivable from forward preservation) |
| final `coassoc_gen` residual | `Measure` / `E` / `LegModel` / `Parent` / `rep*` |
| axioms (every body) | `[propext, Classical.choice, Quot.sound]` |
| unconditional coassociativity | **not yet claimed** |

The headline of this stretch: **native resolved `Δᵣ`-coassociativity now rests on nothing but two CK model laws and the
base representatives** — one of which (`LegModel`) is on a concrete combinatorial path to elimination via the `W″`
carrier, the other (`Parent`) a genuine, isolated power-counting assumption.  The remaining work is finishing the `W″`
closure of the other two constructions (`recoveredRawUnion`, `canonicalCorrectedQuotientRaw`) so that `LegModel` drops
off the signature entirely, leaving `Parent` as the sole honest physics input.

---

*Maintained alongside `HOPF_DECOMPOSITION.md` (internal, full sprint log).
This file is the reviewer-facing distillation; do not add day-by-day logs here.*
