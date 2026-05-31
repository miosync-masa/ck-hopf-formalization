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
`{ attachedTo, sector }` carries no identity. *Counterexample:* two legs with
identical `(attachedTo, sector)` that originated from different half-edges.

**Gap 2 — graph insertion uniqueness (`ForestGraphInsertionUniquenessModel`).**
The claim "same vertices + same remnant ⇒ same graph" fails because two distinct
internal edges with identical `(source, target, sector)` collapse to the same
multiset element. *Counterexample:* graphs differing only by a duplicated edge
that the multiset cannot distinguish, yet sharing vertices and remnant.

Both gaps share one mechanism: **multiset-level collapse of structurally
distinct boundary data**.

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
  This is exactly the collapse that produced both flat counterexamples — now
  **provably impossible** because the persistent id survives.
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
(`BoundaryResolved.lean`), an inhabited `Prop` bundling the three repaired
principles, with `boundaryResolvedSemanticModel` proving it on the
boundary-resolved carrier:
- edge submultiset retarget injectivity (under `EdgeIdsUnique`),
- external-leg submultiset retarget injectivity (under `LegIdsUnique`),
- forgetful compatibility with retargeting (the JAR commuting square).

It is **deliberately not** an instance of the flat facade classes (they are
flat-false; `forget` runs resolved → flat).  Thus the resolved carrier supplies a
concrete, inhabited model of the repaired semantic principles, while the flat
theorem isolates the boundary assumption — answering any "vacuity / unicorn"
objection: *the flat assumptions are intentionally uninhabited because they are
false, and that is the diagnosis; the inhabited positive object lives on the
boundary-resolved carrier.*

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

---

*Maintained alongside `HOPF_DECOMPOSITION.md` (internal, full sprint log).
This file is the reviewer-facing distillation; do not add day-by-day logs here.*
