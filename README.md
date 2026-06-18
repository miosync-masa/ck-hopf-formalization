# CK Hopf Formalization

[![Lean Action CI](https://github.com/miosync-masa/ck-hopf-formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/miosync-masa/ck-hopf-formalization/actions/workflows/lean.yml)

A Lean 4 formalization of the **Connes–Kreimer Hopf algebra of Feynman graphs**.

This repository is extracted from a broader `GaugeGeometry` development.  The Lean
namespace `GaugeGeometry.QFT…` is intentionally retained to preserve **stable
imports and theorem names** — do not rename it.

## What is proved

The conditional Hopf algebra `HopfAlgebra ℚ HopfH` (coproduct, counit,
coassociativity, and **both** antipode axioms) is assembled around the
Connes–Kreimer forest cover identity over a flat Feynman-graph carrier.

The entire conditional surface reduces to **exactly two named kernels**, both of
which are *boundary-semantics facades*: false on the flat carrier (with formal
mechanism-level counterexamples — the flat edge/leg retarget maps are proved
non-injective in `GaugeGeometry/QFT/HopfAlgebra/BoundaryResolvedCounterexamples.lean`),
and **theorems on a boundary-resolved carrier**
(`ResolvedFeynmanGraph`, persistent half-edge / leg identities), with the flat
carrier recovered as its forgetful image.

- `ForestGraphInsertionUniquenessModel`
- `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`

The former third kernel — the CK §3 right-antipode cancellation
`AntipodeForestRightCoreIdentity` — has been **eliminated**: the right antipode
axiom is *proved* via the convolution / local-nilpotency route (the reduced
convolution operator `id − η∘ε` is locally nilpotent on generators), not assumed.

The constructive body contains **no** `sorry`, `admit`, or project-level axiom.

## Non-vacuity (not a unicorn)

The conditional flat-carrier theorem is a **proof-skeleton factorization**, not an
unconditional theorem about the flat carrier: the two flat boundary assumptions
are shown to be *false* on the flat carrier (that is the diagnosis). Non-vacuity
is supplied separately by the concrete, **inhabited** object
`BoundaryResolvedSemanticModel` (witness `boundaryResolvedSemanticModel`,
`GaugeGeometry/QFT/HopfAlgebra/BoundaryResolved.lean`), which proves the
corresponding *repaired* principles — edge / external-leg retarget injectivity and
the forget-retarget commuting square — on boundary-resolved graphs. The flat
facade classes are intentionally **not** instantiated; the positive semantic
object lives on the resolved carrier.

## Main certificates

Headline cross-file certificates (in `GaugeGeometry/QFT/HopfAlgebra/HopfAlgebra.lean`,
namespace `GaugeGeometry.QFT.Combinatorial`):

- `hopfAlgebraHopfH_ofBoundaryFacadesAndReflection_convolution` — the full
  `HopfAlgebra ℚ HopfH` from the two boundary facades + the power-counting
  reflection alone (no antipode kernel).
- `coassocStrictForestH58Ready_ofBoundaryFacadesAndReflection` — the
  coassociativity boundary.
- `AntipodeStrictForestRightReady_ofConvolution` — the right antipode axiom via
  the convolution route (`GaugeGeometry/QFT/HopfAlgebra/AntipodeConvolution.lean`).

Boundary-resolved carrier:
`GaugeGeometry/QFT/Combinatorial/ResolvedFeynmanGraphs.lean`
(`GaugeGeometry.QFT.Combinatorial.ResolvedFeynmanGraph`).

R-4-full Phases 1–2 (boundary-resolved reconstruction, in progress; standalone
modules, not yet wired into `Main`):

- **Phase 1** — `GaugeGeometry/QFT/Combinatorial/ResolvedSubGraph.lean`: the
  resolved subgraph / admissible-forest / contraction / quotient-remainder
  carriers, proving the resolved counterparts of **both** flat-false boundary
  interfaces — insertion uniqueness (`parent_eq_of_remainder_eq`) and external-leg
  liftability (`externalLegs_lift_unique`).
- **Phase 2** — `GaugeGeometry/QFT/HopfAlgebra/ResolvedCoproductIndex.lean` and
  `ResolvedCoproduct.lean`: the resolved proper forest forgets into the flat finite
  proper-forest index (`forget_mem_properDisjoint_filter_complement`), and the
  resolved coproduct summand/sum is defined through that bridge
  (`strictSummandViaForget`, `strictCoproductSum`).
- **Phases 3–5** — `ResolvedCoproduct.lean`: the resolved coproduct equals the flat
  strict-forest coproduct as a linear map
  (`resolvedCoproduct_toLinearMap_eq_flat`), and resolved coassociativity is
  inherited by transfer (`resolvedCoproduct_coassoc_ofReflection`, gated only on the
  two boundary facades).
- **Phase 6c** — `ResolvedPayloadModel.lean`: the payload hypothesis is *inhabited*.
  `resolvedHopfPayloadFamily_exists : Nonempty ResolvedHopfPayloadFamily` constructs
  a canonical witness for every generator — the constant-id lift
  `ofFlatGraph (repG g)` with its canonical proper-forest cover — depending only on
  `propext`, `Classical.choice`, `Quot.sound` (no `sorry`, no project axiom). So the
  resolved coproduct/coassociativity are not conditional on an abstract payload: an
  explicit, provably-existent model is exhibited.

- **Phase 7** — `ResolvedHopfCertificate.lean`: an axiom-clean resolved Hopf
  structure **certificate**. It is *not* registered as a competing Mathlib typeclass
  instance (that would clash with the existing flat `Coalgebra`/`Bialgebra`/
  `HopfAlgebra` instance on the same carrier `HopfH`); instead it certifies that the
  explicitly inhabited boundary-resolved payload coproduct satisfies the Hopf laws —
  coassociativity, both counit laws, and both antipode axioms
  (`resolvedHopfStructureCertificate_holds`), with an explicit canonical family
  exhibited (`exists_resolvedHopfStructureCertificate`).

Design conclusions: the **algebra carrier stays flat `HopfH`** — no resolved
generator type, no native resolved `Fintype`, no ambient id-uniqueness assumption;
the resolved carrier is a *semantic witness layer* reached through `forget`. The
resolved-payload coproduct equals the flat coproduct as a linear map, satisfies the
full Hopf-structure law bundle, and is inhabited by a canonical lift — the only
thing deliberately *not* done is installing a duplicate typeclass instance on the
flat carrier.

R-4-superfull (identity-unique payload + native H5.8 reindexing architecture;
standalone modules, axiom-clean) — **✅ COMPLETE**:

> **The native H5.8 reindex is landed and axiom-clean.** The public theorem
> `h58_resolved_carrier_double_sum_reindex`
> (`GaugeGeometry/QFT/HopfAlgebra/ResolvedActualSigmaCover.lean`) proves the outer-forest
> double sum `∑_A innerImageSum A = ∑_A innerBranchSum A` — the H5.8 coassociativity
> reindex — entirely on the boundary-resolved carrier, with `#print axioms` =
> `[propext, Classical.choice, Quot.sound]`. **Both** boundary facades are discharged
> resolved-natively (no facade typeclass is instantiated), and the gated flat assembly
> `forestComponentSplitPhi_term_eq_of_split` is never exposed. The bullets below narrate
> the build-up; the **completion** paragraph at the end records what actually closed.

- The payload is upgraded to an *identity-unique* lift
  (`ResolvedHopfPayloadFamilyWithUniqueIds`, `ResolvedUniquePayloadModel.lean`), so the
  resolved boundary repairs apply to the actual payload graphs
  (`ResolvedBoundaryRepairCertificate`).
- A full resolved H5.8 reindexing architecture is built: a branch-map layer
  (`ResolvedBranchMapLayer`), its separated-cover classifier
  (`ResolvedIndexedBranchClassifier`), the finite sum-reindex
  (`ResolvedFiniteBranchMapLayer.sum_reindex`: `∑ image = ∑ forest + ∑ mixed`), and a
  bridge to the **concrete flat H5.8 tensor terms** (`ResolvedH58Bridge`, via thin
  public aliases of the flat σ-objects in `Coassoc.lean`).
- The architecture **reaches the concrete flat H5.8 tensor reindexing identity**
  (`ResolvedActualSigmaCover.concrete_sum_reindex`), and the remaining finite data package
  is now **constructed**: the per-outer-forest full-grain inner supply
  (`CanonicalOuterFullGrainInnerSupplyData.ofCoverOrigins`) plus the outer-forest sum
  (`ResolvedH58FullGrainOuterSkeleton.outer_sum_reindex`) assemble into the public
  `h58_resolved_carrier_double_sum_reindex`. Its fields (the finite branch-map layer, the
  resolved→flat index maps, the split-term agreement) are all σ-cover data, not boundary facades.
- The layer's `cover` (every quotient image is a forest or mixed branch image) is reduced
  *facade-free* to a single datum: the **mixed** case is structural
  (`exists_mixed_preimage_of_not_forest`), the **forest** case is built from a
  component-to-parent lift (`ResolvedForestCasePreimageData` →
  `forest_case_of_preimageData`), consolidated as `ResolvedForestCaseSupply.cover`. No flat
  `…PromotedExternalLegsLiftableModel` is used — the cover obstruction is now the single
  facade-free datum `ResolvedForestCaseSupply` (`resolvedParentRemnant` component-level
  surjectivity).
- **De-contraction section (constructed).** That `parentOf` lift is now *built*, not assumed:
  `parentOfQuotient` de-contracts a quotient subgraph `δ` to a parent `γ ⊇ Aout` (edge/leg
  submultiset preimages via the id-unique payload's `exists_le_map`), with
  `parentOfQuotient_remnant_eq : resolvedParentRemnant … (parentOfQuotient … δ) = δ` (a genuine
  section). Forest-branch images are single-parent (`singletonForestImageDataOfParent`); with
  the mixed side (`ResolvedMixedCarrierSupply`, star-avoiding subgraphs) they assemble via
  `CanonicalOuterInnerSupplyData.toCanonicalSupply` into a
  `CanonicalResolvedActualSigmaCoverSupply g`. The remaining inputs are the concrete finite
  quotient/mixed carriers, the resolved→flat index maps, and the split-term factorization — all
  σ-cover data. *(Build-up step; closed by the completion paragraph below.)*
- **Carrier import (Track S, in progress).** The machinery to import the flat σ-cover's finite
  carriers into the resolved coordinate is built: the contracted-graph forget bridge
  `forget_canonicalOuterContractedGraph` (whose keystone is the id-uniqueness payoff — `forget`
  is faithful across the complement subtraction — plus the star/retarget/vertices alignments),
  and a generic forget-subgraph lift `resolvedSubgraphOfForget` specialised to
  `liftFlatQuotientSubgraphToCres` / `liftFlatQuotientForestToCres` (flat quotient
  subgraphs/forests lift into the resolved contracted graph, with forget round-trips). Remaining:
  build the concrete carriers with CD/star facts, the resolved→flat coordinate dictionary, and
  `splitTerm_agreement` (the genuine boundary, not imported from flat). *(Build-up step; closed by
  the completion paragraph below.)*
- **The boundary reduced to one predicate `forest_term`.** The remaining datum is now a single
  named theorem. The boundary `ResolvedFlatH58Correspondence` (index dictionary + weight equality)
  is whittled down: `flatImageOf` is *constructed* (forget through the contracted-graph bridge +
  the actual↔rep transport); a carrier-based refactor removes an over-strong whole-type condition
  (the P2 pattern); the mixed half is killed (an origin projection); the forest boundary splits
  into a mechanical index round-trip (`forest_comm`) and a term factorization; and the term
  factorization branch-splits (`forest ⊕ mixed`, by `Sum.isLeft`) into `forest_term` + `mixed_term`.
  The reduction reached a single named datum **`forest_term`** — the forest-branch weight
  factorization (`∀ s, s.isLeft → splitChoiceTerm s = quotientTerm (splitPhi s)`).
- **Completion (R-4-full ∎).** `forest_term` turned out **canonical**, not a remaining gap: the
  whole term side is facade-free (`splitTermAgreementCanonical`). Both boundary facades are then
  discharged resolved-natively — facade #1 (forest insertion uniqueness) via
  `resolvedParentRemnant_injOn` / `ResolvedFullQuotientForestImageData.toImage_injective`, facade #2
  (σ-cover liftability) via `resolved_promotedComponent_externalLegs_le_plus` with the full-grain
  forest+mixed cover (`fullQuotientForestImageDataOfFlatSplit_comm`, `fullMixedImageDataOfFlatSplit_comm`,
  the origin-indexed covers). These assemble into the public, axiom-clean
  `h58_resolved_carrier_double_sum_reindex`.
  The **old flat `forestComponentSplitPhi` reindex stays facade-conditional by necessity, not by
  missing work**: its forest-branch injectivity consumes
  `ForestGraphInsertionUniquenessModel.parent_eq_of_remnant_eq` on the flat graph, which is *false*
  on the flat carrier (`flatEdgeRetarget_not_injective`) — the flat retarget forgets the boundary
  edge/leg id data the theorem needs, so no facade-free transport of the flat bijection exists. The
  boundary-resolved carrier restores exactly that id data, which is why the facade-free H5.8 reindex
  lives **there**, not in the flat statement.

All R-4-superfull modules depend only on `propext`/`Classical.choice`/`Quot.sound`; `Main`
is unaffected apart from the thin public aliases added to `Coassoc.lean`.

## Build

```bash
lake exe cache get      # fetch the Mathlib build cache
lake build Main         # builds Main.lean and, transitively, the whole development
```

`Main.lean` imports the top of the dependency chain and `#check`s the headline
certificates, so `lake build Main` both compiles everything and confirms the
dependency boundary.

## Documentation

- [`docs/CK_HOPF_FORMALIZATION_MAP.md`](docs/CK_HOPF_FORMALIZATION_MAP.md) —
  reader-facing map: what is proved, what is assumed, where the flat carrier
  fails, and how boundary resolution repairs it.
- [`docs/CK_HOPF_DEPENDENCY_GRAPH.md`](docs/CK_HOPF_DEPENDENCY_GRAPH.md) —
  developer/reviewer technical dependency DAG.

## Toolchain

Lean `leanprover/lean4:v4.29.0`, Mathlib `v4.29.0` (see `lean-toolchain` /
`lakefile.toml`).

## Acknowledgment
Translation＆Repository Makeing. Claude Opus 4.7 (Anthropic, May 25, 2026; https://claude.ai) was used to 
assist with English translation of the manuscript & Github Repository Making. The author is a non-native English speaker. 
All content, analysis, and interpretation are entirely the work of the author.

