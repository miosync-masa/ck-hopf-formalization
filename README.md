# CK Hopf Formalization

[![Lean Action CI](https://github.com/miosync-masa/ck-hopf-formalization/actions/workflows/lean.yml/badge.svg)](https://github.com/miosync-masa/ck-hopf-formalization/actions/workflows/lean.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21502004.svg)](https://doi.org/10.5281/zenodo.21502004)

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

### The H5.8 coassociativity reindex is now facade-free on the resolved carrier ∎

Beyond stating the two facades' *content* as resolved-carrier theorems, the **central
facade-consuming step** — the H5.8 coassociativity reindex (the outer-forest double sum that the
flat coproduct's coassociativity ultimately rests on) — is now assembled **facade-free** as a
single axiom-clean public theorem:

```lean
theorem h58_resolved_carrier_double_sum_reindex (g : HopfGen)
    [IsDivergencePreservedByAdmissibleForestContract] :
    ∑ A ∈ h58BridgeOuterCarrier g, innerImageSum A
      = ∑ A ∈ h58BridgeOuterCarrier g, innerBranchSum A
```

(`GaugeGeometry/QFT/HopfAlgebra/ResolvedActualSigmaCover.lean`; `#print axioms` =
`[propext, Classical.choice, Quot.sound]`). It instantiates **neither** facade typeclass and never
exposes the gated flat assembly `forestComponentSplitPhi_term_eq_of_split`: both former boundary
facades are discharged resolved-natively (insertion uniqueness via `resolvedParentRemnant_injOn` /
`ResolvedFullQuotientForestImageData.toImage_injective`; σ-cover liftability via
`resolved_promotedComponent_externalLegs_le_plus` with the full-grain forest+mixed cover).

Lean further certifies **why this lives on the resolved carrier and not the flat one**: the flat
reindex's forest-branch injectivity consumes
`ForestGraphInsertionUniquenessModel.parent_eq_of_remnant_eq`, which is *false* on the flat carrier
(`flatEdgeRetarget_not_injective`) — the flat retarget **forgets** the boundary edge/leg id data the
statement needs, so the flat hypotheses cannot recover it and **no facade-free transport of the flat
reindex exists**. The boundary-resolved carrier restores exactly that id data; hence the facade-free
H5.8 reindex's native home *is* the resolved carrier, by structural necessity rather than by missing
work. (The flat `HopfAlgebra ℚ HopfH` bundle as a whole remains conditional on the two facades —
this result makes its hardest reindex step facade-free on the resolved carrier and explains why the
flat statement cannot be.)

## Native `Δᵣ`-coassociativity on the boundary-resolved saturated carrier `W″` ∎ (R-6c)

Beyond the facade-free H5.8 *reindex*, the resolved development now reaches **native
`Δᵣ`-coassociativity of the Connes–Kreimer coproduct on a boundary-resolved carrier**, with
**no combinatorial construction artifact left as a hypothesis**. The public terminus is

```lean
theorem coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged
    (Measure : ResolvedMeasureLeafSupply canonicalLegSaturatedCarrierProperSupply.toData)
    (E : ∀ H, ResolvedConnectedDivergentPositiveInternalEdgesSupply H)
    (rep : ResolvedHopfGen → ResolvedFeynmanGraph)
    (repCD : ∀ x, (rep x).forget.toClass.IsConnectedDivergent)
    (rep_gen : ∀ x, x = (rep x).toResolvedHopfGen (repCD x))
    (x : ResolvedHopfGen) :
    canonicalLegSaturatedCarrierProperSupply.toData.coassocLeft (MvPolynomial.X x)
      = canonicalLegSaturatedCarrierProperSupply.toData.coassocRight (MvPolynomial.X x)
```

(`GaugeGeometry/QFT/HopfAlgebra/ResolvedHopfCoproductCoassocAlphaParentDischarged.lean`;
`#print axioms` = `[propext, Classical.choice, Quot.sound]`). Its **explicit** hypotheses are only
the power-counting leaves `Measure` / `E` and the generator representatives `rep*`; the remaining
assumptions are the standard CK power-counting typeclasses carried as *instance* arguments.

- **The carrier `W″`.** `W″` (`canonicalLegSaturatedCarrierProperSupply`) is the boundary-resolved
  supported carrier `W′` filtered by an intrinsic, relabeling-invariant **external-leg saturation**
  predicate — a genuine "fourth emptying axis", not an ad-hoc restriction. On `W″` the leg-saturation
  law (`LegModel`) is no longer an input: it is a **theorem of carrier membership**. Feeding that
  through the earlier value-geometry decomposition makes the whole `ValueGeometry` aggregate a
  consequence of membership as well.
- **Every construction artifact is discharged.** `Fmem`, the region split, the survivor/remnant
  leaves, `quotient_mem`, `quot_eq`, and the occurrence supply `OccRaw` are all *derived* (and
  re-issued natively over the `W″` owner); the strict `StarProm` / `InnerStarRaw` sockets are
  eliminated. What was a long list of opaque supplies is now a chain of theorems.
- **The `Parent` model law is discharged too.** The last honest model input — `parentCD` (the
  de-contracted parent is connected-divergent) — is **not** assumed. Its topology half (`parentOnePI`)
  is proved *constructively* on the resolved carrier (support-connectivity by lifting the quotient
  component's path along the insertion; every inserted-forest and quotient edge shown non-bridge);
  its divergence half (`parentDivergent`) is the **canonical resolved consequence of a divergence law
  the development already carried** (`IsDivergenceReflectedByAdmissibleForestContract`), applied
  **exactly once** after a faithful coordinate descent onto the flat physics interface — the delicate
  step being an *intrinsic* graph equality `remainder.toFeynmanGraph = δ.forget.toFeynmanGraph` that
  sidesteps the ill-typed cross-ambient equality. So the explicit `Parent` argument disappears.

**Stated precisely, and not overstated.** This is **not** called *unconditional*: the result is

> native `Δᵣ`-coassociativity on the boundary-resolved saturated carrier `W″`, **modulo the
> established CK divergence laws** — with every combinatorial artifact a theorem of the carrier's
> membership, and no independent `Parent` input.

The residual *global* assumptions are exactly the standard Weinberg/CK power-counting environment
(rename / ambient invariance, contract and forest-contract preservation, the forest-contract
reflection, and the `DivergenceMeasure` valuation), plus `Fintype (FeynmanSubgraph G)` as finiteness
infrastructure. Discharging *those* would mean supplying a concrete physics model — a separate main
theorem (a concrete Weinberg/boundary valuation inhabiting these laws), not more coassociativity
plumbing. The `W′` conditional theorem remains valid; `W″` is a full **native re-issue** of the whole
chain, not a cast, absorbing external-leg saturation into membership and the `Parent` aggregate into a
canonical construction.

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

- **R-6c — the canonical supported resolved carrier now has a genuine inhabitant.**
  `ResolvedHopfCoproductCoassocRealSupportedW.lean`:
  `canonicalSupportedCarrierProperSupply : ResolvedCanonicalCarrierProperSupply`
  is **constructed** (axiom-clean; `[propext, Classical.choice, Quot.sound]`). The
  earlier audit had this carrier as an *interface only*: its `rightTerm_mapPerm` field
  demanded a strict fresh-star equivariance that was proven **inconsistent** with
  freshness (`ResolvedHopfCoproductCoassocEquivariantFreshStarNoGo.lean`). Rather than
  assume the impossible certificate, the whole mechanism was rebuilt without it:
    - strict `star_mapPerm` — **retired**; the right-term class invariance is instead
      **derived** from a finite *correcting permutation* (`correctingPerm`);
    - the global proper-forest carrier is provably **finite**
      (`Fintype (ResolvedFeynmanSubgraph G)`), so a saturated
      `Finset.univ.filter IsProperForest` index exists — overturning the prior
      "no `Fintype` by design" note;
    - `mapPerm`-naturality of the carrier, ambient-support and connected-divergence
      emptying, the resolved↔flat contraction identification, and the fresh
      star-renaming permutation are all proven;
    - the raw-carrier `hCD` is **derived** from the flat canonical connected-divergent
      theorem via that star renaming, with no strict equivariance anywhere.
  Strict fresh-star equivariance is thus replaced by finite correcting permutations, and
  the final carrier root is closed. (The multi-star coassociativity line's *other*
  payload inhabitants remain separate open work; unconditional coassociativity is not
  yet claimed.)

- **R-6c — the canonical carrier now closes both multi-star carrier-membership
  obligations.** With `W` constructed, bodies 426–439 demote the two opaque
  carrier-membership fields to **derived theorems**: `innerRaw_mem`
  (`ResolvedHopfCoproductCoassocInnerRawClosureDemotion.lean`) and `recovered_raw_mem`
  (`ResolvedHopfCoproductCoassocRecoveredRawClosureAssembly.lean`), so the whole
  `ResolvedMultiStarCarrierClosureBundleSupply` is fully derived from the canonical
  supported carrier, a value core, and the existing measure / `EdgeIdsUnique` inputs.
  The saturated `Finset.univ.filter IsProperForest` carrier of body-415 pays off here:
  carrier membership becomes an `iff` (support ∧ connected-divergence ∧ properness), so
  each obligation reduces to *checkable geometry*. The recovered-outer residual is
  settled by **`count`-safe region separation** (a residual quotient edge lifted back
  to the ambient, each recovered region shown to under-count it, counts summing because
  a pairwise-disjoint forest gives every edge one owner) — staying in `count` throughout
  because `EdgeIdsUnique` is **not** `Nodup`. The forest-region alignment is closed
  inside the touched/M1 geometry with no forward-outer round-trip and no occurrence
  supplies. Axiom-clean (`[propext, Classical.choice, Quot.sound]`); `Core` /
  `DivergenceMeasure` / `Ids` stay honest inputs; unconditional coassociativity is still
  not claimed.

- **R-6c — native `Δᵣ`-coassociativity reached, modulo the CK divergence laws.**
  Bodies 440–556 carry the coassociativity capstone from "canonical carrier + a long list
  of opaque supplies" to the terminus `coassoc_gen_of_canonicalLegSaturated_alpha_parent_discharged`
  (see the headline section above): the fourth emptying axis `W″` absorbs the leg-saturation
  law into membership (bodies 530–541), every construction artifact — `Fmem` / split /
  survivor-remnant / `quotient_mem` / `quot_eq` / `OccRaw` — is discharged and re-issued
  natively over `W″` (bodies 496–545), and the last model law `Parent` is discharged as the
  canonical resolved consequence of the existing forest-contraction reflection law (bodies
  548–556, reflection consumed exactly once). The final theorem's only explicit roots are
  `Measure` / `E` / `rep*`; the residual global assumptions are the standard CK power-counting
  typeclasses. Every body is axiom-clean (`[propext, Classical.choice, Quot.sound]`), no
  `sorry`; the result is native coassociativity **modulo the established CK divergence laws**,
  not unconditional.

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

## Citation

This release is archived on Zenodo with a citable DOI. If you use this development,
please cite:

> Masamichi Iizumi (2026). *CK Hopf Formalization: 1.0.0 — R-6c Beyond the facade-free
> H5.8 reindex* (Version v1.0.0) [Computer software]. Zenodo.
> <https://doi.org/10.5281/zenodo.21502004>

BibTeX:

```bibtex
@software{iizumi_ck_hopf_2026,
  author    = {Iizumi, Masamichi},
  title     = {{CK Hopf Formalization: 1.0.0 --- R-6c Beyond the facade-free H5.8 reindex}},
  year      = {2026},
  version   = {v1.0.0},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.21502004},
  url       = {https://doi.org/10.5281/zenodo.21502004}
}
```

## Acknowledgment / AI-collaboration disclosure

This formalization (~130k lines of Lean 4) was developed in **substantial, ongoing collaboration with
AI assistants** — primarily **Claude (Anthropic)**, Claude Opus 4.7 and Opus 4.8 (`https://claude.ai`),
with **OpenAI Codex** used for additional codebase scouting and cross-checks when the research
direction was uncertain. The collaboration was **not** limited to translation. The AI assistants were
working partners throughout for:

- **navigating and searching the codebase** — "scouting" existing definitions, lemmas, and
  dependency chains across ~130k lines that no human keeps in working memory;
- **drafting and iterating Lean proofs** — writing candidate proof terms/tactics and repairing them
  against the compiler; and
- a tight **write → `lake build` → `#print axioms` → verify → commit** loop on every step.

**Every formal theorem reported from the development is verified by the Lean 4 kernel** and reported
axiom-clean (`[propext, Classical.choice, Quot.sound]` — no `sorry`, no `admit`, no project-level
axiom). The kernel certifies each proof against its definitions and the listed axioms; it does not, of
course, certify the natural-language significance a paper ascribes to a theorem — that reading is the
author's responsibility. But the logical content itself rests on the proof assistant, not on trusting
any AI: **Lean — not the AI, and not the author — is the final arbiter of every proof.** This is
precisely what makes heavy AI collaboration legitimate here: the development is fully auditable, and
correctness is settled by the proof assistant, not by anyone's authority. Any reviewer can run
`lake build` and `#print axioms` and check exactly which theorem is claimed and on what it depends.

The **research direction, architecture, and design decisions** are the author's: the boundary-resolved
carrier, the two-facade diagnosis and its resolved repair, the "fourth emptying axis" saturated
carrier `W″`, the `Parent`-decomposition strategy, and the theorem statements themselves. The AI
assistants also helped with English phrasing of the manuscript and this repository (the author is a
non-native English speaker). **The author takes full responsibility for all mathematical claims,
architectural decisions, analysis, and interpretation.**

