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

Design conclusions: the **algebra carrier stays flat `HopfH`** — no resolved
generator type, no native resolved `Fintype`, no ambient id-uniqueness assumption;
the resolved carrier is a *semantic witness layer* reached through `forget`. What is
**not** yet packaged is a full unconditional resolved `HopfAlgebra` instance (the
antipode would be inherited from the carrier-independent convolution proof; only the
bialgebra/coalgebra packaging remains).

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

