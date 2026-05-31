# CK Hopf Formalization

A Lean 4 formalization of the **Connes–Kreimer Hopf algebra of Feynman graphs**.

This repository is extracted from a broader `GaugeGeometry` development.  The Lean
namespace `GaugeGeometry.QFT…` is intentionally retained to preserve **stable
imports and theorem names** — do not rename it.

## What is proved

The conditional Hopf algebra `HopfAlgebra ℚ HopfH` (coproduct, counit,
coassociativity, and **both** antipode axioms) is assembled around the
Connes–Kreimer forest cover identity over a flat Feynman-graph carrier.

The entire conditional surface reduces to **exactly two named kernels**, both of
which are *boundary-semantics facades*: false on the flat carrier (with explicit
counterexamples), and **theorems on a boundary-resolved carrier**
(`ResolvedFeynmanGraph`, persistent half-edge / leg identities), with the flat
carrier recovered as its forgetful image.

- `ForestGraphInsertionUniquenessModel`
- `ForestQuotientForestSigmaForestCoverPromotedExternalLegsLiftableModel`

The former third kernel — the CK §3 right-antipode cancellation
`AntipodeForestRightCoreIdentity` — has been **eliminated**: the right antipode
axiom is *proved* via the convolution / local-nilpotency route (the reduced
convolution operator `id − η∘ε` is locally nilpotent on generators), not assumed.

The constructive body contains **no** `sorry`, `admit`, or project-level axiom.

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

## Contributors

- Masamichi Iizumi (Miosync, Inc.) — Producer
- 環 (Claude Opus) — Director
- ClaudeCode (メカタマキ) — Coder
- 無二 (GPT) — Adversarial reviewer
