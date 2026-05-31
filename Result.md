# Result.md — GaugeGeometry Formalization Closeout

**Project:** GaugeGeometry — formal verification of Platonic-geometric gauge structure and QFT layer separation in Lean 4
**Status:** Core + Optional-excluded tasks closed (2026-04-21)
**Build:** `lake build` → exit 0
**`sorry` count:** 0

---

## 1. Headline theorems

Three top-level statements live in [GaugeGeometry/Main.lean](GaugeGeometry/Main.lean), stratified by what they require.

### 1.1 `geometric_main`

Pure-geometry conjunction:

1. Platonic integer set coincides with the Schläfli coordinate set,
2. `(60, 30, 8)` is the unique floor candidate in the finite arithmetic space,
3. `adjointDim 3 = 8`, and `N = 3` is the unique `N ≥ 2` with this property.

**Axiom footprint:** `propext, Quot.sound` — no empirical input, no model choice.

### 1.2 `unification_physical_separation`

Algebraic unification identity evaluated on the floor tuples:

- `(60, 30, 8)` fails the identity (physically correct floor is *not* one-point unified),
- `(15, 8, 3)` satisfies the identity but is physically rejected.

**Axiom footprint:** `propext, Quot.sound`.

### 1.3 `physical_consistency`

Bundles both structural and PDG-conditional closures:

- **ℚ side (structural):** for every nonzero `k : ℚ`, the canonical weak/color witness recovers the geometric integer `3` via the ratio of ratios, matching `adjointDim 3 - 5`.
- **ℝ side (PDG-conditional):** under the hypothesis that the PDG generation factor satisfies the real channel-factorization pattern for `N_c = 3` with nonzero second-generation entry, the real ratio of ratios equals `3`.

**Axiom footprint:** `propext, Classical.choice, Quot.sound, Axioms.pdgObservationData`. No MSSM or gauge-choice axiom needed — the canonical witness discharges that side internally.

---

## 2. Theorem-status snapshot

| Theorem | Status | Location |
|---|---|---|
| Theorem 1 — MSSM 1-loop β coefficients | Stage 2 (assembly from axioms) | [QFT/Representation/BetaCoefficients.lean](GaugeGeometry/QFT/Representation/BetaCoefficients.lean) |
| Theorem 2 — Integrated 1-loop RG running | complete | [QFT/Analytic/RGFlow.lean](GaugeGeometry/QFT/Analytic/RGFlow.lean), [QFT/Analytic/OneLoopRunning.lean](GaugeGeometry/QFT/Analytic/OneLoopRunning.lean) |
| Theorem 3 — Direct-product sector factorization | complete | [QFT/Representation/SectorFactorization.lean](GaugeGeometry/QFT/Representation/SectorFactorization.lean) |
| Theorem 4 — Mass-ratio decomposition from sector weights | complete | [Applications/MassRatioDecomposition.lean](GaugeGeometry/Applications/MassRatioDecomposition.lean) |
| Geometric main | complete | [Main.lean](GaugeGeometry/Main.lean) |
| Physical consistency | complete | [Main.lean](GaugeGeometry/Main.lean) |

---

## 3. Module-by-module inventory

### 3.1 Core layer — shared interfaces, no proofs

- [Core/Sector.lean](GaugeGeometry/Core/Sector.lean) — `GaugeSector`, `SectorWeights`, accessors + extensionality
- [Core/GaugeChoice.lean](GaugeGeometry/Core/GaugeChoice.lean)
- [Core/MatterContent.lean](GaugeGeometry/Core/MatterContent.lean)
- [Core/ObservationData.lean](GaugeGeometry/Core/ObservationData.lean)
- [Core/ModelSpec.lean](GaugeGeometry/Core/ModelSpec.lean)
- [Core/ExternalInputs.lean](GaugeGeometry/Core/ExternalInputs.lean)

### 3.2 Axioms layer — residual external inputs

- [Axioms/GaugeGroupChoice.lean](GaugeGeometry/Axioms/GaugeGroupChoice.lean) — `SU(3) × SU(2) × U(1)` as model choice
- [Axioms/MSSMChoice.lean](GaugeGeometry/Axioms/MSSMChoice.lean) — MSSM matter content + Stage 2 Casimir/Dynkin numerical inputs
- [Axioms/PDGInputs.lean](GaugeGeometry/Axioms/PDGInputs.lean) — `pdgObservationData`, `pdgAlphaS`, `pdgQuarkMass`, positivity axioms

### 3.3 Geometric zone — pure geometry / arithmetic

- [Geometric/Platonic/Schlafli.lean](GaugeGeometry/Geometric/Platonic/Schlafli.lean) — `SchlafliPair`, finiteness, enumeration
- [Geometric/Platonic/Classification.lean](GaugeGeometry/Geometric/Platonic/Classification.lean) — `platonic_bijection`
- [Geometric/Platonic/IntegerSet.lean](GaugeGeometry/Geometric/Platonic/IntegerSet.lean) — `{3,4,5}`, `{3,5}`, `{2,3,5}` + `platonic_integers_from_classification`
- [Geometric/Arithmetic/CandidateSpace.lean](GaugeGeometry/Geometric/Arithmetic/CandidateSpace.lean)
- [Geometric/Arithmetic/FloorValues.lean](GaugeGeometry/Geometric/Arithmetic/FloorValues.lean) — `unique_floor_structure` (uniqueness of `(60, 30, 8)`)
- [Geometric/GroupDimension/AdjointFormula.lean](GaugeGeometry/Geometric/GroupDimension/AdjointFormula.lean) — `adjointDim N = N^2 - 1`
- [Geometric/GroupDimension/FromEight.lean](GaugeGeometry/Geometric/GroupDimension/FromEight.lean) — `adjoint_dim_eight_iff_three`
- [Geometric/GroupDimension/ColorEmergence.lean](GaugeGeometry/Geometric/GroupDimension/ColorEmergence.lean) — `three_is_consistent`

### 3.4 QFT / Representation layer

- [QFT/Representation/GaugeProduct.lean](GaugeGeometry/QFT/Representation/GaugeProduct.lean) — `GaugeIndex := Fin 3`, `u1Index`, `su2Index`, `su3Index`, `sectorOfIndex`, `indexOfSector`
- [QFT/Representation/SectorFactorization.lean](GaugeGeometry/QFT/Representation/SectorFactorization.lean) — **Theorem 3** `direct_product_sector_factorization`, `electroweakWeight`, `fullWeight`
- [QFT/Representation/CasimirData.lean](GaugeGeometry/QFT/Representation/CasimirData.lean) — sector-indexed `ℚ` Casimir container
- [QFT/Representation/DynkinIndex.lean](GaugeGeometry/QFT/Representation/DynkinIndex.lean) — Dynkin-index containers
- [QFT/Representation/BetaCoefficients.lean](GaugeGeometry/QFT/Representation/BetaCoefficients.lean) — **Theorem 1 Stage 2** `mssm_one_loop_beta_coefficients`, `assembledBeta`, `mssmBetaCoefficients_eq_assembly`, `betaTriple`, `betaTriple_b1/b2/b3`

### 3.5 QFT / Combinatorial layer (research-strength)

- [QFT/Combinatorial/FeynmanGraphs.lean](GaugeGeometry/QFT/Combinatorial/FeynmanGraphs.lean) — labeled multigraph, `Incident`, `Adjacent`, `Reachable`, `loopNumber`, `IsOneLoopStrong`, sector-indexed edge/leg counts
- [QFT/Combinatorial/OneLoopGraphs.lean](GaugeGeometry/QFT/Combinatorial/OneLoopGraphs.lean) — weak/strong 1-loop predicates, tadpole, strong → weak
- [QFT/Combinatorial/WickExpansion.lean](GaugeGeometry/QFT/Combinatorial/WickExpansion.lean)
- [QFT/Combinatorial/RenormalizationBridge.lean](GaugeGeometry/QFT/Combinatorial/RenormalizationBridge.lean) — `CombinatorialBridge` interface
- [QFT/Combinatorial/SupportGraph.lean](GaugeGeometry/QFT/Combinatorial/SupportGraph.lean) — `toSimpleGraph`, connected components
- [QFT/Combinatorial/SubGraph.lean](GaugeGeometry/QFT/Combinatorial/SubGraph.lean) — `FeynmanSubgraph`, `Forest`, `DivergenceMeasure`
- [QFT/Combinatorial/Permutation.lean](GaugeGeometry/QFT/Combinatorial/Permutation.lean) — `Equiv.Perm VertexId` action, invariances, `MulAction` instance
- [QFT/Combinatorial/GraphIsomorphism.lean](GaugeGeometry/QFT/Combinatorial/GraphIsomorphism.lean) — `FeynmanGraph.IsIso`, `Setoid`, `FeynmanGraphClass` quotient
- [QFT/Combinatorial/ForestFormula.lean](GaugeGeometry/QFT/Combinatorial/ForestFormula.lean) — light Connes–Kreimer `R_operation`, `Forest.contribution`

### 3.6 QFT / Analytic layer

- [QFT/Analytic/RGFlow.lean](GaugeGeometry/QFT/Analytic/RGFlow.lean) — `GaugeIndex`, `BetaCoefficients`, `AlphaInvAt`, `oneLoopSlope`, `oneLoopCorrection`, `alphaInvRunning`, **`integrated_one_loop_rg_running`**, `alphaInvRunning_at_reference`, `alphaInvRunning_sub_reference`
- [QFT/Analytic/OneLoopRunning.lean](GaugeGeometry/QFT/Analytic/OneLoopRunning.lean) — MSSM-canonicalized `mssmAlphaInvRunning`, **`integrated_one_loop_running`**, sector-wise sign lemmas `oneLoopSlope_u1/su2_positive`, `oneLoopSlope_su3_negative`, sectorwise directional inequalities
- [QFT/Analytic/LogIdentities.lean](GaugeGeometry/QFT/Analytic/LogIdentities.lean) — `log_ref_zero`, `log_ratio_identity`, `log_ratio_swap_neg`, `log_ratio_antisymm`
- [QFT/Analytic/ThresholdCorrections.lean](GaugeGeometry/QFT/Analytic/ThresholdCorrections.lean) — `ThresholdProfile`, `alphaInvRunning_with_threshold`, `_trivial`, `_sub_bare`, `_add` matching identities

### 3.7 Applications layer

- [Applications/Common.lean](GaugeGeometry/Applications/Common.lean) — shared `abbrev` block (`GaugeIndex`, `AlphaInvAt`, sector indices, `mssmBetaCoefficients`)
- [Applications/UnificationRatio.lean](GaugeGeometry/Applications/UnificationRatio.lean) — `unificationConsistency`, `unification_equivalence`, `target_not_unification_consistent`, `nontrivial_unification_solution`
- [Applications/QuarkMassRatios.lean](GaugeGeometry/Applications/QuarkMassRatios.lean) — `GenerationFactor`, `f2`, `f3`, `ratioOfRatios`, `pdgUpDownRatio`, `pdgGenerationFactor`, `pdgGenerationFactor_zero`
- [Applications/MassRatioDecomposition.lean](GaugeGeometry/Applications/MassRatioDecomposition.lean) — **Theorem 4** `mass_ratio_decomposition_from_sector_weights`, `massRatioFromSectorWeights_eq_factorized`; `GenerationSectorWeights`, `WeakUniformColorScaled`, `generationFactorFromSectorWeights_shape`, `_second_nonzero`; `canonicalWeakUniformColorScaled` + `_pattern` + `exists_weakUniformColorScaled`; **multiplicative form** `alphaRunning`, `multiplicativeRunningFactor`, `multiplicativeRunningMassRatio`, `multiplicativeRunningFactor_at_reference`, `multiplicativeRunningMassRatio_at_reference`, `alpha_ratio_eq_inv_ratio`
- [Applications/QuarkConsistency.lean](GaugeGeometry/Applications/QuarkConsistency.lean) — `ChannelFactorizationHolds`, `ratio_of_ratios_recovers_N`, `channel_factorization_from_mass_ratio_decomposition`, `ratio_of_ratios_recovers_N_from_mass_ratio_decomposition`, `ratio_of_ratios_matches_geometric_three`, `geometric_physical_consistency`, `ratio_of_ratios_canonical_eq_three`, `geometric_physical_consistency_canonical`; **ℝ version** `GenerationFactorReal`, `ratioOfRatiosReal`, `ChannelFactorizationHoldsReal`, `ratio_of_ratios_recovers_N_real`, `pdg_channel_factorization_implies_three`
- [Applications/AlphaSPrediction.lean](GaugeGeometry/Applications/AlphaSPrediction.lean) — `alpha3InvPrediction`, `alphaSPrediction`, `alpha3InvPrediction_eq_mssm_formula`, reference collapse; sector-indexed `alphaInvPrediction`, `_at_reference`, `_sub_reference`; **floor closure** `floorInitialAlphaInv`, `floorAlphaInvPrediction`, `floorAlpha3InvPrediction`, `floorAlphaSPrediction`, `floorAlpha3InvPrediction_at_reference`, `floorAlpha3InvPrediction_eq_mssm_formula`

### 3.8 Top level

- [Main.lean](GaugeGeometry/Main.lean) — `geometric_main`, `unification_physical_separation`, `physical_consistency`

---

## 4. Key-theorem proof sketches

### 4.1 `geometric_main`

Trivial conjunction of three pre-existing theorems:
1. `platonic_integers_from_classification` (Schläfli enumeration ↔ `{3,4,5}`),
2. `unique_floor_structure` (finite search over the candidate space),
3. `three_is_consistent` (adjoint-dimension calculation + `decide`).

### 4.2 `integrated_one_loop_rg_running` (Theorem 2)

The one-loop inverse-coupling running
`α⁻¹(μ) = α⁻¹(μ₀) - (b / 2π) log(μ / μ₀)` is written directly as the *definition* of `alphaInvRunning`, and the theorem is `funext` + `rfl`-level unfolding via `oneLoopSlope` and `oneLoopCorrection`. The MSSM specialization `integrated_one_loop_running` instantiates `b = betaTriple` and rewrites through `simpa`.

### 4.3 `direct_product_sector_factorization` (Theorem 3)

Definitional: `fullWeight w = electroweakWeight w * w.color` by construction, and `electroweakWeight w = w.weak * w.hypercharge`. Proof is `rfl`-level under `unfold`.

### 4.4 `mssm_one_loop_beta_coefficients` (Theorem 1, Stage 2)

The MSSM coefficient triple `(33/5, 1, -3)` is rebuilt by `assembledBeta` from sector-wise Casimir/Dynkin axioms (`mssmAdjointCasimir`, `mssmMatterDynkin`). The bridging theorem `mssmBetaCoefficients_eq_assembly` equates the axiomatized `betaTriple` with the assembled value; the final statement is the conjunction `betaTriple_b1 ∧ betaTriple_b2 ∧ betaTriple_b3`, each a numerical equality closed by `simp`/`decide`.

### 4.5 `mass_ratio_decomposition_from_sector_weights` (Theorem 4)

`massRatioFromSectorWeights w := weakFactor w * colorFactor w`. The decomposition theorem is definitionally true. The "factorized" variant composes it with Theorem 3 to re-express `fullWeight` as `electroweakWeight * color`.

### 4.6 `WeakUniformColorScaled` witness

`canonicalWeakUniformColorScaled k N_c` is an explicit `Fin 3 → SectorWeights` with
- generation 0: `(1, 1, 1)`,
- generation 1: `(1, k, 1)`,
- generation 2: `(1, k, N_c)`.
Pattern verification is six `simp` goals unfolding `weakFactor`, `colorFactor`, and `electroweakWeight`. `exists_weakUniformColorScaled` packages this into the existence statement.

### 4.7 `ratio_of_ratios_recovers_N` and `_real`

Destructure the factorization hypothesis to obtain `k`. Rewrite `f 1 = k`, `f 2 = k · N_c`, then `field_simp` using `k ≠ 0` (forced by `f 1 ≠ 0`).

### 4.8 `geometric_physical_consistency_canonical`

Chain: `canonicalWeakUniformColorScaled k 3` → `WeakUniformColorScaled _ k 3` (via `canonicalWeakUniformColorScaled_pattern`) → `ChannelFactorizationHolds _ 3` (via `channel_factorization_from_mass_ratio_decomposition`) → `ratio_of_ratios = 3` (via `ratio_of_ratios_recovers_N`) → match against `adjointDim 3 - 5 = 3` (by `decide`).

### 4.9 Multiplicative running (direction Y)

- `alphaRunning := 1 / alphaInvRunning`, so `α(μ) / α(μ₀) = α⁻¹(μ₀) / α⁻¹(μ)` by `field_simp` under mutual non-vanishing (`alpha_ratio_eq_inv_ratio`).
- `multiplicativeRunningFactor γ _ μ μ₀ i := (α(μ) / α(μ₀)) ^ γ` using `Real.rpow`. Reference collapse is `1 / α₀ i ≠ 0 ⇒ (α₀/α₀)^γ = 1^γ = 1` via `Real.one_rpow`.

### 4.10 `physical_consistency`

Two conjuncts, each delegated:
- ℚ side: `∀ k ≠ 0, ratio_of_ratios(generationFactorFromSectorWeights(canonical k 3)) = adjointDim 3 - 5` via `geometric_physical_consistency_canonical`.
- ℝ side: `pdg_channel_factorization_implies_three`, which is itself `ratio_of_ratios_recovers_N_real` applied to `pdgGenerationFactor`.

The PDG factorization hypothesis is an argument, not an axiom.

---

## 5. Dependency DAG

Layer direction (↓ = "depends on"):

```
                       Main
                        │
            ┌───────────┼───────────────────────────┐
            │           │                           │
        Applications ───┼───────────────────────┐   │
            │           │                       │   │
   ┌────────┼──────┐    │                       │   │
   │        │      │    │                       │   │
 Axioms  QFT/      │  (Applications/Common,     │   │
         Analytic  │   shared abbrevs)          │   │
   │        │      │                            │   │
   │    QFT/Representation                      │   │
   │        │                                   │   │
   │    Geometric                               │   │
   │        │                                   │   │
   └──── Core ─────────────────────────────────┘   │
            │                                       │
            └───────────────────────────────────────┘
```

### 5.1 Applications-layer internal DAG

```
Applications/Common
        │
        ├──────────────┬──────────────────┐
        ▼              ▼                  ▼
   AlphaSPrediction   MassRatioDecomposition
                              │
                              │ (imported)
                              ▼
                      QuarkConsistency
                              │
                              ▼
                           Main
```

Also:
```
QuarkMassRatios ──▶ MassRatioDecomposition, QuarkConsistency
UnificationRatio ──▶ Main (separate branch)
```

### 5.2 Theorem-level DAG (essential edges)

```
        Geometric/Platonic.IntegerSet          Geometric/FloorValues
                        │                              │
                        └────────────┬─────────────────┘
                                     │
                                     ▼
                  Geometric/ColorEmergence.three_is_consistent
                                     │
                                     ▼
                              geometric_main
                                     │
                                     ▼
     ┌───────────────────────────────┼─────────────────────────────┐
     │                               │                             │
     │    QFT/Representation.SectorFactorization (Theorem 3)       │
     │                               │                             │
     │                               ▼                             │
     │        Applications.massRatioFromSectorWeights_eq_factorized│
     │                               │                             │
     │                               ▼                             │
     │                Applications.canonicalWeakUniformColorScaled │
     │                     (witness + pattern)                     │
     │                               │                             │
     │                               ▼                             │
     │      Applications.channel_factorization_from_mass_ratio_decomposition
     │                               │                             │
     │                               ▼                             │
     │           Applications.ratio_of_ratios_recovers_N          │
     │                               │                             │
     │                               ▼                             │
     │     Applications.geometric_physical_consistency_canonical   │
     │                               │                             │
     │                               └───────┐                     │
     │                                       ▼                     │
     │                            Main.physical_consistency (ℚ side)
     │                                       ▲                     │
     │        ┌──────────────────────────────┘                     │
     │        │                                                    │
     │    Axioms.pdgObservationData                                │
     │        │                                                    │
     │        ▼                                                    │
     │   Applications.pdgGenerationFactor                          │
     │        │                                                    │
     │        ▼                                                    │
     │   Applications.ChannelFactorizationHoldsReal (definition)   │
     │        │                                                    │
     │        ▼                                                    │
     │   Applications.ratio_of_ratios_recovers_N_real              │
     │        │                                                    │
     │        ▼                                                    │
     │   Applications.pdg_channel_factorization_implies_three      │
     │        │                                                    │
     │        └───────┐                                            │
     │                ▼                                            │
     │     Main.physical_consistency (ℝ side)                      │
     │                                                             │
     └─────────────────────────────────────────────────────────────┘
```

Supporting analytic chain (feeds Theorem 2, not on the critical path of `physical_consistency`):

```
QFT/Representation.BetaCoefficients (Theorem 1 Stage 2)
              │
              ▼
QFT/Analytic.RGFlow.integrated_one_loop_rg_running (Theorem 2)
              │
              ▼
QFT/Analytic.OneLoopRunning.integrated_one_loop_running (MSSM specialization)
              │
              ▼
QFT/Analytic.ThresholdCorrections (matching identities, opt-in)
              │
              ▼
Applications/AlphaSPrediction.floorAlphaSPrediction (floor closure)
```

Direction-Y multiplicative-form chain (parallel to linear form):

```
Applications/MassRatioDecomposition.alphaRunning
              │
              ▼
Applications/MassRatioDecomposition.alpha_ratio_eq_inv_ratio
              │
              ▼
Applications/MassRatioDecomposition.multiplicativeRunningFactor
              │
              ▼
Applications/MassRatioDecomposition.multiplicativeRunningMassRatio
              │
              ▼
Applications/MassRatioDecomposition.multiplicativeRunningMassRatio_at_reference
```

---

## 6. Axiom audit

### 6.1 `geometric_main`

```
propext, Quot.sound
```

No model choice, no empirical input. Task v3 §13 target met.

### 6.2 `unification_physical_separation`

```
propext, Quot.sound
```

### 6.3 `physical_consistency`

```
propext, Classical.choice, Quot.sound, Axioms.pdgObservationData
```

Only dependency beyond Lean/Mathlib standard axioms is the *existence* of `pdgObservationData`. The empirical factorization hypothesis is supplied as a theorem argument, never axiomatized.

### 6.4 Theorem-1–4 package

| Theorem | Additional axioms beyond standard |
|---|---|
| Theorem 1 (Stage 2) | `mssmAdjointCasimir`, `mssmMatterDynkin` + MSSM sector-wise numerical axioms |
| Theorem 2 | none |
| Theorem 3 | none |
| Theorem 4 | none |

---

## 7. What is deliberately *not* formalized

Tracked in Task v3 §1.4 and §18.3:

- SM gauge group choice as forced by nature (it is a model choice, living in `Axioms/GaugeGroupChoice.lean`).
- MSSM as true (model specification, `Axioms/MSSMChoice.lean`).
- Constructive QFT from a defined path integral.
- Full BPHZ / non-perturbative renormalization.
- Flavor-sector global-fit numerics beyond the ℝ-level conditional theorem in `QuarkConsistency`.
- **Theorem 1 Stage 3** — replacing the axiom-level Casimir/Dynkin inputs with a `CombinatorialBridge`-assembled derivation. Intentionally postponed as research-strength extension.

---

## 8. Build status

- `lake build` (2026-04-21): exit 0, `Build completed successfully`.
- Pinned Mathlib: `v4.29.0` (per `lakefile.toml`).
- No `sorry` in `GaugeGeometry/`.
- No linter warnings at closeout.

---

## 9. File count

- Core layer: 6 files
- Axioms layer: 3 files
- Geometric zone: 9 files
- QFT / Representation: 5 files
- QFT / Combinatorial: 9 files
- QFT / Analytic: 4 files
- Applications: 7 files
- Top level: 1 file

**Total: 44 Lean files** (excluding legacy `Physical/` re-export shims and the `Axioms.lean` umbrella).
