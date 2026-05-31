# Task.md: Formal Verification of Platonic-Geometric Gauge Structure and QFT Layer Separation in Lean 4

**Project:** GaugeGeometry — formal proofs supporting the discrete geometric framework for Standard Model / MSSM gauge structure and mass-ratio organization

**Producer:** Masamichi Iizumi (Miosync, Inc.)  
**Target Environment:** Lean 4 + Mathlib (latest stable)  
**Expected scale:** ~35–50 files, ~4,500–7,000 lines, ~120–180 theorems  
**Status:** Planning / architecture revision phase

---

## 1. Purpose and Design Principle

### 1.1 Central claim

The companion paper reports a broad empirical pattern: selected Standard Model / MSSM-facing quantities can be organized using elementary arithmetic on integers derived from the classification of three-dimensional regular polytopes. This formalization project verifies two distinct but connected claims:

1. **Geometric claim:** the integer structure itself is forced by three-dimensional Platonic classification and finite arithmetic search.
2. **QFT claim:** once a gauge model and matter content are specified, the relevant one-loop structure can be split into clean formal layers and minimized to a small external interface.

The project therefore has **two hard boundaries**:

- a **geometric boundary** between pure arithmetic / classification and any physical interpretation,
- a **QFT boundary** between internal theorem machinery and irreducible external inputs.

### 1.2 Revised design principle

The architecture is now organized around the following principle:

> **Everything derivable from three-dimensional geometry alone is proved in `Geometric/`, with zero physical input. Everything derivable from formal QFT structure is proved in `QFT/`, split into `Representation/`, `Combinatorial/`, and `Analytic/` layers. Only observational data and explicit model choices remain external, isolated under `Axioms/` and `Core/`.**

This means the old `Physical/` zone is no longer treated as a monolithic downstream block. Instead, it is decomposed into mathematically distinct sublayers:

- **Representation layer** — gauge-product structure, sector factorization, Casimir / Dynkin-index data, beta-coefficient assembly.
- **Combinatorial layer** — formal perturbative bookkeeping, Wick expansion, one-loop graph classes, renormalization bridge.
- **Analytic layer** — one-loop RG differential equation, logarithmic running, threshold-style symbolic corrections.

### 1.3 What is being proved

#### Geometric main theorem

> From three-dimensional Platonic classification alone, the gauge-coupling floor structure `(α₁⁻¹, α₂⁻¹, α₃⁻¹) = (60, 30, 8)` is uniquely determined within the finite arithmetic candidate space, and the integer `N = 3` emerges uniquely from `N² − 1 = 8` for `N ≥ 2`.

#### QFT structural theorem package

The following four theorem families define the QFT side of the project:

- **Theorem 1 — MSSM 1-loop beta coefficients**  
  The rational tuple `(b₁, b₂, b₃) = (33/5, 1, -3)` is produced from gauge-group sector data and specified matter content, with the strongest feasible internal derivation implemented in Lean.

- **Theorem 2 — Integrated 1-loop RG running**  
  The one-loop equation for inverse couplings is integrated exactly at the level of the one-loop truncation:
  `α⁻¹(μ) = α⁻¹(μ₀) - (b / 2π) log (μ / μ₀)`.

- **Theorem 3 — Direct-product sector factorization**  
  For a direct-product gauge structure, sector contributions separate cleanly, enabling weak/color factorization and downstream multiplicative organization.

- **Theorem 4 — Mass-ratio decomposition from sector weights**  
  Under sector factorization and chosen weight rules, the quark mass-ratio organization is expressed as a composition of sector weights, recovering the same integer structure identified geometrically.

#### Physical consistency theorem

> Under the chosen model specification and one-loop RG framework, the geometric floor `(60, 30, 8)` predicts `α_s(M_Z)` consistently with observation, while the sector-weight decomposition of quark hierarchy data recovers the same integer `N = 3` derived geometrically.

### 1.4 What is NOT being proved

- **Not** that the Standard Model gauge group must be `SU(3) × SU(2) × U(1)` in nature.
- **Not** that MSSM is true.
- **Not** constructive QFT from a fully defined path integral.
- **Not** full renormalization theory or non-perturbative existence.
- **Not** flavor-sector global-fit numerics beyond the explicitly formalized interfaces.

---

## 2. External Inputs vs Internal Theorems

The project now uses the language of **external interfaces**, not undifferentiated axioms.

### 2.1 External inputs that remain outside the theorem core

#### (a) Observation data
These are empirical boundary conditions and can never be made purely mathematical within the project:

- `α_s(M_Z)` and related coupling inputs,
- quark masses,
- uncertainties,
- renormalization scheme labels,
- reference scales.

#### (b) Gauge-structure choice
The statement that the gauge structure is `SU(3) × SU(2) × U(1)` is treated as a **model choice**, not a theorem.

#### (c) Matter-content choice
The statement that the matter content is MSSM-like (at least at the one-loop bookkeeping level) is treated as a **model specification**, not a theorem.

### 2.2 Internal theorem target
Everything else should be pushed inward as far as feasible. Concretely:

- the beta-coefficient tuple should be derived as far as the representation-theoretic layer permits,
- one-loop RG evolution should be proved as an integrated ODE statement once the one-loop equation is available,
- direct-product sector separation should be theoremized structurally,
- mass-ratio decomposition should be stated as a consequence of sector weights, not as a raw black-box axiom.

---

## 3. Top-Level Architecture

```text
GaugeGeometry/
├── GaugeGeometry.lean
│
├── Core/                             ← shared interfaces, model specs, external-input types
│   ├── GaugeChoice.lean
│   ├── MatterContent.lean
│   ├── ObservationData.lean
│   ├── Sector.lean
│   ├── ModelSpec.lean
│   └── ExternalInputs.lean
│
├── Geometric/                        ← pure mathematics (no physics)
│   ├── Platonic/
│   │   ├── Schlafli.lean
│   │   ├── Classification.lean
│   │   └── IntegerSet.lean
│   ├── Arithmetic/
│   │   ├── CandidateSpace.lean
│   │   ├── UnificationRatio.lean
│   │   └── FloorValues.lean
│   └── GroupDimension/
│       ├── AdjointFormula.lean
│       ├── FromEight.lean
│       └── ColorEmergence.lean
│
├── QFT/
│   ├── Representation/               ← symmetry, sectors, invariants, factorization
│   │   ├── GaugeProduct.lean
│   │   ├── SectorFactorization.lean
│   │   ├── CasimirData.lean
│   │   ├── DynkinIndex.lean
│   │   └── BetaCoefficients.lean
│   │
│   ├── Combinatorial/                ← formal perturbation / one-loop bookkeeping
│   │   ├── WickExpansion.lean
│   │   ├── FeynmanGraphs.lean
│   │   ├── OneLoopGraphs.lean
│   │   └── RenormalizationBridge.lean
│   │
│   └── Analytic/                     ← RG ODE integration and symbolic log structure
│       ├── RGFlow.lean
│       ├── OneLoopRunning.lean
│       ├── LogIdentities.lean
│       └── ThresholdCorrections.lean
│
├── Applications/                     ← concrete predictions / consistency theorems
│   ├── AlphaSPrediction.lean
│   ├── QuarkConsistency.lean
│   ├── QuarkMassRatios.lean
│   └── MassRatioDecomposition.lean
│
└── Axioms/                           ← minimal external assumptions only
    ├── GaugeGroupChoice.lean
    ├── MSSMChoice.lean
    └── PDGInputs.lean
```

### 3.1 Migration of current files

Current files under the old `Physical/` directory should be reassigned as follows:

- `Physical/BetaFunctions.lean`  
  → `QFT/Representation/BetaCoefficients.lean`

- `Physical/RGFlow.lean`  
  → `QFT/Analytic/RGFlow.lean`

- `Physical/AlphaSPrediction.lean`  
  → `Applications/AlphaSPrediction.lean`

- `Physical/QuarkConsistency.lean`  
  → `Applications/QuarkConsistency.lean`

Optional transitional compatibility:

- keep `Physical/` temporarily as a legacy re-export layer,
- delete it once imports are stabilized.

### 3.2 Dependency discipline

The intended import direction is:

```text
Core
  ↓
Geometric
  ↓
QFT/Representation
  ↙       ↘
QFT/Combinatorial   QFT/Analytic
          ↓           ↓
        Applications
```

Rules:

- `Geometric/` must never import `QFT/` or `Applications/`.
- `QFT/Representation/` may use `Core/` and `Geometric/`, but not `Applications/`.
- `QFT/Combinatorial/` and `QFT/Analytic/` may depend on `Representation/` as needed.
- `Applications/` is the only layer allowed to combine geometric results, QFT theorems, and empirical inputs.
- `Axioms/` contains only residual external assumptions that cannot yet be internalized.

---

## 4. Zone Rules and Proof Policy

| Property | `Geometric/` | `QFT/Representation/` | `QFT/Combinatorial/` | `QFT/Analytic/` | `Applications/` |
|---|---|---|---|---|---|
| Allowed inputs | Finite arithmetic, classification | `Core/`, `Geometric/`, representation data | formal series, graph data, representation layer | real/log analysis, beta data, ODEs | all lower layers + observation data |
| Forbidden inputs | PDG, MSSM, RG numerics | PDG experimental values | raw observation numerics | raw observation numerics unless explicitly parameterized | none |
| Output style | exact finite equalities | structural theorem / factorization / coefficient assembly | formal combinatorial identities | integrated formulas / symbolic bounds | predictions / consistency theorems |
| Axioms | none beyond Lean/Mathlib | avoid if possible | avoid if possible | avoid if possible | may reference minimal external input modules |
| Arithmetic policy | exact ℕ / ℚ | exact ℕ / ℚ preferred | exact symbolic objects | symbolic/log-real layer | exact first, numerical wrappers second |

Proof policy:

1. **Internalize first.** Any assumption should be moved out of `Axioms/` whenever a theorem route becomes feasible.
2. **Representation before analytics.** If a coefficient can be reduced to representation data, do that before introducing analytic reasoning.
3. **One-loop before general loop order.** Establish the one-loop package before any higher-loop ambitions.
4. **Applications remain downstream.** No application theorem should be used upstream to justify a structural theorem.

---

## 5. Module Specifications — Geometric Zone

The geometric zone remains conceptually unchanged, but is now explicitly upstream of the QFT layers.

### 5.1 `Geometric/Platonic/Schlafli.lean`

**Goal:** Formalize the Schläfli condition and enumerate integer solutions.

**Key definitions:**
```lean
structure SchlafliPair where
  p : ℕ
  q : ℕ
  p_ge : 3 ≤ p
  q_ge : 3 ≤ q
  condition : (1 : ℚ) / p + (1 : ℚ) / q > 1 / 2
```

**Key theorems:**
- `schlafli_finite`
- `schlafli_enumeration`

### 5.2 `Geometric/Platonic/Classification.lean`

**Goal:** The five-Platonic-solids theorem as a bijection.

**Key theorems:**
- `platonic_bijection`

### 5.3 `Geometric/Platonic/IntegerSet.lean`

**Goal:** Extract the integer set `{3,4,5}`, prime subset `{3,5}`, and generator set `{2,3,5}`.

**Key theorems:**
- `platonic_integers_from_classification`
- `platonic_primes_are_3_and_5`
- `four_is_two_squared`

### 5.4 `Geometric/Arithmetic/CandidateSpace.lean`

**Goal:** Enumerate the finite candidate space for floor structures built from `{2,3,5}`.

**Key theorems:**
- `candidate_space_finite`

### 5.5 `Geometric/Arithmetic/UnificationRatio.lean`

**Goal:** State the unification constraint as a purely rational algebraic identity.

**Key definition:**
```lean
def unificationConsistency (α : Fin 3 → ℚ) (b : Fin 3 → ℚ) : Prop :=
  (α 0 - α 1) * (b 1 - b 2) = (α 1 - α 2) * (b 0 - b 1)
```

**Key theorem:**
- `unification_equivalence`

### 5.6 `Geometric/Arithmetic/FloorValues.lean`

**Goal:** Prove uniqueness of `(60,30,8)` in the finite candidate space subject to the rational consistency condition.

**Important revision:** the slope tuple used here is treated only as a dimensionless parameter tuple. Its physical identification is deferred to the QFT layer.

**Key theorem:**
- `unique_floor_structure`

### 5.7 `Geometric/GroupDimension/AdjointFormula.lean`

**Goal:** Define `adjointDim N = N^2 - 1` as a number-theoretic map.

### 5.8 `Geometric/GroupDimension/FromEight.lean`

**Goal:** Prove `adjointDim N = 8 ↔ N = 3` for `N ≥ 2`.

**Key theorem:**
- `adjoint_dim_eight_iff_three`

### 5.9 `Geometric/GroupDimension/ColorEmergence.lean`

**Goal:** Relate the three appearances of the integer `3` on the geometric side and leave a clean hook for downstream QFT/application closure.

---

## 6. Module Specifications — Core Layer

### 6.1 `Core/GaugeChoice.lean`

**Goal:** Define the abstract gauge-product specification used throughout the project.

**Key definitions:**
```lean
inductive GaugeFactor
  | u1Y
  | su2L
  | su3C

structure GaugeChoice where
  factors : Finset GaugeFactor
  has_u1Y : GaugeFactor.u1Y ∈ factors
  has_su2L : GaugeFactor.su2L ∈ factors
  has_su3C : GaugeFactor.su3C ∈ factors
```

### 6.2 `Core/MatterContent.lean`

**Goal:** Package matter-content assumptions (SM / MSSM / generic sector list).

### 6.3 `Core/ObservationData.lean`

**Goal:** Store empirical inputs with provenance-sensitive tags.

**Recommended structure:**
```lean
structure ObservedQuantity where
  value : ℚ
  uncertainty : ℚ
  scheme : String
  scale : ℚ
  provenance : String
```

### 6.4 `Core/Sector.lean`

**Goal:** Define the indexing type for weak/color/hypercharge sectors and generic sector weights.

### 6.5 `Core/ModelSpec.lean`

**Goal:** Bundle `GaugeChoice`, `MatterContent`, and high-level model metadata into one shared object.

### 6.6 `Core/ExternalInputs.lean`

**Goal:** Provide a single point from which application-level modules import empirical data and explicit model choices.

---

## 7. Module Specifications — QFT Representation Layer

This is the first theorem-producing QFT layer and the most important immediate target.

### 7.1 `QFT/Representation/GaugeProduct.lean`

**Goal:** Formalize the direct-product gauge structure and its sector indexing.

**Key theorems:**
- product-sector lookup lemmas,
- independence of sector labels,
- direct-product bookkeeping identities.

### 7.2 `QFT/Representation/SectorFactorization.lean`

**Goal:** Prove that direct-product sector contributions can be factorized or separated in the forms required by downstream theorems.

**Key theorem target:**
- **Theorem 3 — `direct_product_sector_factorization`**

### 7.3 `QFT/Representation/CasimirData.lean`

**Goal:** Define the representation-theoretic invariants needed for one-loop coefficient assembly.

Possible contents:
- Casimir placeholders / tables,
- trace invariants,
- sector-indexed coefficient containers.

### 7.4 `QFT/Representation/DynkinIndex.lean`

**Goal:** Package Dynkin-index-like data and sum rules in a Lean-friendly form.

### 7.5 `QFT/Representation/BetaCoefficients.lean`

**Goal:** Move the old `Physical/BetaFunctions.lean` here and progressively replace value axioms with internal assembly theorems.

**Immediate theorem target:**
- **Theorem 1 — `mssm_one_loop_beta_coefficients`**

**Implementation staging:**

- **Stage 1:** retain a minimal external interface specifying the MSSM field content and resulting beta tuple.
- **Stage 2:** derive the tuple from sector data and invariant sums as far as the current library permits.
- **Stage 3:** connect diagram bookkeeping from `Combinatorial/` where beneficial.

---

## 8. Module Specifications — QFT Combinatorial Layer

This layer is intentionally scoped to **formal perturbative bookkeeping**, not full constructive QFT.

### 8.1 `QFT/Combinatorial/WickExpansion.lean`

**Goal:** Express Wick-style expansion combinatorially for the restricted one-loop target setting.

### 8.2 `QFT/Combinatorial/FeynmanGraphs.lean`

**Goal:** Introduce a lightweight graph datatype adequate for one-loop classification and sector-label bookkeeping.

### 8.3 `QFT/Combinatorial/OneLoopGraphs.lean`

**Goal:** Enumerate or classify the graph shapes relevant to one-loop coefficient extraction.

### 8.4 `QFT/Combinatorial/RenormalizationBridge.lean`

**Goal:** Provide the bridge from combinatorial one-loop structure to coefficient formulas used in `Representation/BetaCoefficients.lean`.

**Important scope restriction:**
This layer is not required to implement full BPHZ or general Hopf-algebra renormalization in version 1. Its first mission is to support the provenance of Theorem 1.

---

## 9. Module Specifications — QFT Analytic Layer

### 9.1 `QFT/Analytic/RGFlow.lean`

**Goal:** Move the old `Physical/RGFlow.lean` here and formalize the one-loop RG equation at the symbolic level.

**Key theorem target:**
- symbolic form of the one-loop differential equation,
- monotonicity / sign lemmas by sector.

### 9.2 `QFT/Analytic/OneLoopRunning.lean`

**Goal:** Prove the integrated one-loop formula.

**Key theorem target:**
- **Theorem 2 — `integrated_one_loop_running`**

### 9.3 `QFT/Analytic/LogIdentities.lean`

**Goal:** Isolate all logarithmic algebra and simplification lemmas needed by RG-running proofs.

### 9.4 `QFT/Analytic/ThresholdCorrections.lean`

**Goal:** Reserve a clean symbolic location for future threshold-style refinements without polluting the core one-loop theorem.

---

## 10. Module Specifications — Applications Layer

### 10.1 `Applications/AlphaSPrediction.lean`

**Goal:** Move the old `Physical/AlphaSPrediction.lean` here and prove the application-level `α_s(M_Z)` consistency statement.

### 10.2 `Applications/QuarkConsistency.lean`

**Goal:** Move the old `Physical/QuarkConsistency.lean` here and recast it as a downstream application of Theorem 3 plus chosen sector-weight rules.

### 10.3 `Applications/QuarkMassRatios.lean`

**Goal:** Separate raw ratio identities from the final theoremized decomposition.

### 10.4 `Applications/MassRatioDecomposition.lean`

**Goal:** State and prove the final sector-weight composition theorem.

**Key theorem target:**
- **Theorem 4 — `mass_ratio_decomposition_from_sector_weights`**

**Thermo-oriented interpretation hook:**
This module is the preferred place to add a thermodynamic or coarse-graining reinterpretation of sector weights, if such a reformulation is adopted later.

---

## 11. Residual Axioms / External Interface Registry

### 11.1 `Axioms/GaugeGroupChoice.lean`

Contains only the explicit choice that the working model uses the gauge-product structure `SU(3) × SU(2) × U(1)`.

### 11.2 `Axioms/MSSMChoice.lean`

Contains only the explicit matter-content choice needed for MSSM-level one-loop bookkeeping.

### 11.3 `Axioms/PDGInputs.lean`

Contains only empirical input values and metadata needed by application theorems.

**Revision policy:** whenever a statement can be relocated from `Axioms/` to `Core/` or `QFT/`, it must be relocated.

---

## 12. Main Theorem Assembly

### 12.1 `GaugeGeometry.lean` or `Main.lean`

This file should state the top-level results with explicit stratification.

#### Geometric main theorem
```lean
/-- From three-dimensional Platonic classification alone, the floor
    structure (60,30,8) and the unique integer N = 3 are determined. -/
theorem geometric_main : Prop := ...
```

#### QFT structure package
```lean
/-- Representation/QFT theorem package used downstream. -/
theorem qft_structure_package : Prop :=
  mssm_one_loop_beta_coefficients ∧
  integrated_one_loop_running ∧
  direct_product_sector_factorization ∧
  mass_ratio_decomposition_from_sector_weights
```

#### Physical consistency theorem
```lean
/-- Under the chosen external interface, the geometric floor and the QFT
    structure package imply consistency with alpha_s(M_Z) observation and
    quark-sector integer recovery. -/
theorem physical_consistency : Prop := ...
```

---

## 13. Axiom Audit Targets

After `lake build` succeeds, the expected output of:

```text
#print axioms geometric_main
#print axioms qft_structure_package
#print axioms physical_consistency
```

should satisfy the following:

### For `geometric_main`
- only standard Lean / Mathlib axioms,
- **zero model-choice inputs**,
- **zero empirical inputs**.

### For `qft_structure_package`
Target state:
- only standard Lean / Mathlib axioms,
- plus at most explicit model-choice interface facts not yet internalized.

Version-1 acceptable state:
- may still depend on minimal matter-content / gauge-choice interface declarations,
- should not depend on PDG numerical observation data.

### For `physical_consistency`
- standard Lean / Mathlib axioms,
- explicit gauge-choice interface,
- explicit matter-content interface,
- PDG observation inputs.

The strongest deliverable remains the cleanliness of the axiom audit boundary.

---

## 14. Build Order / Execution Plan

### Phase A — stabilize shared infrastructure
1. Create `Core/`.
2. Move observation and model-choice declarations into `Core/` + `Axioms/`.
3. Freeze `Physical/` as legacy compatibility only.

### Phase B — move old `Physical/` files
1. `BetaFunctions.lean` → `QFT/Representation/BetaCoefficients.lean`
2. `RGFlow.lean` → `QFT/Analytic/RGFlow.lean`
3. `AlphaSPrediction.lean` → `Applications/AlphaSPrediction.lean`
4. `QuarkConsistency.lean` → `Applications/QuarkConsistency.lean`

### Phase C — prove the first structural package
Recommended theorem order:

1. **Theorem 3** — direct-product sector factorization  
2. **Theorem 2** — integrated one-loop RG running  
3. **Theorem 1** — MSSM one-loop beta coefficients  
4. **Theorem 4** — mass-ratio decomposition from sector weights

Rationale:
- factorization gives the structural skeleton,
- RG running is analytically straightforward once posed correctly,
- beta coefficients are representation-heavy and can be improved incrementally,
- mass-ratio decomposition is best assembled last as an application theorem.

### Phase D — optional strengthening
1. Add the `Combinatorial/` bridge for provenance of Theorem 1.
2. Minimize remaining external declarations.
3. Remove legacy `Physical/` completely.

---

## 15. Workflow Protocol

Following the established Miosync pipeline:

1. **Producer (Masamichi):** decomposition design, theorem boundary decisions, final approval of external-interface scope.
2. **Director (環 / Claude):** module specifications, proof strategy, architecture revisions.
3. **Strategic reviewer (無二 / GPT):** dependency discipline, axiom minimization, theorem-package coherence, adversarial boundary checks.
4. **Coder (メカタマキ / ClaudeCode):** Lean implementation, type checking, import cleanup, CI stabilization.

---

## 16. Deliverables

1. **GitHub repository:** `miosync-masa/GaugeGeometry`
   - Lean source
   - updated `README.md`
   - CI
   - archived axiom-audit outputs

2. **Zenodo DOI release:** tagged archive for citation.

3. **Paper cross-reference:** the paper cites the Lean repository for:
   - geometric uniqueness of `(60,30,8)`,
   - emergence of `N = 3`,
   - theoremized one-loop QFT split,
   - application-level consistency checks.

---

## 17. Philosophy

- **Zero unnecessary constructs.** Reuse Mathlib where possible.
- **Typed theorem DAG.** Upstream layers return exact equalities or structural propositions; downstream layers assemble them into application-level statements.
- **Connector framing.** No claim of inventing the historical inputs; the claim is that their interconnection can be made formally explicit and sharply audited.
- **Axiom minimization over axiom denial.** The goal is not to pretend that observation or model choice is derivable. The goal is to isolate exactly what is not derivable and force everything else into theorem form.

The strongest claim of the project is therefore still not a number but a boundary:

> **`geometric_main` should carry no physical inputs, and the QFT structure package should shrink the non-geometric interface to the smallest explicit set compatible with the chosen model.**

---

## 18. Implementation Status — Sprint Closeout (2026-04-21)

This section records what has been implemented in Lean and what remains,
as of the sprint closeout on 2026-04-21. It is descriptive, not
prescriptive: authoritative scope and zone rules remain Sections 1–17.

Current repository state compiles cleanly end-to-end
(`lake build` → `Build completed successfully`).

### 18.1 Completed

#### Core / Axioms

- [x] `Core/Sector.lean` — `GaugeSector`, `SectorWeights` + extensionality and accessors
- [x] `Axioms/GaugeGroupChoice.lean` — gauge-product choice axiomatization
- [x] `Axioms/MSSMChoice.lean` — MSSM matter content choice, **plus Stage 2
      inputs**: `mssmAdjointCasimir`, `mssmMatterDynkin` and sector-wise
      numerical axioms
- [x] `Axioms/PDGInputs.lean` — PDG `alphaS`, quark masses, positivity axioms

#### Geometric zone

- [x] `Geometric/Platonic/{Schlafli,Classification,IntegerSet}.lean`
- [x] `Geometric/Arithmetic/{CandidateSpace,FloorValues}.lean` — uniqueness
      of `(60, 30, 8)` inside the candidate space (Section 5.6)
- [x] `Geometric/GroupDimension/{AdjointFormula,FromEight,ColorEmergence}.lean`
      — `adjointDim 3 = 8`, uniqueness theorem for `N = 3`
- [x] `Geometric/Arithmetic/UnificationRatio.lean` — **moved** to
      `Applications/UnificationRatio.lean` (physical, not geometric)

#### QFT/Representation

- [x] `GaugeProduct.lean` — direct-product gauge structure, sector lookup
- [x] `SectorFactorization.lean` — **Theorem 3** (`direct_product_sector_factorization`)
- [x] `CasimirData.lean`, `DynkinIndex.lean` — sector-indexed `ℚ`-valued data
- [x] `BetaCoefficients.lean` — **Theorem 1 Stage 2**: `assembledBeta`,
      `mssmBetaCoefficients_eq_assembly`, `mssm_one_loop_beta_coefficients`

#### QFT/Combinatorial (research-strength)

- [x] `FeynmanGraphs.lean` — labeled multigraph, `Incident`, `Adjacent`,
      `Reachable`, `loopNumber`, `IsOneLoopStrong` (with built-in `0 < V`),
      sector-indexed edge/leg counts + 3-sector decomposition
- [x] `OneLoopGraphs.lean` — weak and strong 1-loop predicates, tadpole
      example, strong → weak implication
- [x] `WickExpansion.lean` — existing Wick-style combinatorics
- [x] `RenormalizationBridge.lean` — `CombinatorialBridge` interface from
      combinatorial statistics to representation-layer data
- [x] `SupportGraph.lean` — `toSimpleGraph` functor, `SupportAdj`,
      `SupportReachable`, `IsSupportConnected`, `IsSupportSpanningTree`,
      connected components through `SimpleGraph.ConnectedComponent`
- [x] `SubGraph.lean` — `FeynmanSubgraph`, `IsProper`, `IsNonempty`,
      `Disjoint`, `Nested`, `NestedOrDisjoint`; `DivergenceMeasure` class,
      `IsDivergent` / `IsLogDivergent` / `IsConvergent`; `Forest G`,
      `Forest.insert` / `.erase`, `LE`, `IsMaximal`, `DecidableEq`
- [x] `Permutation.lean` — `Equiv.Perm VertexId` left action on edges,
      legs, graphs, subgraphs; `mapPerm_one`, `mapPerm_mul`;
      `mapPerm_*Count`, `mapPerm_loopNumber` invariances;
      `MulAction (Equiv.Perm VertexId) FeynmanGraph` instance;
      subgraph-level `Disjoint` / `Nested` / `NestedOrDisjoint` transports;
      `IsPermInvariantDivergence`; `Forest.mapPerm`
- [x] `GraphIsomorphism.lean` — `FeynmanGraph.IsIso`, `Setoid`, equivalence
      lemmas, connection to `MulAction.orbitRel`; `FeynmanGraphClass`
      quotient with `vertexCount` / `internalEdgeCount` /
      `externalLegCount` / `loopNumber` lifted
- [x] `ForestFormula.lean` — **light Connes–Kreimer**: `CountertermScheme`,
      `RemainderEvaluator`, `Forest.contribution`, `R_operation`, basic
      algebraic properties — full Zimmermann forest sum written without
      graph-quotient `Γ / γ`

#### QFT/Analytic

- [x] `RGFlow.lean` — `alphaInvRunning`, `integrated_one_loop_rg_running`,
      `alphaInvRunning_at_reference` (Theorem 2 skeleton)
- [x] `OneLoopRunning.lean` — TODO-structured placeholder
- [x] `LogIdentities.lean` — TODO-structured placeholder
- [x] `ThresholdCorrections.lean` — TODO-structured placeholder

#### Applications

- [x] `UnificationRatio.lean` — relocated from `Geometric/`; documents the
      split between idealized algebraic unification and empirical floor
      consistency. Contains `unificationConsistency`,
      `unification_equivalence`, `target_not_unification_consistent`
      (for `(60, 30, 8)`), `nontrivial_unification_solution`
      (for `(15, 8, 3)`)
- [x] `AlphaSPrediction.lean` — `alpha3InvPrediction`, `alphaSPrediction`,
      integrated formula, reference-scale collapse
- [x] `QuarkMassRatios.lean` — `GenerationFactor`, `f2`, `f3`,
      `ratioOfRatios`; PDG-level `pdgUpDownRatio`, `pdgGenerationFactor`,
      `pdgGenerationFactor_zero`
- [x] `QuarkConsistency.lean` — `ChannelFactorizationHolds` predicate,
      **`ratio_of_ratios_recovers_N`**, `ratio_of_ratios_matches_geometric_three`,
      **`geometric_physical_consistency`** closing the
      `platonic 3 ↔ adjoint N = 3 ↔ color N_c = 3` triangle at the
      `ℚ`-algebraic level
- [x] `MassRatioDecomposition.lean` — **Theorem 4**:
      `mass_ratio_decomposition_from_sector_weights`,
      `massRatioFromSectorWeights_eq_factorized`,
      `running_mass_ratio_decomposition_from_sector_weights`

#### Top-level

- [x] `Main.lean` — `geometric_main` (purely geometric), plus
      `unification_physical_separation` as a separate headline theorem
      now that algebraic unification lives in `Applications/`

### 18.2 Theorem-status snapshot

| Theorem | Status | Location |
|---|---|---|
| Theorem 1 — MSSM 1-loop β coefficients | ✅ Stage 2 (assembly from axioms) | `QFT/Representation/BetaCoefficients.lean` |
| Theorem 2 — Integrated 1-loop RG running | ✅ statement + proof (`integrated_one_loop_rg_running`) | `QFT/Analytic/RGFlow.lean` |
| Theorem 3 — Direct-product sector factorization | ✅ complete | `QFT/Representation/SectorFactorization.lean` |
| Theorem 4 — Mass-ratio decomposition from sector weights | ✅ complete | `Applications/MassRatioDecomposition.lean` |
| Geometric main — Platonic → floor / adjoint / `N = 3` | ✅ `geometric_main` | `Main.lean` |
| Physical consistency — full three-way closure | ⬜ `physical_consistency` placeholder | `Main.lean` |

### 18.3 Remaining tasks

#### Representation
- [ ] Theorem 1 Stage 3 — replace the axiom-level Casimir/Dynkin inputs
      with a `CombinatorialBridge`-assembled derivation; wire to
      `QFT/Combinatorial/RenormalizationBridge.lean` so that the
      remaining inputs collapse to matter-content choice

#### Analytic
- [x] `OneLoopRunning.lean` — restate Theorem 2 canonically, add
      monotonicity / sign lemmas per sector
- [x] `LogIdentities.lean` — `log_ratio_identity`, `log_ref_zero`,
      `log_scaling_identity`
- [ ] `ThresholdCorrections.lean` — `ThresholdProfile`,
      `alphaInvRunning_with_threshold`, matching identities

#### Applications
- [ ] `Main.lean` — `physical_consistency` assembling
      `geometric_main` + Theorem 1 + Theorem 2 + Theorem 4 +
      `ratio_of_ratios_recovers_N` under the PDG and MSSM axioms
- [ ] Numerical consistency statements that feed `pdgGenerationFactor`
      into `ratio_of_ratios_recovers_N` once a suitable PDG-level
      `ChannelFactorizationHolds` instance is established

#### Combinatorial (optional / research-strength extensions)
- [ ] Graph quotient `Γ / γ` and the full Connes–Kreimer Hopf algebra
      (coproduct `Δ`, antipode `S`, Birkhoff decomposition). Current
      `ForestFormula.lean` intentionally avoids `Γ / γ`.
- [ ] Sub-Hopf algebras (e.g. ladders) as instance theorems under the
      full Hopf construction
- [ ] Full 1PI predicate (`IsOnePI`) and its use as the Hopf generator set

#### Axiom audit
- [ ] `#print axioms` audit for `geometric_main`, the Theorem-1–4 bundle,
      and a future `physical_consistency` — compare against the targets
      in Section 13

### 18.4 Build status

- `lake build` (working tree, 2026-04-21): **exit 0**,
  `Build completed successfully`.
- All modules under `GaugeGeometry/` type-check against the pinned
  Mathlib revision in `lakefile.toml` (`v4.29.0`).
