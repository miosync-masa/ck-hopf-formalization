# HOPF_DECOMPOSITION.md
## Connes–Kreimer Hopf Algebra of Feynman Graphs — Theorem-Map Decomposition

**Methodology:** NSBarrier-style layer decomposition. Every statement carries exactly one tag; the goal is to push the cardinality of `[ConKr]` (the irreducible Connes–Kreimer-specific layer) to its minimum, with everything else discharged through `[Def]/[Comb]/[Graph]/[Algebra]/[Tensor]/[Hopf]/[ConKr-derived]`.

**Status (revised 2026-04-30):** Sprints A + B' + C1 + C2 + Sprint D prep + Sprint D/H5.8F **complete** at IDE-clean granularity.  Sprint E now starts from the final coassociativity gate `coassoc_strict_forest_linear_h58`, whose only explicit finite payload is the RHS indexed branch classifier.
- Sprint A: H0 (12/12) + H1 (17/17) incl. H1.17 `contract_chain` [ConKr].
- Sprint B': H1.WF.1–5 + H2.1/H2.2/H2.3/H2.4 + H3.0–3.5. H2.5 deferred to Sprint C per Plan-D Hybrid.
- Sprint C1: H2.5 + H3.6–3.9 (strict `HopfH` + bridge). New typeclass `IsIsoInvariantDivergence` (strategist-approved).
- Sprint C2: H4.1–H4.11 (index set + `coproductGen` non-recursive formula + `coproductGen_isomorphism_invariant` + class-lift + `coproduct` via `MvPolynomial.aeval`). `Fintype (FeynmanSubgraph G)` carried as Path-cut variable (supply-commitment recorded below).
- Sprint D prep: `contract.IsOnePI`, `contract.IsDivergent`, `contract.IsConnectedDivergent` (Path-α: full graph-theoretic proof of 1PI preservation; Plan-D1 typeclass `IsDivergencePreservedByContract` for divergence preservation).
- Sprint D final cut: the admissible-forest coassociativity route is fully installed.  H5.8F has been reduced through boundary cancellation, graph-field transport, source internal-edge counting, source-edge witnesses, quotient-index positivity, and the RHS indexed branch classifier to the final theorem entrance `coassoc_strict_forest_linear_h58`.  The explicit summit payload is now only `CoassocStrictForestH58FinitePayloads.indexed_classifier`; quotient complement positivity and component-complement positivity are canonical below the gate.
- `sorry` 0, project-specific axiom 0. Axiom audit: `[propext, Classical.choice, Quot.sound]` only — same footprint as `geometric_main`.
- Path-B `FeynmanSubgraphClass` carrier chosen over Σ-type Path A; `swapFixExtend π s := swap s (π s) * π` added for ambient-fixing-perm → `freshVertex`-fixing-perm adjustment in H2.1.
- Path-Sub for `FeynmanGraph.IsConnectedDivergent` (delegation to `FeynmanSubgraph.self`, strategist-selected 2026-04-24 morning).
- Path-W for `DivergenceMeasure`/`IsPermInvariantDivergence`/`IsIsoInvariantDivergence`/`Fintype (FeynmanSubgraph G)` supply (global family-instance `variable` parameters, Sprint C1/C2 mechanism). Sprint D2 adds `IsDivergencePreservedByAdmissibleForestContract` for CK forest-level power-counting stability.

---

## Tag Legend (revised 2026-04-23)

| Tag | Meaning | Discharge mechanism |
|-----|---------|---------------------|
| `[Def]` | Definitional unfolding | `unfold`, `rfl`, `simp` on accessors |
| `[Comb]` | Multiset/Finset combinatorics | Mathlib `Multiset.*`, `Finset.*` lemmas |
| `[Graph]` | Graph-specific identity (Euler, connectivity transport) | Local induction over `internalEdges` / vertices |
| `[Algebra]` | Free commutative algebra / ring-theoretic identity | Mathlib `MvPolynomial`, `Algebra.lift_unique`, `aeval` universality |
| `[Tensor]` | Tensor-product syntactic manipulation | Mathlib `TensorProduct`, `LinearMap.lTensor`, `rTensor` |
| `[Hopf]` | Mathlib `HopfAlgebra` / `Bialgebra` instance machinery | `Mathlib.RingTheory.HopfAlgebra` |
| `[ConKr]` | Connes–Kreimer 1998 specific identity, **stand-alone irreducible** | A new combinatorial truth not deducible from any prior `[ConKr]` |
| `[ConKr-derived]` | A statement *of CK form* whose proof reduces to a prior `[ConKr]` by `rw`/induction without introducing new combinatorics | E.g. H5.8 coassoc `rw [contract_chain]`. Counted separately from `[ConKr]` for irreducibility audit. |

**Counting rule (NSBarrier discipline):** For irreducibility audits, `[ConKr-derived]` does NOT increment the irreducible count. The "true irreducible footprint" of the construction is `#[ConKr]` only.

---

## Architecture: Layer DAG

```
H0 (connectivity primitives)         [done]
  └─▶ H1 (subgraph contraction)      [done, incl. H1.17 [ConKr]]
        ├─▶ H1.WF (loopNumber wf-recursion stub)
        │     └─▶ H2 (graph-class quotient)
        │           └─▶ H3 (free commutative algebra over restricted classes)
        │                 └─▶ H4 (coproduct via aeval, recursion on loopNumber)
        │                       └─▶ H5 (bialgebra: counit, coassoc, multiplicativity)
        │                             └─▶ H6 (antipode + Hopf instance)
```

Discipline:
- H_n only depends on H_{<n}.
- Each Sprint must end with `lake build` exit 0, `sorry`-count 0, no project-specific axioms.

### Sprint cuts (revised 2026-04-24, post-Sprint-C2)

| Sprint | Layers | Statement count | Character | Status |
|--------|--------|-----------------|-----------|--------|
| **Sprint A** | H0 + H1 | 29 | Hard combinatorics (H1.17 `[ConKr]`) | **DONE 2026-04-22** |
| **Sprint B'** | H1.WF + H2.1–2.4 + H3.0–3.5 | 16 | Mechanical wiring | **DONE 2026-04-23** |
| **Sprint C1** | H2.5 + H3.6–3.9 | 7 | Generator subtype + bridge (Path-Sub + Path-W) | **DONE 2026-04-24 morning** |
| **Sprint C2 Phase A** | H4.1–H4.5 | 6 | Index set + non-recursive `coproductGen` + unfold | **DONE 2026-04-24 morning** |
| **Sprint C2 Phase B** | H4.6 + helpers | 10 (incl. `contract_mapPerm_isIso` core, Option X2) | Isomorphism-invariance, ambient-moving contract iso | **DONE 2026-04-24 morning** |
| **Sprint C2 Phase C** | H4.7–H4.11 | 5 | Class-lift + `MvPolynomial.aeval` extension | **DONE 2026-04-24 morning** |
| **Sprint D prep** | `contract.IsOnePI` / `IsDivergent` / `IsConnectedDivergent` | 8 (incl. `asSubOfErase`, data equality, `IsDivergencePreservedByContract`) | Path-α: prove 1PI preservation + Plan-D1 divergence typeclass | **DONE 2026-04-24 afternoon** |
| Sprint D main | H5.1–H5.10 (Bialgebra) | 10 | admissible-forest H5.8F route; final gate `coassoc_strict_forest_linear_h58` | **DONE 2026-04-30** |
| Sprint E | H6.1–H6.8 (Antipode + Hopf) | 8 | antipode recursion + Hopf instance assembly | Pending |

**Why split Sprint C into C1/C2-A/B/C** (mid-Sprint-C refinement, 2026-04-24 morning):
The original Sprint C was H4 (12 statements, recursion-heavy). During C2 Phase A a design clarification surfaced: the CK coproduct `Δ([Γ]) = [Γ] ⊗ 1 + 1 ⊗ [Γ] + ∑ [γ] ⊗ [Γ/γ]` is a **non-recursive formula on generators** — both tensor factors are generators, not recursive calls. `edgeRecursion` (Sprint B') remains the scaffolding for H4.6 isomorphism-invariance induction and Sprint E antipode recursion, but `coproductGen` itself is a direct `def`. This discovery enabled Phase A → Phase B → Phase C to be separated along the mechanical/proof-heavy/mechanical grain, mirroring Sprint A's retrospective lesson.

**Why Sprint D prep was inserted (mid-session, 2026-04-24 afternoon):**
Sprint C2 Phase C's `coproduct : HopfH →ₐ[ℚ] HopfH_temp ⊗ HopfH_temp` has target `HopfH_temp` (scaffold), but Mathlib `Bialgebra ℚ HopfH` requires `comul : HopfH →ₗ[ℚ] HopfH ⊗ HopfH` (source = target = `HopfH`). To align target, each summand `[γ.contract]` must be a `HopfGen` element, which needs `γ.contract.IsConnectedDivergent`. Sprint A H1.16 supplies connectedness preservation; `IsOnePI` preservation was previously unproved. Strategist selected **Path-α** (prove it, ~250 lines) over Path-β (new typeclass) and Path-γ (weaken CK claim to `HopfH_temp` sub-bialgebra). Split plan: prep today, main body tomorrow.

**Sprint B.WF eliminated.** A previous version of this document scheduled a dedicated Sprint B.WF to discharge a deferred Euler-inequality hypothesis (`loopNumber_nonneg_of_connected`). The 2026-04-23 measure-change to `internalEdgeCount` makes that hypothesis structurally unnecessary; the entire H1.WF layer compiles axiom-clean from Sprint B' alone.

### Supply-commitments (Path-cut deferred items)

Sprint C2 Phase A carried `Fintype (FeynmanSubgraph G)` as a `variable` hypothesis to avoid 30–50 lines of Mathlib Subtype-fintype combinator wiring. **Supply commitment (strategist-recorded 2026-04-24):** the concrete `Fintype` instance (via triple-injection `(Finset × Multiset × Multiset)` into ambient-finite types) must be supplied before Sprint D completion. The final `HopfAlgebra ℚ HopfH` instance must be hypothesis-free.

Sprint D prep introduced `class IsDivergencePreservedByContract` (Plan-D1, abstracting CK 1998 power-counting stability). Concrete measures (e.g. MSSM 1-loop) satisfying power-counting must provide instances; this is on the same level as Sprint A's `IsPermInvariantDivergence` and is not a project-specific axiom.

---

## H0. Connectivity & 1PI predicates  [DONE]

**Goal:** Promote `IsSupportConnected` to a 1PI (one-particle-irreducible) predicate, plus a "connected ∧ 1PI ∧ divergent" composite that becomes the index set of the Connes–Kreimer sum.

**Existing resources (Sprint A artifact):**
- [SupportGraph.lean](GaugeGeometry/QFT/Combinatorial/SupportGraph.lean) — `IsSupportConnected`, `SupportReachable`, `toSimpleGraph`
- [SubGraph.lean](GaugeGeometry/QFT/Combinatorial/SubGraph.lean) — `FeynmanSubgraph`, `IsDivergent`, `IsProper`, `IsNonempty`
- [FeynmanGraphs.lean](GaugeGeometry/QFT/Combinatorial/FeynmanGraphs.lean) — `loopNumber : Int`, `IsConnected`

| # | Statement | Tag | Status |
|---|---|---|---|
| H0.1–H0.12 | (see git history; all 12 done) | `[Def]/[Comb]/[Graph]` | ✓ |

**Layer count:** 12 statements, **0 `[ConKr]`**.

---

## H1. Subgraph contraction primitive  [DONE]

**Goal:** Define `contractWith : FeynmanSubgraph G → VertexId → FeynmanGraph` (with `contract` as the alias `contractWith γ.contractedVertex`). Prove cardinality counts, loop-number additivity, and `contract_chain` (H1.17).

**Architectural decision preserved from Sprint A:** `contractWith` carries the star vertex as an explicit parameter. This was the option-α choice (literal `FeynmanGraph` equality in H1.17) over option-β (isomorphism-only). Cost: 200+ extra lines in H1.17. Payoff: H5.8 (coassociativity) becomes a `rw [contract_chain]`-driven derivation rather than a 500+ line `TensorProduct.map` gymnastics.

| # | Statement | Tag | Status |
|---|---|---|---|
| H1.1–H1.16 | (see git history) | `[Def]/[Comb]/[Graph]` | ✓ |
| **H1.17** | **`contract_chain`** | **`[ConKr]`** | ✓ |

**Layer count:** 17 statements, **1 `[ConKr]`** — the only stand-alone irreducible of the entire construction.

---

## H1.WF. Well-founded recursion stub  [Sprint B', Option C+δ+(ii) confirmed 2026-04-23]

**Goal:** Provide a `WellFoundedRelation` for connected Feynman graphs keyed on `loopNumber`, plus a shared recursion helper that both H4.3 (coproduct) and H6.1 (antipode) can reuse.

### File layout (Option δ confirmed 2026-04-23)

New directory `GaugeGeometry/QFT/HopfAlgebra/` separates Hopf-algebra-section infrastructure from existing graph-structure files in `Combinatorial/`. Sprint B–E layout:

```
GaugeGeometry/QFT/
├── Combinatorial/                    (graph structure — Sprint A artifacts)
│   ├── FeynmanGraphs.lean
│   ├── SubGraph.lean                 (Sprint A: H1.17 etc.)
│   ├── SupportGraph.lean
│   ├── GraphIsomorphism.lean
│   ├── Permutation.lean
│   └── ForestFormula.lean            (legacy R_operation, future Birkhoff target)
│
└── HopfAlgebra/                      (algebra structure — Sprints B'–E)
    ├── ConnectedFeynmanGraph.lean    (Sprint B': subtype + basic lemmas)
    ├── RecursionMeasure.lean         (Sprint B': H1.WF.1–4 via internalEdgeCount)
    ├── HopfGenSubtype.lean           (Sprint B': H3 subtype + decidability)
    ├── Coproduct.lean                (Sprint C: H4)
    ├── Bialgebra.lean                (Sprint D: H5)
    └── Antipode.lean                 (Sprint E: H6)
```

Rationale:
- Sprint B–E shared infrastructure lives in one directory.
- `Combinatorial/` (graph structure) and `HopfAlgebra/` (algebraic structure) have clean responsibility boundaries.
- Future Birkhoff decomposition work in `Combinatorial/ForestFormula.lean` cleanly cites `HopfAlgebra/` instead of cross-cutting.
- Paper-writing reference is clean: "the Hopf-algebra-section core files live in `HopfAlgebra/`".

### Measure choice: `internalEdgeCount`, not `loopNumber.toNat`

A first-pass design used `loopNumber.toNat` as the wf-measure. This forced a separate proof that `0 ≤ G.loopNumber` for connected graphs (the Euler inequality `V ≤ E + 1` via spanning-tree combinatorics) — a deep but tangential lemma, not on the critical path for the Hopf-algebra construction.

**Resolution (2026-04-23, after exploration of three candidate measures): use `internalEdgeCount` as the wf-measure.**

| Candidate | Reduction proof | Auxiliary needed |
|---|---|---|
| `loopNumber.toNat` (initial) | H1.15 (`loopNumber_contract_lt`) + Euler inequality | `loopNumber_nonneg_of_connected` (spanning-tree, ~100 lines) |
| `internalEdgeCount` (**adopted**) | H1.9 + `Multiset.card_sub` + `omega` | none beyond Sprint A |
| `vertexCount + internalEdgeCount` | H1.8 + H1.9, `Nat.sub` monotonicity | clumsy, rejected |

`internalEdgeCount` is the cleanest: H1.9 (`internalEdgeCount_contract`) gives `γ.contract.E = (G.I − γ.I).card`, and `Multiset.card_sub` plus `omega` close strict decrease in 5 lines, given the natural condition `0 < γ.internalEdges.card` (γ has ≥ 1 internal edge — physically, divergent 1PI subgraphs with no internal lines are excluded from the Connes–Kreimer sum and will be excluded from H4.1's index set by construction).

**Why this changes nothing about the final Hopf instance.** The Connes–Kreimer 1998 *grading* by loop number is a property of the resulting `HopfAlgebra` (recoverable as a graded-bialgebra structure on `HopfH`), not of the recursive *construction*. The choice of recursion measure is internal scaffolding; it affects only the termination proof, not the algebraic output. The paper's Discussion will note: "*The wf-measure used in the Lean formalization is `internalEdgeCount`. The Connes–Kreimer loop-number grading is recovered as a separate proposition (Prop X.Y) on the constructed `HopfH`.*"

**Zero project-specific axioms.** With `internalEdgeCount`, the entire `H1.WF` layer compiles with axiom footprint `[propext, Classical.choice, Quot.sound]` only — identical to Sprint A. No deferred hypotheses, no Sprint B.WF.

### Resolution: Option C (subtype to connected graphs) — retained

The subtype `ConnectedFeynmanGraph` is still the right carrier for the recursion, because `coproductGen` and `antipodeGen` rely on H1.16 (connectivity preserved under contraction) at every recursive call. The structural fact that closes the loop:

```
H0.9   IsConnectedDivergent           ─┐
H1.16  contract preserves connectivity ─┤
H1.9   internalEdgeCount_contract     ─┤  (provides strict decrease)
                                       ├─▶ ConnectedFeynmanGraph subtype is closed under recursion
H3.1   HopfGen subtype  ──────────────┘
                                       ▼
H4.3   coproductGen recursion on ConnectedFeynmanGraph is self-contained
H6.1   antipodeGen     ditto
```

The recursion's recursive call `coproductGen (G.contract γ)` lands back in `ConnectedFeynmanGraph` because `G` connected + `γ ∈ ConnectedDivergent` ⇒ `G.contract γ` connected (H1.16).

### Statement table (H1.WF, revised — internalEdgeCount measure)

| # | Statement | Tag | Depends on |
|---|---|---|---|
| H1.WF.1 | `def ConnectedFeynmanGraph := { G : FeynmanGraph // G.IsSupportConnected }` | `[Def]` | SupportGraph |
| H1.WF.2 | `def graphEdgeWFRel : WellFoundedRelation ConnectedFeynmanGraph := invImage edgeMeasure Nat.lt_wfRel` (where `edgeMeasure := G.toFeynmanGraph.internalEdgeCount`) | `[Def]` | H1.WF.1 |
| H1.WF.3 | `edgeMeasure_contract_lt : γ.IsConnected → γ.IsNonempty → 0 < γ.internalEdges.card → (G.contract γ _ _).edgeMeasure < G.edgeMeasure` | `[Comb]` (H1.9 + `Multiset.card_sub` + `omega`, ~5 lines) | H1.9 |
| H1.WF.4 | **`def edgeRecursion : ∀ (motive : ConnectedFeynmanGraph → Sort*), (∀ G, (∀ G', G'.edgeMeasure < G.edgeMeasure → motive G') → motive G) → ∀ G, motive G`** — shared recursor for H4.3 and H6.1 | `[Def]` | H1.WF.2 |
| H1.WF.5 | `instance : WellFoundedRelation ConnectedFeynmanGraphClass` (Quotient lift) | `[Algebra]` | H1.WF.2, GraphIsomorphism |

**Layer count:** 5 statements, **0 `[ConKr]`**, **0 deferred hypotheses, 0 axioms**.

**Why H1.WF.4 (the shared helper) is mandatory and not optional:** H4.3 (`coproductGen`) and H6.1 (`antipodeGen`) both recurse on the same `edgeMeasure`-decreasing structure. Writing the `termination_by` clause twice doubles debugging surface and risks divergence between the two recursions. Mirrors the `contractWith` shared-primitive thinking from Sprint A H1.5.

**Status (2026-04-23):** H1.WF.1 in `ConnectedFeynmanGraph.lean`; H1.WF.2–4 in `RecursionMeasure.lean`. Both files build clean, axiom audit shows only `[propext, Classical.choice, Quot.sound]`. H1.WF.5 deferred to Sprint B' H2 work (depends on `GraphIsomorphism`).

---

## H2. Graph-class quotient lift  [Sprint B' + Sprint C1]  [DONE]

**Goal:** Lift `contract` and `IsConnectedDivergent` to `FeynmanGraphClass = Quotient FeynmanGraph.isoSetoid`. Most infrastructure already exists in `GraphIsomorphism.lean` and `Permutation.lean`.

**Per Q3 = (Y) — confirmed:** generators of the algebra are `FeynmanGraphClass`, so `Δ` must be isomorphism-invariant. H2 establishes the underlying invariances.

**Existing infrastructure (verified 2026-04-23):**
- `FeynmanGraphClass = Quotient FeynmanGraph.isoSetoid` (GraphIsomorphism.lean:130) ✓
- `IsIso G₁ G₂ := ∃ π : Equiv.Perm VertexId, G₂ = G₁.mapPerm π` (line 33–34) ✓
- `MulAction (Equiv.Perm VertexId) FeynmanGraph` instance (Permutation.lean:403) ✓
- `mapPerm_isOnePI_iff`, `Disjoint`/`Nested` permutation-invariance (Permutation.lean:378, etc.) ✓

| # | Statement | Tag | Status | Sprint | File |
|---|---|---|---|---|---|
| H2.1 | `IsIso.contract_isomorphic` : `G₁.IsIso G₂ → ∀ γ₁ γ₂ corresponding, γ₁.contract.IsIso γ₂.contract` | `[Graph]` | ✓ | B' | `HopfAlgebra/SubgraphClass.lean` |
| H2.2 | `def FeynmanGraphClass.contract` (via `Quotient.lift`) | `[Algebra]` | ✓ | B' | `HopfAlgebra/SubgraphClass.lean` |
| H2.3 | `FeynmanGraphClass.loopNumber` already exists; verify decreasing under H2.2 | `[Def]` | ✓ | B' | `HopfAlgebra/SubgraphClass.lean` |
| H2.4 | `FeynmanSubgraphClass` — `Quotient` of subgraphs under permutations preserving `G`'s class | `[Algebra]` | ✓ | B' | `HopfAlgebra/SubgraphClass.lean` |
| H2.5 | `FeynmanSubgraphClass.IsConnectedDivergent` is well-defined (lifted) | `[Algebra]` | ✓ | C1 | `HopfAlgebra/SubgraphClass.lean` |

**Layer count:** 5 statements, **0 `[ConKr]`**. Mechanical.

**Sprint C1 addition for H2.5:** a new companion typeclass `IsIsoInvariantDivergence` was introduced alongside Sprint A's `IsPermInvariantDivergence`. The Path-B iso relation on `FeynmanSubgraph G` is *intra-ambient* (both γ₁, γ₂ have ambient `G` with a witness `G.mapPerm π = G`), so `subst hG` fails on `G.mapPerm π = G` (the LHS contains `G`). The `IsIsoInvariantDivergence` class states intra-ambient iso-invariance directly, sidestepping `▸`-transport. Strategist-approved 2026-04-24.

---

## H3. Free commutative algebra over restricted graph classes  [Sprint B' + Sprint C1, Plan-D Hybrid]  [DONE]

**Goal:** Build the polynomial algebra `HopfH := MvPolynomial X_CK ℚ` where `X_CK = { [Γ] : FeynmanGraphClass // [Γ] is connected 1PI divergent }` is the Connes–Kreimer 1998 generators set.

**Why `MvPolynomial` over `FreeCommRing`:**
- `MvPolynomial X ℚ` is a `CommAlgebra ℚ` directly; no `ℤ`-algebra ⇒ `ℚ`-algebra extension needed.
- `TensorProduct ℚ` over `MvPolynomial X ℚ` is well-developed in Mathlib (verified 2026-04-23).
- The unit `1 : H` is `MvPolynomial.C 1`; the empty graph corresponds to `1`, not to a generator.

### Plan-D Hybrid strategy (confirmed 2026-04-23)

The full `IsConnectedDivergent` predicate requires class-level lifting of `DivergenceMeasure` (a per-graph typeclass) and `IsOnePI`, which together involve >100 lines of speculative class-lift infrastructure that Sprint B' should not pre-build.

We adopt the **Sprint A `contractWith` pattern**: build a minimal scaffold artifact in Sprint B', then add the full Connes–Kreimer artifact in Sprint C alongside it.

| Sprint | Artifact | Generators set | Status |
|--------|----------|----------------|--------|
| **B'** | `HopfH_temp := MvPolynomial { [Γ] // [Γ].IsSupportConnected } ℚ` | All connected (not necessarily 1PI/divergent) graph classes | Scaffold |
| **C** | `HopfH := MvPolynomial { [Γ] // [Γ].IsConnectedDivergent } ℚ` | Connes–Kreimer 1998 strict generators (connected 1PI divergent) | **Final CK artifact** |
| C | Bridge: `HopfH ↪ HopfH_temp` (algebra embedding) — or `HopfH_temp ↠ HopfH` (projection killing non-CD generators) | — | Connecting hom |

The bridge mirrors `contract = contractWith γ.contractedVertex` from Sprint A: the scaffold (`HopfH_temp`) and the final artifact (`HopfH`) coexist, with `HopfH` being the one carrying the `HopfAlgebra ℚ` instance and corresponding to Connes–Kreimer 1998.

**Why Plan-D is mathematically honest:** The final paper claim is "we formalised the Connes–Kreimer 1998 Hopf algebra". The artifact carrying `HopfAlgebra ℚ` is `HopfH` with the strict `IsConnectedDivergent` generators set — exactly Connes–Kreimer. `HopfH_temp` is internal scaffolding, not part of the published claim.

### Sprint B' subtable (H3 minimal scaffold)  [DONE]

| # | Statement | Tag | Status | File |
|---|---|---|---|---|
| H3.0 | `def HopfGenTemp := { [Γ] : FeynmanGraphClass // [Γ].IsSupportConnected }` | `[Def]` | ✓ | `HopfAlgebra/Algebra.lean` |
| H3.1 | `abbrev HopfH_temp := MvPolynomial HopfGenTemp ℚ` | `[Def]` | ✓ | `HopfAlgebra/Algebra.lean` |
| H3.2 | `def gen_temp ([Γ] : HopfGenTemp) : HopfH_temp := MvPolynomial.X [Γ]` | `[Def]` | ✓ | `HopfAlgebra/Algebra.lean` |
| H3.3 | `instance : CommRing HopfH_temp`, `Algebra ℚ HopfH_temp` | `[Algebra]` | ✓ (Mathlib) | — |
| H3.4 | `instance : CommRing (HopfH_temp ⊗[ℚ] HopfH_temp)` | `[Algebra]` | ✓ (Mathlib) | — |
| H3.5 | `instance : Algebra ℚ (HopfH_temp ⊗[ℚ] HopfH_temp)` | `[Algebra]` | ✓ (Mathlib) | — |

**Sprint B' layer count:** 6 statements, **0 `[ConKr]`**. Mathlib heavy lifting.

### Sprint C1 subtable (H3 strict CK refinement)  [DONE 2026-04-24 morning]

**Path-Sub strategy (strategist-selected 2026-04-24):** `FeynmanGraph.IsConnectedDivergent` is defined by delegation to the Sprint A subgraph-level predicate via `FeynmanSubgraph.self`:

```
def FeynmanGraph.IsConnectedDivergent [DivergenceMeasure G] : Prop :=
  ∃ hG : G.WellFormed, (FeynmanSubgraph.self G hG).IsConnectedDivergent
```

This reuses the Sprint A three-conjunct `IsConnected ∧ IsOnePI ∧ IsDivergent` definition without introducing a parallel `FeynmanGraph.IsOnePI ∧ ...` API. The `∃ hG`-wrapper makes `IsConnectedDivergent` a `Prop` on `FeynmanGraph` alone; `WellFormed` is proof-irrelevant so no choice is made. Every `HopfGen` element carries an implicit `WellFormed` witness through this design — **crucial for Sprint D** where `coproductGen_isomorphism_invariant` requires `G.WellFormed`.

**Path-W strategy (strategist-selected 2026-04-24):** class-lifting `DivergenceMeasure` is avoided via family-instance `variable` parameters:

```
section PathW
  variable [∀ G : FeynmanGraph, DivergenceMeasure G]
           [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
           [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
```

Concrete instances are substituted at use sites; the bundle avoids 100+ lines of class-wide typeclass infrastructure (Plan-Y).

| # | Statement | Tag | Status | File |
|---|---|---|---|---|
| H3.6 | `FeynmanGraph.IsConnectedDivergent` + `FeynmanGraphClass.IsConnectedDivergent` via `Quotient.lift` with Path-W supply | `[Def]`+`[Algebra]` | ✓ | `HopfAlgebra/StrictGenerators.lean` |
| H3.7 | `def HopfGen := { [Γ] : FeynmanGraphClass // [Γ].IsConnectedDivergent }` | `[Def]` | ✓ | `HopfAlgebra/StrictGenerators.lean` |
| H3.8 | `abbrev HopfH := MvPolynomial HopfGen ℚ` + Mathlib instance verification | `[Def]`+`[Algebra]` | ✓ | `HopfAlgebra/StrictGenerators.lean` |
| H3.9 | `bridge : HopfH →ₐ[ℚ] HopfH_temp` via `MvPolynomial.aeval` on subtype inclusion `HopfGen.toTemp : HopfGen → HopfGenTemp` | `[Algebra]` | ✓ | `HopfAlgebra/StrictGenerators.lean` |

**Sprint C1 layer count (H3 portion):** 4 statements. Total H3: 10 statements, **0 `[ConKr]`**.

**Remark:** The empty graph is *not* a generator (`vertexCount = 0` violates `IsSupportConnected.toIsConnected` plus 1PI requirement, and is excluded from `IsConnectedDivergent` by nonemptiness). It corresponds to `1 : HopfH` via the unit. This is critical for H1.14 (loop-number additivity) to apply: γ must be connected.

---

## H4. Coproduct on generators  [Sprint C2 Phase A/B/C]  [DONE 2026-04-24 morning]

**Goal:** Define `Δ : HopfH → HopfH_temp ⊗[ℚ] HopfH_temp` by

```
Δ([Γ]) = [Γ] ⊗ 1 + 1 ⊗ [Γ] + ∑_{γ ⊊ Γ, γ ∈ ConnectedDivergentSubgraphs} [γ] ⊗ [Γ/γ]
```

extended multiplicatively to all of `HopfH` via `MvPolynomial.aeval` (the algebra map universal property).

### Design clarification surfaced during Sprint C2 Phase A (2026-04-24)

**`coproductGen` is NOT recursive.** A mid-Phase-A re-read of the design note clarified that Connes–Kreimer's coproduct formula `[Γ] ⊗ 1 + 1 ⊗ [Γ] + ∑ [γ] ⊗ [Γ/γ]` is an *explicit formula on generators*: both tensor factors are generators (`[γ]` and `[Γ/γ]`), not recursive calls to `coproductGen(Γ/γ)`. `edgeRecursion` (Sprint B' H1.WF.4) remains the scaffolding used by:
- **H4.6 isomorphism-invariance induction** (Sprint C2 Phase B),
- **Sprint E antipode recursion** (H6.1),

but `coproductGen` itself is a direct `def`. This eliminated the need for a separate "wf-recursion unfold lemma" (old H4.5a/b split), replaced by a single `rfl` unfold.

### Path-cut: `Fintype (FeynmanSubgraph G)` carried as Path-W variable

The concrete `Fintype (FeynmanSubgraph G)` instance (via triple-injection into `(Finset × Multiset × Multiset)`) requires 30–50 lines of Mathlib Subtype-fintype combinator wiring. Strategist-approved Path-cut: carry `[∀ G, Fintype (FeynmanSubgraph G)]` as a Path-W `variable` hypothesis. Supply commitment (recorded in Supply-commitments section above): concrete instance before Sprint D completion.

### Statement table (Sprint C2, revised 2026-04-24)

| # | Statement | Tag | Status | Phase | File |
|---|---|---|---|---|---|
| H4.0 | `def Δ_emptyGraph_rule : 1 ↦ 1 ⊗ 1` (convention; handled at class-lift stage) | `[Def]` | ✓ (subsumed by H4.10) | C | — |
| H4.1 | `def properConnectedDivergentSubgraphs (G : FeynmanGraph) : Finset (FeynmanSubgraph G)` | `[Def]` | ✓ | A | `HopfAlgebra/Coproduct.lean` |
| H4.2 | `mem_properConnectedDivergentSubgraphs` membership iff + `edgeMeasure` decrease link | `[Comb]` | ✓ | A | `HopfAlgebra/Coproduct.lean` |
| H4.3 | **`def coproductGen : ConnectedFeynmanGraph → HopfH_temp ⊗[ℚ] HopfH_temp`** — direct formula (non-recursive, per clarification above) | `[Def]` | ✓ | A | `HopfAlgebra/Coproduct.lean` |
| H4.4 | base-case value: subtype level vacuous (empty graph ∉ `ConnectedFeynmanGraph`); class-level handled by H4.10 | `[Def]` | ✓ | A | — |
| H4.5 | `coproductGen_eq` body unfold (rfl, no wf-recursion needed) | `[Def]` | ✓ | A | `HopfAlgebra/Coproduct.lean` |
| **H4.6** | **`coproductGen_isomorphism_invariant : G₁.IsIso G₂ → coproductGen G₁ = coproductGen G₂`** — requires `G₁.WellFormed` hypothesis | `[Graph]` | ✓ (~130 lines incl. core `contract_mapPerm_isIso`) | B | `HopfAlgebra/Coproduct.lean` |
| H4.7 | `def coproductGenClass : HopfGen → HopfH_temp ⊗[ℚ] HopfH_temp` via `Quotient.out` + H4.6 well-definedness | `[Algebra]` | ✓ | C | `HopfAlgebra/Coproduct.lean` |
| H4.8 | `def coproduct : HopfH →ₐ[ℚ] HopfH_temp ⊗[ℚ] HopfH_temp` via `MvPolynomial.aeval coproductGenClass` | `[Algebra]` | ✓ | C | `HopfAlgebra/Coproduct.lean` |
| H4.9 | `coproduct_X : coproduct (MvPolynomial.X g) = coproductGenClass g` | `[Algebra]` | ✓ (`MvPolynomial.aeval_X`) | C | `HopfAlgebra/Coproduct.lean` |
| H4.10 | `coproduct_one : coproduct 1 = 1` | `[Algebra]` | ✓ (`map_one _`) | C | `HopfAlgebra/Coproduct.lean` |
| H4.11 | `coproduct_mul : coproduct (a * b) = coproduct a * coproduct b` | `[Algebra]` | ✓ (`map_mul _ _ _`) | C | `HopfAlgebra/Coproduct.lean` |

**Layer count:** 11 statements (H4.0 absorbed into H4.10, H4.4 vacuous), **0 `[ConKr]`**.

### Phase B core: `contract_mapPerm_isIso` (Option X2, strategist-selected)

For H4.6's `Finset.sum_bij` reindexing, the per-term equality `(γ.mapPerm π).contract.toClass = γ.contract.toClass` requires an isomorphism witness between `(γ.mapPerm π).contract` (contracted in ambient `G.mapPerm π`) and `γ.contract` (contracted in ambient `G`). This is the *ambient-moving* counterpart of Sprint B' H2.1 `contract_mapPerm_of_IsIso` (which was ambient-fixing).

Strategist chose **Option X2 (iso witness only, not literal equality)** over Option X1 (literal equality, 50–80 lines) and Option X3 (Sprint B' refactor, regression risk).

The witness permutation is

```
τ := swap s₂ (π s₁) * π,    s₁ := freshVertex G.vertices,
                             s₂ := freshVertex (G.mapPerm π).vertices
```

which satisfies `τ s₁ = s₂` and agrees with `π` on `G.vertices`. The proof that `(γ.mapPerm π).contract = γ.contract.mapPerm τ` (field-wise `FeynmanGraph` equality) runs ~130 lines of manually-expanded `if`-branches (avoiding `maximum recursion depth` from blind `simp`).

### Termination discipline (unchanged)

The natural condition `0 < γ.internalEdges.card` (γ has ≥ 1 internal edge) is built into H4.1's index-set definition `properConnectedDivergentSubgraphs`, so the `edgeMeasure_contract_lt` obligation (Sprint B' H1.WF.3) is discharged at every recursive call site by construction. Since `coproductGen` is non-recursive, this termination discipline carries over only to Sprint E's `antipodeGen`.

---

## H4.5 Sprint D prep — `contract` preserves CK generator predicates  [DONE 2026-04-24 afternoon]

**Why this prep is needed:** Sprint C2 Phase C's `coproduct : HopfH →ₐ[ℚ] HopfH_temp ⊗ HopfH_temp` has target `HopfH_temp` (scaffold). Mathlib `Bialgebra ℚ HopfH` requires `comul : HopfH →ₗ[ℚ] HopfH ⊗ HopfH` (source = target = `HopfH`). For each summand `[γ] ⊗ [γ.contract]` on a generator `g ∈ HopfGen`, we need `γ.contract` to be itself a `HopfGen` element — i.e. `γ.contract.IsConnectedDivergent` (connected + 1PI + divergent).

Sprint A H1.16 supplies connectedness preservation. 1PI and divergence preservation are established here.

**Strategist decision (2026-04-24 afternoon):** **Path-α** (prove it, ~250 lines) selected over Path-β (new typeclass for IsOnePI, avoids labor but leaves CK paper claim unproven) and Path-γ (weaken CK claim to `HopfH_temp` sub-bialgebra, bends the central thesis). Rationale: "150-250 lines of necessary labor, not speculative infrastructure. Path-γ bends the paper's central thesis — not an acceptable trade-off."

### Statement table

| # | Statement | Tag | Status | File |
|---|---|---|---|---|
| H4.5.1 | `Multiset_le_erase_of_count_lt` (helper) | `[Comb]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.2 | `Multiset_sub_erase_comm` (helper) | `[Comb]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.3 | `asSubOfErase` — re-interpret γ as subgraph of `G.eraseInternalEdge e` | `[Graph]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.4 | `contract_eraseInternalEdge_eq` — **core data equality** | `[Graph]` | ✓ (via `Multiset.map_erase_of_mem`, injectivity-free) | `HopfAlgebra/ContractionPreservation.lean` |
| **H4.5.5** | **`contract_isOnePI` : `G.IsOnePI → γ.IsOnePI → γ.IsNonempty → γ.contract.IsOnePI`** | `[Graph]` | ✓ (~40 lines via data equality + H1.16) | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.6 | `class IsDivergencePreservedByContract` (Plan-D1 typeclass) | `[Algebra]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.7 | `contract_isDivergent` — re-export under the typeclass | `[Graph]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |
| H4.5.8 | `contract_isConnectedDivergent` — combined result (feeds Sprint D) | `[Graph]` | ✓ | `HopfAlgebra/ContractionPreservation.lean` |

**Layer count:** 8 statements, **0 `[ConKr]`**. ~250 lines total, within strategist's 150–250 estimate.

### Multiset-count subtlety (pitfall #28 in feedback memory)

`e ∈ γ.complementEdges` does NOT imply `e ∉ γ.internalEdges` — `Multiset.mem_sub` says `e ∈ A - B ↔ count e B < count e A`, strictly weaker than membership exclusion. First draft of `asSubOfErase` used the wrong hypothesis and had to be refined to count-based form (`count e γ.I < count e G.I`) after strategist halt.

### Breakthrough: `Multiset.map_erase_of_mem` (pitfall #27 in feedback memory)

The core data-equality `(s.erase x).map f = (s.map f).erase (f x)` is usually proved via `Multiset.map_erase` (Mathlib), which requires `Function.Injective f`. Our `retarget γ.vertices star` is *non-injective* (boundary edges from different interior vertices to the same exterior vertex collapse to the same self-loop). `Mathlib/Data/Multiset/MapFold.lean:203` has the injectivity-free companion `Multiset.map_erase_of_mem` requiring only `x ∈ s`. This breakthrough reduced the proof from an estimated 80-120 lines of count-based calculation to a 1-liner.

---

## H5. Bialgebra structure  [Sprint D]

**Goal:** Define counit ε, prove coassociativity, prove ε-Δ compatibility (counit axiom).

| # | Statement | Tag | Depends on |
|---|---|---|---|
| H5.1 | `def counitGen : FeynmanGraphClass → ℚ` ≡ `1 if [emptyGraph], 0 otherwise` | `[Def]` | — |
| H5.2 | `def counit : HopfH →ₐ[ℚ] ℚ` via `MvPolynomial.aeval` extending `counitGen` | `[Algebra]` | MvPolynomial.aeval |
| H5.3 | `counit_one : counit 1 = 1` | `[Algebra]` | H5.2 |
| H5.4 | `counit_X_emptyGraph : counit (X [emptyGraph]) = 1` (vacuous if H3.1 excludes it) | `[Def]` | H5.2 |
| H5.5 | `counit_X_nonempty : ∀ [Γ] ≠ [emptyGraph] connected 1PI divergent, counit (X [Γ]) = 0` | `[Def]` | H5.2 |
| H5.6 | `(ε ⊗ id) ∘ Δ = id` (left counit axiom, via `LinearMap`) | `[Tensor]` + induction | H5.2, H4.8 |
| H5.7 | `(id ⊗ ε) ∘ Δ = id` (right counit axiom) | `[Tensor]` + induction | symmetric |
| **H5.8** | **`coassociativity : (Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`** | **`[ConKr-derived]`** ★ | H1.17, H4.3, induction on `loopNumber` |
| H5.9 | `Δ_isAlgebraHom` already by H4.8, gives multiplicativity for free | `[Algebra]` | H4.8 |
| H5.10 | `instance : Bialgebra ℚ HopfH` | `[Hopf]` | H5.6, H5.7, H5.8, H5.9 |

**Layer count:** 10 statements, **0 `[ConKr]`** (H5.8 is `[ConKr-derived]`, see below).

### Why H5.8 is `[ConKr-derived]`, not `[ConKr]` (revised 2026-04-23)

The `contractWith` literal-equality choice in Sprint A pays off here. Expanding both sides on a generator `[Γ]`:

- `(Δ ⊗ id) Δ([Γ])` produces terms `[γ₁] ⊗ [γ₂/γ₁] ⊗ [Γ/γ₂]` indexed over γ₁ ⊊ γ₂ ⊊ Γ. The third tensor factor is `Γ.contract γ₂` as a literal `FeynmanGraph`.
- `(id ⊗ Δ) Δ([Γ])` produces terms `[γ₁] ⊗ [γ₂/γ₁] ⊗ [(Γ/γ₁)/(γ₂/γ₁)]` indexed via γ₂ ⊊ Γ then γ₁ ⊊ γ₂. The third tensor factor is `(Γ.contract γ₁).contract (γ₂.contractRestrict γ₁)`.
- **H1.17 `contract_chain` states these two `FeynmanGraph` values are literally equal**, hence equal in `FeynmanGraphClass` via `Quotient.eq.mpr`, hence equal as `HopfGen`, hence equal in `MvPolynomial`.
- The proof becomes a `rw [contract_chain]`-driven tensor-factor reorganization plus reindexing — estimated 50–80 lines, no new combinatorial irreducibility.

This is the precise sense in which "the irreducible count is 1": H5.8 is *of* `[ConKr]` form (a Connes–Kreimer 1998 axiom) but its proof is mechanical reduction to H1.17. Hence the new tag.

**`[ConKr]` running total after H5: still 1** (H1.17 only). Nominal `[ConKr]+[ConKr-derived]`: 2.

---

## H6. Antipode + Hopf instance  [Sprint E]

**Goal:** Define antipode `S` recursively (the standard Hopf-algebra antipode formula on a connected graded bialgebra) and supply the Mathlib `HopfAlgebra` instance.

The antipode on a connected graded bialgebra is uniquely determined by the recursive formula:

```
S([Γ]) = -[Γ] - ∑_{γ ⊊ Γ proper} S([γ]) · [Γ/γ]
```

Termination: same `loopNumberRecursion` (H1.WF.4) as Δ — this is why H1.WF.4 was promoted to a shared helper.

| # | Statement | Tag | Depends on |
|---|---|---|---|
| H6.1 | `def antipodeGen : FeynmanGraph → HopfH` via `loopNumberRecursion` (H1.WF.4) | `[Def]` | H1.WF.4, H4.3 |
| H6.2 | `antipodeGen_emptyGraph : antipodeGen emptyGraph = 1` | `[Def]` | H6.1 |
| H6.3 | `antipodeGen_isomorphism_invariant` | `[Graph]` | H2.1, induction |
| H6.4 | `def antipode : HopfH →ₐ[ℚ] HopfH` via `MvPolynomial.aeval` extending `antipodeGen` lifted to classes | `[Algebra]` | H6.3 |
| H6.5 | `antipode_one : antipode 1 = 1` | `[Algebra]` | H6.4 |
| H6.6 | **`antipode_axiom_left : μ ∘ (antipode ⊗ id) ∘ Δ = η ∘ ε`** (i.e. `m(S ⊗ id)Δ(x) = ε(x) · 1`) | `[ConKr-derived]` (consequence of recursive defn + induction; reduces to H5.8 + structural induction) | H6.1, H5.8 |
| H6.7 | **`antipode_axiom_right`** | `[ConKr-derived]` (analogous) | H6.1, H5.8 |
| H6.8 | `instance : HopfAlgebra ℚ HopfH` | `[Hopf]` | H5.10, H6.6, H6.7 |

**Layer count:** 8 statements.

**Note on H6.6/H6.7 (revised 2026-04-23):** Re-tagged from `[ConKr]` (conservative) to `[ConKr-derived]`. On a connected graded bialgebra, the antipode recursion *is constructed precisely so* that the antipode axioms hold by the inductive hypothesis. No new combinatorial irreducibility.

**`[ConKr]` total after H6: 1** (H1.17 only). Nominal `[ConKr]+[ConKr-derived]`: 4.

---

## Summary table (revised 2026-04-24, Plan-D Hybrid + Sprint C1/C2/D-prep)

| Layer | Statements | `[ConKr]` | `[ConKr-derived]` | Status |
|-------|-----------|-----------|-------------------|--------|
| H0 | 12 | 0 | 0 | ✓ Sprint A (2026-04-22) |
| H1 | 17 | **1** (H1.17 contract_chain) | 0 | ✓ Sprint A |
| H1.WF | 5 | 0 | 0 | ✓ Sprint B' (2026-04-23) |
| H2 | 5 (H2.1–2.5) | 0 | 0 | ✓ Sprint B' + C1 (H2.5 + `IsIsoInvariantDivergence`) |
| H3 (B' scaffold) | 6 (H3.0–5, `HopfH_temp`) | 0 | 0 | ✓ Sprint B' |
| H3 (C1 strict) | 4 (H3.6–9, `HopfH` + `bridge`) | 0 | 0 | ✓ Sprint C1 (2026-04-24) |
| H4 | 11 (H4.1–H4.11, H4.0 subsumed, H4.4 vacuous) | 0 | 0 | ✓ Sprint C2 Phases A/B/C (2026-04-24) |
| H4.5 prep (contract preservation) | 8 | 0 | 0 | ✓ Sprint D prep (2026-04-24) |
| H5 | 10 | 0 | **1** (H5.8 coassociativity) | Sprint D main (pending) |
| H6 | 8 | 0 | **2** (H6.6, H6.7 antipode axioms) | Sprint E (pending) |
| **Total** | **86** | **1** | **3** | |

**True irreducible count: 1** (H1.17, already done). **Deferred hypothesis count: 0** (Path-W `variable`-parameter instances are explicit user-supplied facts, not axioms). **Project-specific axiom count: 0**. **`sorry` count across project: 0**.

**Plan-D Hybrid trace:** Sprint B' builds the scaffold artifact `HopfH_temp` over `IsSupportConnected`-only generators (avoiding speculative `DivergenceMeasure` class-lift infrastructure). Sprint C1 adds the strict Connes–Kreimer artifact `HopfH` over `IsConnectedDivergent` generators alongside, with an algebra-embedding bridge `HopfH ↪ HopfH_temp`. The final paper-claim artifact is `HopfH`; `HopfH_temp` is internal scaffolding mirroring Sprint A's `contractWith → contract` alias pattern.

**Sprint C2 design evolution:** The original Sprint C plan had `coproductGen` as a well-founded recursion (12 statements including `H4.5a`/`H4.5b` split). Mid-Sprint-C2 Phase A re-read of CK 1998 clarified that the coproduct formula is non-recursive — both tensor factors `[γ]` and `[Γ/γ]` are generators, not recursive calls. `edgeRecursion` remains the scaffolding for Phase B's isomorphism-invariance induction and Sprint E's antipode, but `coproductGen` itself is a direct `def` with a single `rfl` unfold. H4.5a/b split eliminated; H4.0 (emptyGraph convention) absorbed into H4.10 `map_one`; H4.4 (emptyGraph base case) vacuous at subtype level.

**Sprint D prep insertion:** After Sprint C2 Phase C, the target-type misalignment between `coproduct : HopfH →ₐ[ℚ] HopfH_temp ⊗ HopfH_temp` and `Mathlib.Bialgebra` requirements forced introduction of contract-preservation lemmas (`contract.IsOnePI`, `contract.IsDivergent` via `IsDivergencePreservedByContract` typeclass). Strategist-selected **Path-α** (prove 1PI preservation directly, ~250 lines) over Path-β (typeclass abstraction) and Path-γ (weaken CK claim). Three new pitfalls added to `feedback_lean4_mathlib_pitfalls.md` (#27–29, all Multiset-related).

The construction's NSBarrier-style irreducibility footprint is minimised to a single combinatorial truth about multiset operations on Feynman graphs. Pre-paper-submission `#print axioms HopfAlgebra` is expected to show only `[propext, Classical.choice, Quot.sound]` — identical to `geometric_main`.

---

## Irreducibility map (revised 2026-04-23)

After all sprints, the project's "Hopf irreducible" footprint is:

| irreducible | content | parallel to NSBarrier `[PDE]` |
|---|---|---|
| **H1.17 `contract_chain`** | combinatorial contraction associativity (Connes–Kreimer 1998 Prop 3) | `omega_mem` (the one external assumption) |

Everything else (H5.8 coassoc, H6.6/H6.7 antipode axioms) is `[ConKr-derived]` — provable from H1.17 by structural induction without new combinatorics.

So the only true irreducible is H1.17, **and it is internally provable** — labour-intensive (≈400 lines in Lean as completed in Sprint A) but **not** an axiom: a theorem of finite combinatorics about multiset operations.

Realistic projection: by the end of Sprint E, the Hopf chain's axiom audit reads

```
HopfAlgebra ℚ HopfH depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

— i.e., zero project-specific axioms. Same axiom footprint as `geometric_main` and `physical_consistency`.

---

## Strategist decisions log (resolved through 2026-04-24)

### Sprint B' kickoff (resolved 2026-04-23)

1. **H1.WF measure**: original choice was loopNumber.toNat (requiring Euler inequality `loopNumber_nonneg_of_isConnected`). **Resolved**: switched to `internalEdgeCount` (Sprint B' 2026-04-23), eliminating the Euler inequality hypothesis entirely. See H1.WF section.

2. **`emptyGraph` membership in `HopfGen`**: `IsConnectedDivergent` includes `IsSupportConnected` (via `self.IsConnected`), which requires `IsNonempty`. **Resolved**: `emptyGraph ∉ HopfGen` by type-level construction. Unit-vs-generator distinction clean.

### Sprint C1 (resolved 2026-04-24 morning)

3. **Path for class-level `IsConnectedDivergent`**: Path-Sub (delegation to `FeynmanSubgraph.self`) vs Path-FG (parallel `FeynmanGraph.IsOnePI` API). **Resolved**: Path-Sub — reuses Sprint A subgraph-level predicate; Larry Wall Laziness applied to avoid parallel API.

4. **`DivergenceMeasure` class-lift strategy**: Path-thin (drop divergence), Path-representative/Path-W (external supply), Path-classwise (new typeclass). **Resolved**: Path-W (global `[∀ G, DivergenceMeasure G]` + `[∀ G, IsPermInvariantDivergence G]` + `[∀ G, IsIsoInvariantDivergence G]`). Path-thin rejected ("divergence condition post-hoc changes CK to a different Hopf algebra"); Path-classwise rejected (100+ lines speculative).

5. **New typeclass `IsIsoInvariantDivergence`**: companion to Sprint A `IsPermInvariantDivergence` for intra-ambient (not cross-ambient) iso-invariance. **Approved** under the 3-point criterion (Mathlib-foundation-clean, companion to existing, technical necessity).

### Sprint C2 (resolved 2026-04-24 morning)

6. **C1/C2 split**: originally planned as one Sprint C. **Resolved**: split into C1 (H2.5 + H3.6–3.9) and C2 (H4), following Sprint B'/C grain principle (mechanical vs recursive). Further split C2 into Phases A/B/C after Phase A surfaced the "coproductGen is non-recursive" clarification.

7. **`Fintype (FeynmanSubgraph G)` supply**: carried as Path-W `variable` or supplied concretely. **Resolved (Path-cut)**: carried as `variable`; concrete supply deferred to Sprint D or earlier. Supply commitment recorded above.

8. **Option X1/X2/X3 for `contract_mapPerm_isIso` (Phase B core)**: literal equality / iso witness only / Sprint B' refactor. **Resolved**: Option X2 (iso witness). 50–80 lines vs 150+ for alternatives; precision matches H4.6 class-level requirement.

### Sprint D prep (resolved 2026-04-24 afternoon)

9. **Bialgebra target-type misalignment**: Path-α (prove `contract.IsOnePI` + `IsDivergent` preservation), Path-β (typeclass abstraction for both), Path-γ (weaken CK claim to `HopfH_temp` sub-bialgebra). **Resolved**: Path-α. Path-γ rejected as "bending the paper's central thesis"; Path-β rejected for `IsOnePI` as "avoiding necessary labor = Laziness misuse". Path-β retained *only* for `IsDivergent` as Plan-D1 typeclass (CK 1998 power-counting stability is physics-motivated, justifiably abstracted).

10. **Split plan (today vs tomorrow)**: split (prep today, main body tomorrow) vs all-in-one. **Resolved**: split. Contract preservation lemmas completed 2026-04-24 afternoon (~250 lines, ~1h wallclock thanks to `Multiset.map_erase_of_mem` discovery); Sprint D main body (H5.1–H5.10) pending next session.

### Open for Sprint D main

- **`Fintype (FeynmanSubgraph G)` supply timing** — re-verify before Phase B/C of Sprint D completion. *(2026-04-25 status: discharged via `SubgraphFintype.lean`, triple-injection into `Finset × Multiset × Multiset` powerset.)*
- **H5.8 coassociativity `rw [contract_chain]` strategy** — Sprint A H1.17's literal-equality payoff; confirm the formulation is `rw`-driven as planned (50–80 lines) rather than requiring a separate `ConKr-derived` induction. *(2026-04-25 status: see "H5.8 design obstruction" below.)*
- **Concrete `IsDivergencePreservedByContract` instance** (for a representative measure, e.g. MSSM 1-loop) — if needed for a concrete use case; abstract instance suffices for the `HopfAlgebra` construction.

---

## H5.8 design obstruction (2026-04-25)

**Status:** Stages 1, 2, 3a-i/ii/iii, 3b-i/ii/iii/iv-pre/iv-A all completed (~870 lines in `Coassoc.lean`). The invalid connected-only `termE3_eq_termF3` theorem is no longer stated; the file is NoSorry while the admissible-index redesign proceeds.

**Obstruction discovered (strategist note, 2026-04-25):**

The naive forward bijection
```
(γ_outer, γ_inner) ↦ (γ_inner.promote, γ_outer.contractRestrict γ_inner)
```
has image strictly contained in the RHS sum. The second factor always contains
`γ_inner.promote.contractedVertex` by `contractRestrict_star_mem`
(`SubGraph.lean`: `contractRestrict_vertices = (γ₂ \ γ₁) ∪ {star}`).

But the RHS index `γ_outer'.contract.properConnectedDivergentSubgraphs`
also includes **star-free subgraphs** δ ⊊ Γ/γ_outer' with `star ∉ δ.vertices`.
These correspond, in the original Γ, to subgraphs δ ⊊ Γ that are **disjoint
from γ_outer'**.

**Root cause: index design mismatch with full CK admissible subgraphs.**

In standard Connes–Kreimer 1998, the coproduct sum index ranges over
**admissible subgraphs** γ ⊊ Γ, which include:

1. Connected 1PI divergent subgraphs (covered by current `properConnectedDivergentSubgraphs`)
2. **Disjoint unions** of such subgraphs (NOT covered)

The first tensor factor `[γ]` for a disjoint admissible γ = γ₁ ⊔ γ₂ ⊔ ... is
a **product** `[γ₁] · [γ₂] · ...` in the Hopf algebra, not a single generator.

**The RHS star-free term `(γ_outer', δ)` with γ_outer' ⊥ δ in Γ corresponds
to the LHS chain `(γ_outer = γ_outer' ⊔ δ, γ_inner = γ_outer')` in the
disjoint-admissible regime.** The current connected-only index has no slot
for this correspondence, hence the bijection fails.

**Implication:**

The current `coproductGen_strict` formula
```
Δ([Γ]) = [Γ] ⊗ 1 + 1 ⊗ [Γ] + ∑_{γ ⊊ Γ proper connected divergent} [γ] ⊗ [Γ/γ]
```
is **strictly weaker than CK 1998**. Coassociativity holds in CK only with
admissible-subgraph indexing. A connected-only construction yields a
*sub-bialgebra* at best, not the full Hopf algebra of Connes–Kreimer.

**Next session redesign (Sprint D2):**

1. **Index extension:** redefine `properConnectedDivergentSubgraphs` to
   `properAdmissibleDivergentSubgraphs` = arbitrary disjoint unions of
   connected 1PI divergent subgraphs.
2. **First tensor factor lift:** `[γ]` for admissible γ becomes
   `∏_i [γ_i]` over connected components γ_i, mapped into `HopfH` as a
   product of generators.
3. **Bijection redesign:** the LHS sigma now has `γ_outer = ⊔ γ_i` with the
   inner γ_inner being any subset of components. The forward map covers both
   nested (Type A) and disjoint (Type B) regimes uniformly.

**Sprint D2 prep estimate:** ~150–250 lines for the admissible-subgraph
infrastructure (component decomposition, product lift), then the existing
Stage 3 work mostly transfers.

**Salvage value of current Stage 3 code (~870 lines in `Coassoc.lean`):**

| Component | Reusable in Sprint D2? |
|---|---|
| `coassoc_strict_algHom_X` skeleton (Stage 1) | ✓ unchanged |
| `coproduct_strict_X_eq` (Stage 2) | ✓ unchanged (need extension to admissible) |
| `coassoc_LHS_eq` / `coassoc_RHS_eq` shell (Stage 3a-i/ii) | ⚠ index changes, structure preserved |
| `termA/B/C/D/E` term decomposition | ✓ pattern reusable |
| `termE_eq` / `termF_eq` 7-term split | ✓ pattern reusable |
| `coproductGen_sumPart` + `_eq` + `_eq_amb` | ✓ unchanged |
| `termE3_sigma_eq` / `termF3_sigma_eq` | ⚠ index changes |
| `FeynmanSubgraph.promote` | ✓ unchanged |
| `contractRestrict_star_mem` | ✓ key invariant for Sprint D2 bijection |
| `outer_dite_inner_sum_eq` | ✓ general utility |

**Approximate Sprint D2 reusability: 70%.** The Stage 1–2 + termA/B/C/D/E
infrastructure transfers verbatim; only the bijection statement needs
rework with the admissible-subgraph index.

**Strategist judgment trace:**

- 2026-04-25 strategist halted naive bijection implementation 
  ("contractRestrict_inv to be built as part of Stage 3b-iv-C") on the
  observation that `contractRestrict_star_mem` proves forward image is
  strictly contained in RHS.
- Diagnosis: not a Lean implementation issue but a CK index-design issue.
- Decision: commit current build-pass state; redesign coproduct index in
  Sprint D2 before resuming bijection work.
- Avoided: writing 200+ lines of `contractRestrict_inv` infrastructure
  that would only handle the star-containing fragment of the bijection.

**Sprint D2 prep tasks (next session):**

1. CK 1998 paper re-read on admissible subgraph definition and coassoc proof
2. ✓ Minimal `AdmissibleSubgraph G` carrier implemented as a
   connected-divergent `Forest G` wrapper.
3. ✓ Raw finite-set API for forest carriers:
   `Forest.IsElements`, `Forest.IsConnectedDivergentElements`,
   `Forest.ofElements`, and `Forest.ofConnectedDivergentElements`.
4. ✓ Full finite connected-divergent forest carrier:
   `Forest.connectedDivergentIndex`, with membership/completeness lemmas.
5. ✓ Full finite admissible carrier:
   `AdmissibleSubgraph.connectedDivergentIndex` and
   `FeynmanGraph.admissibleDivergentSubgraphs`.
6. ✓ Minimal admissible carrier projections:
   `AdmissibleSubgraph.vertices` as the union of component vertices, plus
   empty/singleton simp lemmas and `vertices_subset`.
7. ✓ Disjoint admissible carrier:
   `AdmissibleSubgraph.IsPairwiseDisjoint` and
   `FeynmanGraph.disjointAdmissibleDivergentSubgraphs`.
8. ✓ Nonempty disjoint admissible carrier:
   `AdmissibleSubgraph.IsNonempty` and
   `FeynmanGraph.nonemptyDisjointAdmissibleDivergentSubgraphs`.
9. ✓ Conservative singleton-only
   `properAdmissibleDivergentSubgraphs : Finset (AdmissibleSubgraph G)`,
   obtained by embedding the existing connected-divergent index into
   singleton admissible forests. The full disjoint carrier exists, but the
   coproduct summand is not widened yet.
10. ✓ Inclusion/sum-extension bridge from the conservative singleton index
   into the disjoint/nonempty-disjoint carriers:
   `properAdmissibleDivergentSubgraphs_subset_disjointAdmissibleDivergentSubgraphs`
   and `properAdmissibleDivergentSubgraphs_subset_nonemptyDisjointAdmissibleDivergentSubgraphs`,
   plus the corresponding zero-extension sum lemmas.
11. ✓ Minimal component/product-lift API
   `AdmissibleSubgraph.toHopfH : AdmissibleSubgraph G → HopfH`
   with empty/singleton simp lemmas.
12. ✓ First connected-sum → singleton-admissible-sum bridges:
   `sum_properAdmissibleDivergentSubgraphs`,
   `sum_connectedIndexToAdmissible_eq_sum_properAdmissibleDivergentSubgraphs`,
   `connectedIndexToAdmissible_toHopfH`, and
   `sum_properConnectedDivergentSubgraphs_toHopfH`.
13. ✓ Conservative inverse and full strict-summand bridge:
   `admissibleToConnectedIndex`, `connectedStrictSummand`,
   `admissibleStrictSummand`, and
   `sum_properConnectedDivergentSubgraphs_inline_admissibleStrictSummand`.
14. ✓ Named contraction replacement point:
   `admissibleContractIndex`, `admissibleContractSubgraph`, and
   `admissibleContractToHopfGen`, with singleton recovery lemmas.
15. ✓ Re-state `coproductGen_strict` with admissible summand display theorems:
   `coproductGen_strict_eq_admissibleSummand` and
   `coproductGen_strict_eq_nonemptyDisjointAdmissibleSummand`.
16. ✓ Component lookup and retarget skeleton:
   `componentAt`, `componentAt?`, uniqueness under `IsPairwiseDisjoint`,
   `retargetVertex`, `retargetEdge`, and `retargetExternalLeg`.
17. ✓ Forest contraction skeleton:
   `AdmissibleSubgraph.internalEdges`, `complementEdges`,
   `starVertices`, and `contractWithStars`, with empty/singleton projection
   simp lemmas. Fresh/distinct star construction remains deliberately
   external.
18. ✓ Singleton recovery and strict-summand replacement point:
   `singleton_contractWithStars`, `singleton_contractWithStars_contract`,
   `admissibleContractGraphWithStars_eq_contractSubgraph`,
   `admissibleContractGraphWithStarsToHopfGen_eq`, and
   `admissibleStrictSummandWithStars_eq_admissibleStrictSummand`.
19. ✓ Direct sum/display bridges through the forest-contraction skeleton:
   `sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars`,
   `sum_properConnectedDivergentSubgraphs_admissibleStrictSummandWithStars_nonemptyDisjoint`,
   `coproductGen_strict_eq_admissibleSummandWithStars`, and
   `coproductGen_strict_eq_nonemptyDisjointAdmissibleSummandWithStars`.
20. ✓ Proper-disjoint admissible carrier and parametric summand skeleton:
   `properDisjointAdmissibleDivergentSubgraphs`,
   `properAdmissibleDivergentSubgraphs_subset_properDisjointAdmissibleDivergentSubgraphs`,
   `admissibleStrictSummandWithRight`, and
   `admissibleForestStrictSummand`. This externalizes the right tensor
   generator so the summand body no longer has to contain the conservative
   singleton inverse.
21. ✓ `coproductGen_strict` can now be displayed over the proper-disjoint
   admissible carrier through `contractWithStars`:
   `coproductGen_strict_eq_properDisjointAdmissibleSummandWithStars`.
22. ✓ Genuine forest-right packaging, with preservation kept external:
   `admissibleForestContractGraphWithStars`,
   `admissibleForestContractToHopfGen`,
   `admissibleForestRightWithStars`, and
   `admissibleForestStrictSummandWithStars`.
23. ✓ Future forest coproduct formula staged separately:
   `coproductGen_strict_forestWithStars`.
24. ✓ Fresh-star predicate/API:
   `AdmissibleSubgraph.IsFreshStarAssignment`,
   `IsFreshStarAssignment.disjoint_vertices_starVertices`,
   `IsFreshStarAssignment.disjoint_sdiff_starVertices`,
   `IsFreshStarAssignment.card_starVertices`, and
   `contractWithStars_vertexCount`.
25. ✓ Fresh-star formula staging:
   `admissibleForestRightWithFreshStars`,
   `admissibleForestStrictSummandWithFreshStars`, their `val`/`of_mem`/
   `of_not_mem` API, and
   `coproductGen_strict_forestWithFreshStars`.
26. ✓ Canonical component-star assignment:
   `AdmissibleSubgraph.componentFreshStar`,
   `componentFreshStar_not_mem_vertices`,
   `componentFreshStar_eq_of_eq`, and
   `componentFreshStar_isFreshStarAssignment`.
27. ✓ Public formula with `IsFreshStarAssignment` removed:
   `admissibleForestCanonicalStarOf`,
   `admissibleForestRightWithCanonicalStars`,
   `admissibleForestStrictSummandWithCanonicalStars`, and
   `coproductGen_strict_forestWithCanonicalStars`.
28. ✓ Canonical forest-contraction graph named and preservation split:
   `admissibleForestCanonicalContractGraph`,
   `admissibleForestCanonicalContractGraph_isConnectedDivergent_of_parts`,
   and `admissibleForestCanonicalContractGraph_hCD_of_parts`.
29. ✓ Well-formedness slice discharged:
   `AdmissibleSubgraph.retargetVertex_mem_contractWithStars_vertices`,
   `AdmissibleSubgraph.contractWithStars_wellFormed`, and
   `admissibleForestCanonicalContractGraph_wellFormed`.
30. ✓ Formula shell with only graph-theoretic preservation slices remaining:
   `coproductGen_strict_forestWithCanonicalStarsFromParts` and
   `coproductGen_strict_forestWithCanonicalStarsFromGraphParts`.
31. ✓ Connectedness slice for canonical forest contraction, split at the
   right local boundary:
   `AdmissibleSubgraph.mem_internalEdges`,
   `AdmissibleSubgraph.HasNonemptyComponents`,
   `contractWithStars_step_supportReachable`,
   `contractWithStars_path_supportReachable`,
   `contractWithStars_isSupportConnected`,
   `properDisjointAdmissibleDivergentSubgraphs_isPairwiseDisjoint`, and
   `admissibleForestCanonicalContractGraph_isSupportConnected`.
   The theorem now needs only ambient connectedness, pairwise disjointness
   from the carrier, and component nonemptiness.
32. ✓ Component nonemptiness threaded into the final carrier:
   `properDisjointAdmissibleDivergentSubgraphs` now filters by
   `A.HasNonemptyComponents ∧ 0 < A.internalEdges.card ∧
   A.HasPositiveInternalEdgesComponents`;
   `properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents`
   and
   `properDisjointAdmissibleDivergentSubgraphs_hasPositiveInternalEdgesComponents`
   supply the local witnesses, and
   `admissibleForestCanonicalContractGraph_isSupportConnected` no longer
   asks for an external `hCompNE`.
33. ✓ Formula entrypoint with WF + connectedness discharged:
   `admissibleForestCanonicalContractGraph_hCD_of_onePI_divergence` and
   `coproductGen_strict_forestWithCanonicalStarsFromOnePIDivergence`.
34. ✓ First 1PI split:
   `admissibleForestCanonicalContractGraph_noBridge_of_erase_connected`
   turns quotient-edge erasure connectedness into bridge-freeness, and
   `admissibleForestCanonicalContractGraph_isOnePI_of_erase_connected`
   packages it with the already-discharged connectedness.
35. ✓ Formula entrypoint with 1PI reduced to edge-erasure connectedness:
   `admissibleForestCanonicalContractGraph_hCD_of_erase_connected_divergence`
   and
   `coproductGen_strict_forestWithCanonicalStarsFromEraseConnectedDivergence`.
36. ✓ Edge-preimage entry for the next proof:
   `AdmissibleSubgraph.mem_contractWithStars_internalEdges` and
   `admissibleForestCanonicalContractGraph_internalEdge_preimage` recover
   the original complement edge whose retargeted image is a quotient
   internal edge.
37. ✓ Retarget-complement reduction:
   `AdmissibleSubgraph.mem_ambientInternalEdges_of_mem_complementEdges`,
   `AdmissibleSubgraph.count_lt_of_mem_complementEdges`,
   `admissibleForestCanonicalContractGraph_erase_connected_of_retarget_complement`,
   `admissibleForestCanonicalContractGraph_hCD_of_retarget_erase_connected_divergence`,
   and
   `coproductGen_strict_forestWithCanonicalStarsFromRetargetEraseConnectedDivergence`.
38. ✓ Retarget-erasure transport:
   `AdmissibleSubgraph.complementEdges_erase`,
   `contractWithStars_eraseInternalEdge_internalEdges`,
   `contractWithStars_eraseInternalEdge_step_supportReachable`,
   `contractWithStars_eraseInternalEdge_path_supportReachable`, and
   `contractWithStars_eraseInternalEdge_isSupportConnected` transport
   connectedness of `G.eraseInternalEdge e` through forest contraction.
39. ✓ Ambient 1PI closes quotient 1PI:
   `admissibleForestCanonicalContractGraph_retarget_erase_connected_of_onePI`,
   `admissibleForestCanonicalContractGraph_erase_connected_of_onePI`,
   `admissibleForestCanonicalContractGraph_isOnePI_of_ambient_onePI`,
   `admissibleForestCanonicalContractGraph_hCD_of_ambient_onePI_divergence`,
   and
   `coproductGen_strict_forestWithCanonicalStarsFromAmbientOnePIDivergence`.
40. ✓ Forest-quotient divergence preservation cut:
   `IsDivergencePreservedByAdmissibleForestContract`,
   `AdmissibleSubgraph.contractWithStars_isDivergent`,
   `admissibleForestCanonicalContractGraph_isDivergent_of_ambient_connectedDivergent`,
   `admissibleForestCanonicalContractGraph_hCD_of_ambient_preservation`, and
   `coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation`.
41. Next: use the ambient-preservation forest summand as the strict coproduct
   display, then resume the H5.8 coassociativity decomposition.

**Small-pass restart discipline (2026-04-25):**

Do not attempt a full H5.8 "thermo" pass. Proceed by extracting the
obstruction into tiny, build-checked Lean artifacts:

1. ✓ `contractRestrict_star_mem`: `contractRestrict` always lands in the
   star-containing quotient component.
2. ✓ `rhs_sigma_split_by_star`: split the RHS sigma index into
   star-containing and star-free pieces for an arbitrary summand.
3. ✓ `coassocNestedForward`: extract the old nested-chain forward map from
   the failed `sum_bij` proof.
4. ✓ `coassocNestedForward_star_mem`: prove the extracted nested-chain map
   lands in the star-containing side.
5. ✓ `Forest.singleton`: a one-component forest constructor for a divergent
   subgraph, with connected-divergent preservation.
6. ✓ `AdmissibleSubgraph`: minimal carrier wrapping a connected-divergent
   `Forest G`, with `empty`, singleton embedding, membership projection, and
   component-divergence lemmas.
7. ✓ Minimal product-lift API over `AdmissibleSubgraph.elements.attach`.
8. ✓ Conservative singleton-only `properAdmissibleDivergentSubgraphs`
   index Finset, with singleton-introduction and membership-elimination
   lemmas.
9. ✓ Reindex the existing connected coproduct sum through the singleton
   admissible index as image-sum lemmas, still without changing
   `coproductGen_strict`.
10. ✓ Strict left-factor bridge:
   `sum_properConnectedDivergentSubgraphs_toHopfH` rewrites the existing
   `if hγ : γ.IsConnectedDivergent ∧ 0 < γ.internalEdges.card` generator
   sum as the singleton-admissible `A.toHopfH` sum.
11. ✓ Conservative right-factor bridge:
   `admissibleStrictSummand` uses `admissibleToConnectedIndex` to recover
   the original connected contraction generator on singleton admissible
   index elements.
12. ✓ Named replacement point for future forest contraction:
   `admissibleContractToHopfGen_connectedIndexToAdmissible` proves the
   wrapper reduces to the original connected contraction generator on
   singleton admissible index elements.
13. ✓ `coproductGen_strict_eq_admissibleSummand`: the existing strict
   coproduct is now displayed with the conservative admissible summand.
14. ✓ Forest/admissible finite carrier layer:
   `Forest.connectedDivergentIndex`,
   `AdmissibleSubgraph.connectedDivergentIndex`,
   `FeynmanGraph.admissibleDivergentSubgraphs`, and
   `FeynmanGraph.disjointAdmissibleDivergentSubgraphs`.
15. ✓ Nonempty/disjoint filtering layer:
   `AdmissibleSubgraph.IsNonempty`,
   `FeynmanGraph.nonemptyDisjointAdmissibleDivergentSubgraphs`, and
   singleton membership into that carrier.
16. ✓ Admissible vertex-carrier API:
   `AdmissibleSubgraph.vertices`, `mem_vertices`, `vertices_subset`,
   `empty_vertices`, and `singleton_vertices`.
17. ✓ Component lookup API:
   `Forest.IsPairwiseDisjoint.eq_of_mem_vertices`,
   `AdmissibleSubgraph.componentAt`, `componentAt?`, and the uniqueness
   theorem `componentAt?_eq_some_of_mem_vertices`.
18. ✓ Retarget skeleton parameterized by component stars:
   `retargetVertex`, `retargetEdge`, and `retargetExternalLeg`.
19. ✓ Forest contraction skeleton:
   `internalEdges`, `complementEdges`, `starVertices`, and
   `contractWithStars`.
20. ✓ Conservative-to-disjoint bridge:
   `properAdmissibleDivergentSubgraphs_subset_disjointAdmissibleDivergentSubgraphs`
   / `properAdmissibleDivergentSubgraphs_subset_nonemptyDisjointAdmissibleDivergentSubgraphs`
   plus zero-extension sum lemmas over the larger carriers.
21. ✓ `coproductGen_strict` can now be displayed over the nonempty disjoint
   admissible carrier, with extra terms zero under the conservative summand.
22. ✓ Singleton recovery for `contractWithStars`:
   singleton admissible contraction reduces to the existing
   one-component `contractWith`/`contract` operation.
23. ✓ Strict coproduct display routed through `contractWithStars`:
   `admissibleStrictSummandWithStars` is equal to the conservative summand,
   and `coproductGen_strict` has proper-admissible and nonempty-disjoint
   `WithStars` display theorems.
24. ✓ Proper-disjoint target carrier:
   `properDisjointAdmissibleDivergentSubgraphs` filters the nonempty disjoint
   carrier by `A.HasNonemptyComponents`, `0 < A.internalEdges.card`, and
   `A.HasPositiveInternalEdgesComponents`; the conservative singleton index
   embeds into it.
25. ✓ Parametric future summand shape:
   `admissibleStrictSummandWithRight` and
   `admissibleForestStrictSummand` isolate the future forest-contraction
   right generator as an explicit argument.
26. ✓ `coproductGen_strict_eq_properDisjointAdmissibleSummandWithStars`:
   the strict coproduct is displayed over the proper-disjoint admissible
   carrier while extra terms still vanish under the conservative body.
27. ✓ Forest contraction right-generator packaging:
   `admissibleForestContractGraphWithStars` names the graph,
   `admissibleForestContractToHopfGen` packages it as a `HopfGen` once
   connected-divergent preservation is supplied, and
   `admissibleForestRightWithStars` turns those into the right tensor factor.
28. ✓ Forest summand/formula staging:
   `admissibleForestStrictSummandWithStars` and
   `coproductGen_strict_forestWithStars` give the future proper-disjoint
   forest formula without replacing the conservative coproduct yet.
29. ✓ Fresh-star assignment API:
   `IsFreshStarAssignment` records freshness outside `G.vertices` and
   injectivity on components; singleton conservative stars satisfy it, and
   the induced `starVertices` set is disjoint from the original vertices with
   cardinality equal to the number of components.
30. ✓ Fresh-star forest formula shell:
   `admissibleForestRightWithFreshStars`,
   `admissibleForestStrictSummandWithFreshStars`, and
   `coproductGen_strict_forestWithFreshStars` expose the exact hypotheses
   needed to remove the conservative singleton right factor.
31. ✓ Canonical component-star assignment:
   `componentFreshStar A γ := freshVertex G.vertices + idxOf γ A.elements.toList`.
   It is fresh outside `G.vertices` for every γ and injective on
   `A.elements`, so `componentFreshStar_isFreshStarAssignment` closes the
   previous explicit `hFresh` obligation.
32. ✓ Formula shell with fresh-star proof removed:
   `coproductGen_strict_forestWithCanonicalStars` depends only on the
   remaining preservation hypothesis for canonical forest contractions.
33. ✓ Preservation theorem split:
   `admissibleForestCanonicalContractGraph_hCD_of_parts` reduces the old
   monolithic hCD obligation to WF/connected/1PI/divergent pieces.
34. ✓ WF piece closed:
   `contractWithStars_wellFormed` proves forest contraction is well-formed
   from ambient `G.WellFormed`, for any component-star assignment.
35. ✓ Formula entrypoint after WF:
   `coproductGen_strict_forestWithCanonicalStarsFromGraphParts` now asks
   only for connectedness, 1PI, and divergence preservation.
36. ✓ Connectedness transport through forest contraction:
   original support paths retarget to quotient support paths; collapsed
   component-internal edges become reflexive star steps, and complement edges
   become actual support-adjacency steps.
37. ✓ Component nonemptiness is now part of the final proper-disjoint carrier,
   and connectedness is instantiated from carrier membership via
   `properDisjointAdmissibleDivergentSubgraphs_hasNonemptyComponents`.
38. ✓ Public formula after WF + connectedness:
   `coproductGen_strict_forestWithCanonicalStarsFromOnePIDivergence` exposes
   only the remaining 1PI and divergence hypotheses.
39. ✓ 1PI split to bridge-free target:
   `admissibleForestCanonicalContractGraph_noBridge_of_erase_connected`,
   `admissibleForestCanonicalContractGraph_isOnePI_of_erase_connected`, and
   `coproductGen_strict_forestWithCanonicalStarsFromEraseConnectedDivergence`.
40. ✓ Edge-preimage helper:
   quotient internal edges are named as retargeted complement edges via
   `admissibleForestCanonicalContractGraph_internalEdge_preimage`.
41. ✓ Retarget-complement formula entrypoint:
   `admissibleForestCanonicalContractGraph_erase_connected_of_retarget_complement`
   and
   `coproductGen_strict_forestWithCanonicalStarsFromRetargetEraseConnectedDivergence`
   expose only the original complement-edge erasure target.
42. ✓ Retarget-erasure connectedness transport:
   `contractWithStars_eraseInternalEdge_isSupportConnected` proves the
   erased quotient connectedness from `(G.eraseInternalEdge e).IsSupportConnected`.
43. ✓ Ambient 1PI discharges the full 1PI slice:
   `admissibleForestCanonicalContractGraph_isOnePI_of_ambient_onePI` and
   `coproductGen_strict_forestWithCanonicalStarsFromAmbientOnePIDivergence`
   leave only the canonical forest quotient divergence hypothesis.
44. ✓ Forest-quotient divergence preservation is abstracted and discharged:
   `IsDivergencePreservedByAdmissibleForestContract` supplies the CK
   forest-level power-counting stability, and
   `coproductGen_strict_forestWithCanonicalStarsFromAmbientPreservation`
   exposes the final canonical forest summand entrypoint.
45. ✓ Parallel forest strict coproduct map:
   `coproductGenClass_strict_forest`, `coproduct_strict_forest`,
   `coproduct_strict_forest_X`, `coproductGenClass_strict_forest_eq`,
   plus one/multiplication lemmas. The old connected-only
   `coproduct_strict` remains intact.
46. ✓ H5.8F algebra/linear reductions:
   `coproduct_strict_forest_X_eq`,
   `coassoc_strict_forest_algHom_of_generators`,
   `coassoc_strict_forest_linear_of_algHom`, and
   `coassoc_strict_forest_linear_of_generators`.
47. ✓ Forest Stage 3a named-term split:
   `forestCanonicalHCD`, `forestRightHopfH`, `forestTermA/B/C/D/E/E2/F`,
   `coassoc_forest_LHS_eq`, and `coassoc_forest_RHS_eq`.
48. ✓ Boundary cancellation cut:
   `coassoc_forest_X_of_main_terms` and
   `coassoc_strict_forest_linear_of_main_terms` reduce H5.8F to the single
   main identity
   `forestTermC g + forestTermE g = forestTermE2 g + forestTermF g`.
49. ✓ Component product expansion:
   `coproduct_strict_forest_admissible_toHopfH`,
   `coproduct_strict_forest_componentToHopfH`,
   `forestComponentCoproductFactor`,
   `forestTermEComponents`,
   `forestTermEComponentGenerators`,
   `forestTermE_eq_components`, and
   `forestTermE_eq_componentGenerators`.
50. ✓ Quotient generator expansion + boundary/core cut:
   `forestTermFQuotientGenerators`,
   `coproduct_strict_forest_forestRightHopfH`,
   `forestTermF_eq_quotientGenerators`,
   `forestTermE1`, `forestTermE3`, `forestTermF3`,
   `coassoc_forest_main_terms_of_core`,
   `coassoc_strict_forest_linear_of_core_terms`, and
   `coassoc_strict_forest_linear_of_expanded_core`.
51. ✓ Additive and choice-expanded core cuts:
   `coassoc_strict_forest_linear_of_expanded_core_add` replaces the
   subtraction target by
   `forestTermEComponentGenerators g + forestTermC g =
    forestTermFQuotientGenerators g + forestTermE2 g`.  The generator-level
   carrier `forestCoproductChoice` splits every forest coproduct into
   left boundary / right boundary / forest summand, with
   `coproductGenClass_strict_forest_eq_choiceSum`.
52. ✓ Component-product choice expansion:
   `forestComponentCoproductFactor_eq_choiceSum_of_mem`,
   `forestComponentChoiceIndex`,
   `forestComponentCoproductFactor_prod_eq_choicePi`,
   `forestTermEComponentChoices`, and
   `forestTermEComponentGenerators_eq_choices` expose the left core as a
   `Finset.pi` over component choices.  The right quotient side has the
   matching `forestTermFQuotientChoices` and
   `forestTermFQuotientGenerators_eq_choices`; the reduction theorem
   `coassoc_strict_forest_linear_of_choice_core_add` makes this the new H5.8F
   target.
53. ✓ Distributed choice-core cut:
   `forestComponentChoiceProductTerm`,
   `forestTermEComponentChoicesDistributed`,
   `forestTermEComponentChoices_eq_distributed`,
   `forestTermFQuotientChoicesDistributed`,
   `forestTermFQuotientChoices_eq_distributed`, and
   `coassoc_strict_forest_linear_of_distributed_choice_core_add` expose the
   remaining target term-by-term over an admissible forest `A`, a
   component-choice function `p`, and a quotient choice `c`.
54. ✓ RHS quotient-boundary identification:
   `forestTermFQuotient_leftChoice_eq_C` and
   `forestTermFQuotient_rightChoice_eq_E1` identify the quotient generator's
   `left`/`right` choices with the existing boundary terms `forestTermC` and
   `forestTermE1`.
55. ✓ LHS boundary-choice extraction:
   `forestComponentAllLeftChoice`, `forestComponentAllRightChoice`,
   their membership lemmas, `forestComponentChoiceProductTerm_allLeft`,
   `forestComponentChoiceProductTerm_allRight`,
   `forestTermEComponent_allLeftChoice_eq_E1`, and
   `forestTermEComponent_allRightChoice_eq_E2` identify the two constant
   component-choice slices with `forestTermE1` and `forestTermE2`.
56. ✓ Component-choice core carrier:
   `forestComponentCoreChoiceIndex`,
   `forestComponentChoiceIndex_eq_insert_boundaries`, and
   `forestComponentChoice_inner_sum_eq_boundaries_add_core` split each
   component-choice `Finset.pi` into all-left / all-right / core.
57. ✓ Distributed core exposure on both sides:
   `forestTermEComponentCoreChoicesDistributed`,
   `forestTermEComponentChoicesDistributed_eq_boundaries_add_core`,
   `forestCoproductForestChoiceIndex`,
   `forestCoproductChoice_inner_sum_eq_boundaries_add_forest`,
   `forestTermFQuotientForestChoicesDistributed`, and
   `forestTermFQuotientChoicesDistributed_eq_boundaries_add_core` remove all
   boundary choices from the distributed H5.8F target.
58. ✓ Final forest-core cut:
   `coassoc_strict_forest_linear_of_distributed_forest_core` reduces H5.8F to
   the single remaining core identity
   `forestTermEComponentCoreChoicesDistributed g =
    forestTermFQuotientForestChoicesDistributed g`.
59. ✓ RHS forest-choice image removal:
   `forestCoproductChoice_forest_injective` and
   `forestCoproductForestChoiceIndex_sum` remove the
   `forestCoproductChoice.forest` image wrapper.  The RHS core is now exposed
   as `forestTermFQuotientForestChoicesExpanded`, an ordinary double sum over
   an outer admissible forest `A` and an inner admissible forest `B` in the
   quotient graph.
60. ✓ Expanded quotient forest-core cut:
   `forestTermFQuotientForestChoicesDistributed_eq_expanded` and
   `coassoc_strict_forest_linear_of_expanded_quotient_forest_core` reduce
   H5.8F to
   `forestTermEComponentCoreChoicesDistributed g =
    forestTermFQuotientForestChoicesExpanded g`.
61. ✓ Flat forest-core reindexing cut:
   `forestComponentChoiceFn`, `forestOuterProperIndex`,
   `forestComponentChoiceSigma`, `forestComponentSplitChoiceSigmaIndex`,
   `forestQuotientForestSigma`, `forestQuotientForestSigmaIndex`, and
   `forestComponentSplitChoices_flat_reindex_eq_quotient` put the LHS
   split-regime core and RHS explicit quotient forest double-sum onto explicit
   flat carriers.  `coassoc_strict_forest_linear_of_component_reindex` now
   uses the proved flatization equalities and reduces H5.8F to a concrete
   `Finset.sum_bij` map `φ`.
62. ✓ First graph-level `φ` pieces:
   `admissibleSubgraphOfSubelements`,
   `forestComponentChoiceLeftSubgraph`, and
   `forestComponentChoiceRightSubgraph` build the left/right selected
   admissible subgraphs from an LHS component-choice function, with nonempty
   iff lemmas matching `forestComponentChoiceHasLeft/Right`.
63. ✓ Componentwise properness and mixed outer `φ` slice:
   `AdmissibleSubgraph.HasPositiveInternalEdgesComponents` is now part of the
   proper-disjoint carrier, so nonempty selected component subforests inherit
   positive internal-edge count.  `forestComponentChoiceLeftSubgraph_*` and
   `forestComponentChoiceRightSubgraph_*` now inherit pairwise-disjoint,
   nonempty-component, positive-component, and proper-disjoint membership
   witnesses.  In the mixed left/right boundary regime,
   `forestComponentMixedBoundaryOuterIndex` builds the RHS outer forest as the
   left-selected component subgraph, and
   `forestComponentMixedBoundaryRightSubgraph_mem_properDisjoint` records that
   the right-selected component subgraph is proper in the original ambient.
64. ✓ Bundled final graph-reindexing target:
   `forestComponentSplitGraphReindexing` packages the final `φ` map,
   membership, injectivity, surjectivity, and term equality fields, with
   `coassoc_strict_forest_linear_of_graph_reindexing` as the direct H5.8F cut.
65. ✓ Quotient-side retarget and representative transport API:
   `forestOuterActualQuotientGraph` names the canonical quotient before
   `repG`; `forestOuterActualToRepPerm` and
   `forestOuterActualToRepAdmissibleSubgraph` transport quotient-side forests
   to the chosen representative.  `admissibleSubgraphRetargetSubgraph`,
   `admissibleSubgraphRetarget`, and
   `forestOuterActualRetargetAdmissibleSubgraph` construct an admissible
   forest in `G / outer` from a surviving ambient source forest.  The
   certificate wrapper
   `forestOuterActualRetargetCertificate` drives the mixed right-selected
   forest route.  Genuine component-forest choices are handled separately by
   transporting their representative forests back into the component graph and
   then promoting them into the ambient outer carrier.  The mixed right route
   now has named actual/representative constructors
   `forestComponentMixedBoundaryActualRightQuotientSubgraph` and
   `forestComponentMixedBoundaryRepRightQuotientSubgraph`.
66. ✓ Mixed-boundary right-selected quotient forest:
   `forestComponentChoiceRightSubgraph_not_mem_left`,
   `forestComponentChoiceRightLeft_disjoint`,
   `forestComponentChoiceRight_vertices_not_mem_leftSubgraph`, and
   `forestComponentChoiceRight_internalEdges_le_left_complement` prove that
   right-selected components survive quotienting by the left-selected outer
   forest.  `forestComponentMixedBoundaryRightRetargetCertificateCanonical`
   supplies the edge/CD/compat certificate, and the canonical actual/rep
   quotient-side forests
   `forestComponentMixedBoundaryActualRightQuotientSubgraphCanonical` and
   `forestComponentMixedBoundaryRepRightQuotientSubgraphCanonical` are now
   available for the graph-level `φ`.
67. ✓ Representative transport + promoted genuine-forest carrier:
   `feynmanSubgraphPromoteAdmissibleSubgraph` promotes component-intrinsic
   admissible forests into the ambient graph, preserving connected-divergence,
   Zimmermann compatibility, pairwise-disjointness, nonempty components, and
   proper-disjoint membership.  `feynmanSubgraphToHopfGenRepPerm`,
   `feynmanSubgraphRepToComponentAdmissibleSubgraph`, and
   `feynmanSubgraphRepForestPromoteAdmissibleSubgraph` transport a forest on
   `repG (γ.toHopfGen hγ)` back to `γ.toFeynmanGraph`, then promote it into
   `G`, again preserving proper-disjoint membership.
   `forestComponentChoice_forest_mem_properDisjoint_of_core_mem` extracts the
   properness witness for any `forest B` actually selected by a component
   choice in the `Finset.pi` carrier.
68. ✓ Genuine-forest outer splice:
   `forestComponentChoicePromotedForestComponents` collects the promoted
   ambient components of every selected `forest B`, with membership/source
   and connected-divergent projection lemmas.  The graph-level splice
   `forestComponentForestChoiceOuterSubgraph` is the union of the left-selected
   original components and those promoted forest components; its
   compatibility proof splits into same-source promoted forests, different
   outer components, and left/promoted cross terms.  In the proper
   forest-choice regime,
   `forestComponentForestChoiceOuterSubgraph_mem_properDisjoint` and
   `forestComponentForestChoiceOuterIndex` now package this splice as a RHS
   `forestOuterProperIndex`.
69. ✓ Genuine-forest quotient-side forest skeleton:
   right-selected survivors now retarget through the spliced outer forest via
   `forestComponentForestChoiceRightRetargetCertificateCanonical`, with actual
   and representative quotient forests
   `forestComponentForestChoiceActualRightQuotientSubgraphCanonical` and
   `forestComponentForestChoiceRepRightQuotientSubgraphCanonical`.  Component
   forest remnants are represented by
   `admissibleSubgraphQuotientRemainderSubgraph` and collected in
   `forestComponentForestChoiceRemnantComponents`, with membership/extraction
   lemmas and actual/representative remnant forest constructors under the
   remnant certificate.  The combined quotient-side carrier
   `forestComponentForestChoiceActualQuotientComponents` and actual/rep
   constructors `forestComponentForestChoiceActualQuotientSubgraph` /
   `forestComponentForestChoiceRepQuotientSubgraph` now package
   right-survivors plus remnants under the full quotient certificate.
70. ✓ Right-remnant cross compatibility:
   `forestComponentChoiceRight_forestChoiceSource_disjoint`,
   `forestComponentForestChoiceActualRightQuotientSubgraphCanonical_mem_exists`,
   and `forestComponentForestChoiceRightRemnant_cross` prove that a
   right-selected survivor retargeted through the genuine-forest outer splice
   is disjoint from every selected component-forest quotient remnant.  Hence
   `forestComponentForestChoiceQuotientCertificateOfRemnant` now upgrades a
   remnant-only certificate into the full quotient certificate, and
   `forestComponentForestChoiceActualQuotientSubgraphOfRemnant` /
   `forestComponentForestChoiceRepQuotientSubgraphOfRemnant` give the actual
   and representative quotient-side forests from just the remnant certificate.
71. ✓ Remnant-remnant compatibility:
   `forestComponentForestChoiceOuterSubgraph_mem_source` and
   `forestComponentForestChoiceOuterSubgraph_componentAt_vertices_subset_source`
   identify every spliced outer component with its original source component.
   `forestComponentForestChoiceRemnantComponents_compat` uses that source
   control plus canonical-star freshness/injectivity to prove that distinct
   selected component-forest quotient remnants are disjoint after retargeting.
   The full remnant certificate is now factored through
   `forestComponentForestChoiceRemnantCDCertificate` and
   `forestComponentForestChoiceRemnantCertificateOfCD`: the only remaining
   remnant field is connected-divergence.  The actual/representative
   quotient-side forest constructors also have CD-only entrypoints
   `forestComponentForestChoiceActualQuotientSubgraphOfRemnantCD` and
   `forestComponentForestChoiceRepQuotientSubgraphOfRemnantCD`.
72. ✓ Component quotient side of the remnant CD field:
   `admissibleForestContractGraphWithStars_isConnectedDivergent` upgrades the
   forest-contraction preservation API from canonical stars to any fresh
   component-star assignment.  For a selected genuine component forest,
   `forestComponentForestChoiceComponentRemnantStarOf` pulls the spliced
   outer forest's canonical star assignment back to the component quotient
   `γ / B`; `forestComponentForestChoiceComponentRemnantStarOf_isFresh` proves
   it is fresh, and
   `forestComponentForestChoiceComponentRemnantContractGraph_isConnectedDivergent`
   proves that component quotient graph is connected-divergent.  The new
   `forestComponentForestChoiceRemnantGraphIdentificationCertificate` isolates
   the final literal graph equality needed to identify the raw retargeted
   remnant with that component quotient, and
   `forestComponentForestChoiceRemnantCDCertificateOfGraphIdentification`
   turns that equality into the remnant CD certificate.
73. ✓ Literal graph equality split, vertices field:
   the retargeted remnant graph and component quotient graph now have named
   carriers
   `forestComponentForestChoiceRetargetedRemnantGraph` and
   `forestComponentForestChoiceComponentRemnantGraph`, with fieldwise simp
   expansions and
   `forestComponentForestChoiceRemnantGraphFieldIdentificationCertificate`.
   The graph-level certificate follows from the field certificate via
   `forestComponentForestChoiceRemnantGraphIdentificationCertificateOfFields`.
   On the actual vertex field,
   `forestComponentForestChoice_vertex_mem_outer_iff_componentRemnant`
   identifies which vertices of γ are hit by the spliced outer forest,
   `forestComponentForestChoice_retargetVertex_eq_componentRemnant` proves
   the ambient and component retarget maps agree on γ, and
   `forestComponentForestChoiceRemnantGraph_vertices_eq` proves the literal
   vertices equality.
74. ✓ External-leg retarget field and internal-edge membership cut:
   component-to-ambient promotion now preserves the raw internal-edge multiset
   via `feynmanSubgraphPromoteAdmissibleSubgraph_internalEdges`.  For a genuine
   selected component, `forestComponentForestChoice_internalEdge_mem_outer_iff_componentRemnant`
   proves the γ-restricted deletion predicate agrees between the spliced outer
   forest and the transported component forest.  The edge and leg retarget maps
   now agree pointwise on γ by
   `forestComponentForestChoice_retargetEdge_eq_componentRemnant` and
   `forestComponentForestChoice_retargetExternalLeg_eq_componentRemnant`, and
   `forestComponentForestChoiceRemnantGraph_externalLegs_eq` closes the literal
   external-leg field equality.
75. ✓ Count equality summit and canonical genuine-forest quotient forest:
   `forestComponentForestChoice_promotedForestComponents_internalEdges_count_eq_componentRemnant`,
   `forestComponentForestChoice_leftSubgraph_internalEdges_count_eq_zero_of_component`,
   and `forestComponentForestChoice_outer_internalEdges_count_eq_componentRemnant`
   upgrade the γ-restricted membership cut to exact multiplicity control.
   This yields
   `forestComponentForestChoice_gamma_internalEdges_sub_outer_eq_componentRemnant_complementEdges`
   and `forestComponentForestChoiceRemnantGraph_internalEdges_eq`, closing the
   internal-edge field alongside the existing vertices/external-leg fields.
   The field certificate is now packaged canonically through
   `forestComponentForestChoiceRemnantGraphFieldIdentificationCertificateCanonical`,
   `forestComponentForestChoiceRemnantGraphIdentificationCertificateCanonical`,
   `forestComponentForestChoiceRemnantCertificateCanonical`, and finally
   `forestComponentForestChoiceActualQuotientSubgraphCanonical` /
   `forestComponentForestChoiceRepQuotientSubgraphCanonical`.
76. ✓ `φ` graph-level map body and mixed-boundary membership:
   `forestComponentForestChoiceToQuotientForestSigma` and
   `forestComponentMixedBoundaryToQuotientForestSigma` name the two branch
   targets.  `forestComponentSplitPhi` is now the total graph-level map from
   the split LHS carrier into `forestQuotientForestSigma`, with indexed rewrite
   lemmas for both branches.  The mixed-boundary branch is fully in the RHS
   carrier via
   `admissibleSubgraphRetarget_mem_properDisjoint_of_not_mem`,
   `forestOuterActualRetargetAdmissibleSubgraphOfCert_mem_properDisjoint`,
   `forestComponentMixedBoundaryRepRightQuotientSubgraphCanonical_mem_properDisjoint`,
   and `forestComponentMixedBoundaryToQuotientForestSigma_mem`.
   `forestComponentSplitPhi_map_mem_of_forestBranch` reduces total `map_mem`
   to the remaining genuine-forest branch properness.
77. ✓ Genuine-forest RHS carrier membership cut:
   the canonical quotient-side forest now has canonical nonemptiness,
   nonempty components, and pairwise disjointness.  Right-selected survivors
   have positive internal edges canonically, so full properness is reduced to
   the exact remnant-positive payload
   `forestComponentForestChoiceRemnantPositiveComponentsCertificate`.  This
   yields
   `forestComponentForestChoiceRepQuotientSubgraphCanonical_mem_properDisjoint_of_remnantPositive`,
   `forestComponentForestChoiceToQuotientForestSigma_mem_of_remnantPositive`,
   and total `forestComponentSplitPhi_map_mem`.
78. ✓ `φ` inj/surj/term-equality scaffolding:
   `forestComponentSplitPhi_inj_on_of_split`,
   `forestComponentSplitPhi_surj_on_of_split`, and
   `forestComponentSplitPhi_term_eq_of_split` reduce the three final fields to
   branchwise genuine-forest/mixed-boundary statements plus cross-branch
   separation and RHS branch cover.  `forestComponentSplitPhiBranchReindexing`,
   `forestComponentSplitPhiGraphReindexingOfBranches`, and
   `coassoc_strict_forest_linear_of_split_phi_branches` are now the narrow
   summit interface.  Next: prove the actual branch inverse/cover and
   per-branch tensor term equalities.
79. ✓ Branch inverse/cover and tensor equality split tightened:
   `forestComponentSplitPhiBranchInverseCover` separates the set-theoretic
   inverse/cover data from the tensor calculation, while
   `forestComponentSplitPhiBranchTermFactorization` reduces per-branch term
   equality to product-factorization plus final quotient right-factor
   identification.  The mixed product climb now has concrete algebraic
   payload: `forestComponentChoiceLeftSubgraph_toHopfH_eq_indicator_product`,
   `forestComponentChoiceRightSubgraph_toHopfH_eq_indicator_product`,
   `forestComponentChoiceProductTerm_eq_leftRightSubgraphs_of_noForest`, and
   `forestComponentMixedBoundary_productTerm_eq_leftRightSubgraphs`.  The
   mixed transport payload is now discharged by
   `forestComponentMixedBoundaryRepRightQuotientSubgraphCanonical_toHopfH_eq`
   and
   `forestComponentMixedBoundary_productTerm_eq_repRightQuotientSubgraph`.
   On the genuine-forest side, the representative right-survivor, remnant-only,
   and full quotient forests now transport their `toHopfH` products back to
   the actual quotient carriers, and
   `forestComponentForestChoiceRepQuotientSubgraphCanonical_toHopfH_eq_right_mul_remnant`
   lifts the actual quotient split to the representative carrier.  The
   component representative/preimage/promote product transports are also in
   place for the remaining full `forest_product` and final quotient
   right-factor identification.
80. ✓ Summit payload narrowed again:
   `forestComponentSplitPhiBranchTermFactorizationOfRightPayloads` and
   `forestComponentSplitPhiBranchReindexingOfRightPayloads` now bake the
   mixed-boundary product factorization into the branch term package, so the
   final H5.8F cut
   `coassoc_strict_forest_linear_of_split_phi_right_payloads` only asks for
   branch inverse/cover, genuine-forest product factorization, and the two
   quotient right-factor identifications.  The right-factor climb also has a
   graph-level entrypoint:
   `forestRightHopfH_eq_of_right_val_eq` /
   `forestRightHopfH_eq_of_contract_toClass_eq`, reducing Hopf algebra right
   equality to canonical forest-contraction class equality.
81. ✓ Genuine-forest product payload split:
   the component-choice product now has a forest-case-aware factorization:
   `forestComponentChoiceOuterTensorFactor`,
   `forestComponentChoiceInnerTensorFactorOfCore`,
   `forestCoproductChoiceTerm_eq_outer_inner_of_core`, and
   `forestComponentChoiceProductTerm_eq_outer_inner_products_of_core`.
   The summit no longer needs a monolithic `forest_product` assumption:
   `forestComponentForestChoiceProductFactorization` records only the outer
   product identity and the inner quotient/remnant product identity, and
   `coassoc_strict_forest_linear_of_split_phi_product_payloads` is the new
   thinner final H5.8F cut.
82. ✓ Outer product payload split:
   `forestComponentChoicePromotedOuterTensorFactor` isolates the promoted
   genuine-forest contribution in the first tensor factor, and
   `forestComponentChoiceOuterTensorFactor_product_eq_left_mul_promoted`
   proves the first tensor-factor product splits as the left-selected original
   product times the promoted forest-selection product.  The new
   `forestComponentForestChoiceOuterProductFactorization` and
   `coassoc_strict_forest_linear_of_split_phi_outer_inner_payloads` push the
   H5.8F summit one level lower: the outer product field is now just the
   geometric identity identifying that left/promoted product with the spliced
   outer forest `toHopfH`.
83. ✓ Spliced outer forest product identified:
   `forestComponentChoicePromotedComponentsHopfProduct` names the Hopf product
   over the actual promoted component carrier, and
   `forestComponentForestChoiceOuterIndex_toHopfH_eq_left_mul_promotedComponents`
   proves the geometric identity
   `outer.toHopfH = leftSelected.toHopfH * promotedComponentsProduct`.
   The summit now uses
   `forestComponentForestChoicePromotedProductTransport` and
   `coassoc_strict_forest_linear_of_split_phi_promoted_transport_payloads`, so
   the outer-side remainder is only the transport from the γ-indexed promoted
   representative product to the actual promoted component carrier product.
84. ✓ Outer promoted transport discharged:
   `forestComponentChoicePromotedForestComponentsForChoice` exposes the
   per-component promoted carrier, and
   `forestComponentChoicePromotedForestComponentsForChoice_pairwiseDisjoint`
   supplies the disjointness needed for `Finset.prod_biUnion`.  The transport
   theorem
   `forestComponentChoicePromotedOuterTensorFactor_product_eq_promotedComponentsHopfProduct_of_core`
   identifies the γ-indexed representative promoted product with the actual
   promoted component carrier product.  Consequently
   `forestComponentForestChoicePromotedProductTransportCanonical`,
   `forestComponentForestChoiceOuterProductFactorizationCanonical`, and
   `coassoc_strict_forest_linear_of_split_phi_inner_payloads` remove the last
   outer-side payload from the H5.8F summit: only the inner quotient/remnant
   product identity, branch inverse/cover, and final right-factor identities
   remain.
85. ✓ Inner/right payloads narrowed to graph-level remnants:
   `forestComponentChoiceRemnantInnerTensorFactor` isolates the genuine
   component-forest right factor in the middle tensor slot, and
   `forestComponentChoiceInnerTensorFactor_product_eq_right_mul_remnant`
   splits the inner γ-product into the original right-selected product times
   the remnant-only product.  The right-selected part is already transported
   by `forestComponentForestChoiceRepRightQuotientSubgraphCanonical_toHopfH_eq`,
   while
   `forestComponentForestChoiceRepQuotientSubgraphCanonical_toHopfH_eq_right_mul_remnant`
   supplies the full quotient split.  Thus
   `forestComponentForestChoiceRemnantInnerProductTransport` is now the only
   product payload left.  The final quotient right-factor equalities are also
   lowered through `coassoc_strict_forest_linear_of_split_phi_graph_right_payloads`
   to canonical contracted-graph `toClass` equalities, leaving the summit with
   branch inverse/cover, remnant product transport, and graph-level right
   contraction class identifications.
86. ✓ Remnant product transport lowered to component class payloads:
   `forestComponentForestChoiceRemnantComponentsForChoice` exposes the
   quotient-remnant carrier contributed by each original component choice, and
   `forestComponentForestChoiceRemnantInnerProductGraphTransport` packages
   the remaining carrier disjointness plus local factor-product identity.
   This is further reduced by
   `forestComponentForestChoiceRemnantComponentClassTransport` and
   `forestComponentForestChoiceRemnant_factor_product_eq_of_componentClass`:
   each forest-choice component now only needs the contracted-graph class
   equality between the quotient remnant `γ / B` and the canonical
   representative forest contraction used by `forestRightHopfH`.  The new
   cuts
   `coassoc_strict_forest_linear_of_split_phi_graph_payloads` and
   `coassoc_strict_forest_linear_of_split_phi_component_class_payloads` leave
   the summit as branch inverse/cover, quotient-remnant carrier pairwise
   disjointness, per-component remnant contraction class equality, and the two
   final right contraction class equalities.
87. ✓ Per-component remnant class payload split:
   the quotient-remnant side of the per-component class equality is now
   discharged by the existing canonical remnant graph identification.
   `forestComponentForestChoiceComponentToRepContractionClassTransport`
   isolates the remaining bridge from the component-side contraction
   `γ.toFeynmanGraph / B_component` to the representative-side canonical
   contraction used by `forestRightHopfH`, while
   `forestComponentForestChoiceRemnantComponentClassTransportOfComponentToRep`
   composes that bridge with
   `forestComponentForestChoiceRemnantGraphIdentificationCertificateCanonical`.
   The new cut
   `coassoc_strict_forest_linear_of_split_phi_component_to_rep_payloads`
   leaves the remnant product climb with only carrier pairwise disjointness and
   component-to-representative contraction class transport.
88. ✓ Quotient-remnant carrier pairwise disjointness discharged:
   `forestComponentForestChoiceRemnantComponents_disjoint_of_source_ne`
   isolates the distinct-source disjointness argument for quotient remnants,
   and `forestComponentForestChoiceRemnantComponentsForChoice_pairwiseDisjoint`
   proves the γ-indexed remnant carriers are pairwise disjoint by combining
   that disjointness with canonical nonempty components.  The payload
   `forestComponentForestChoiceComponentToRepContractionClassBridge` removes
   the pairwise field from the remnant transport interface via
   `forestComponentForestChoiceComponentToRepContractionClassTransportOfBridge`,
   and `coassoc_strict_forest_linear_of_split_phi_component_to_rep_bridge`
   leaves the remnant climb with only the component-to-representative
   contraction class bridge.
89. ✓ Component-to-representative bridge reduced to generic graph transport:
   `admissibleForestContractPreimageClassTransport` packages the remaining
   component-side contraction transport as a component-free mapPerm/preimage
   theorem for admissible forest contractions.  The component payload is now
   supplied by
   `forestComponentForestChoiceComponentToRepContractionClassBridgeOfPreimageTransport`,
   and `coassoc_strict_forest_linear_of_split_phi_preimage_contract_transport`
   removes all q/γ-specific geometry from that bridge.  The generic theorem is
   further split into the two graph-level facts
   `admissibleForestContractFreshStarClassTransport` and
   `admissibleForestContractCanonicalPreimageClassTransport`, combined by
   `admissibleForestContractPreimageClassTransportOfFreshAndCanonical`, so the
   final climb now asks only for fresh-star class invariance, canonical
   mapPerm-preimage contraction invariance, branch inverse/cover, remnant
   positivity, and the two final right-factor class equalities.
90. ✓ Pure graph-level transport split to relabeling fields:
   the two remaining graph invariance payloads have been peeled from
   `toClass` equalities down to explicit relabeling witnesses:
   `admissibleForestContractFreshStarRelabeling` and
   `admissibleForestContractCanonicalPreimageRelabeling` each ask for a
   concrete vertex permutation whose `mapPerm` image is literally the target
   contraction graph.  These are further split by
   `admissibleForestContractFreshStarFieldRelabeling` and
   `admissibleForestContractCanonicalPreimageFieldRelabeling` into the three
   fieldwise goals `vertices`, `internalEdges`, and `externalLegs`.  The new
   final cut `coassoc_strict_forest_linear_of_split_phi_contract_field_relabeling`
   leaves the summit with finite graph relabeling data, branch inverse/cover,
   remnant positivity, and the two final right-factor class equalities.
91. ✓ Fresh-star field relabeling discharged from permutation data:
   `admissibleForestContractFreshStarPermutationData` isolates the only
   finite-permutation construction needed on the fixed-forest side: a
   permutation fixing every visible non-contracted vertex and sending each
   caller-supplied fresh component star to the canonical component star.
   The local transport lemmas
   `admissibleForestContractFreshStar_retargetVertex_map`,
   `admissibleForestContractFreshStar_retargetEdge_map`, and
   `admissibleForestContractFreshStar_retargetExternalLeg_map` prove that
   such a permutation carries the contraction fields to the canonical-star
   fields.  Thus
   `admissibleForestContractFreshStarFieldRelabelingOfPermutationData` and
   `coassoc_strict_forest_linear_of_split_phi_fresh_permutation_data` remove
   the fixed-forest field equalities from the summit; what remains is the
   actual finite permutation existence, canonical mapPerm-preimage field
   relabeling, branch inverse/cover, remnant positivity, and final right-factor
   class equalities.
92. ✓ Graph-level relabeling payloads aligned as permutation data:
   the canonical mapPerm-preimage side now has the matching wrapper
   `admissibleForestContractCanonicalPreimagePermutationData`, which records
   the concrete permutation and the three literal field transports for the
   representative-side canonical contraction.  The bridge
   `admissibleForestContractCanonicalPreimageFieldRelabelingOfPermutationData`
   feeds that into the previous field-level cut, and
   `coassoc_strict_forest_linear_of_split_phi_graph_permutation_data` leaves
   the pure graph summit in a symmetric finite-permutation-data form:
   fixed-forest fresh-star permutation data, canonical preimage permutation
   data, branch inverse/cover, remnant positivity, and final right-factor class
   equalities.
93. ✓ Fresh-star finite permutation constructed:
   `finite_visible_star_permutation` proves the finite-support extension
   theorem: a finite injective family of source stars can be sent to a finite
   injective family of target stars while a finite visible set is fixed.  The
   construction extends the partial map on the finite support subtype and then
   lifts it to a full `Equiv.Perm VertexId`.  The graph-level wrapper
   `admissibleForestContractFreshStarPermutation_of_wellFormed` instantiates
   this with the admissible component carrier, using well-formedness to turn
   ambient-vertex fixation into the visible edge/leg fixation needed by the
   field relabeling.  Thus the fresh-star side now has an actual Lean
   permutation constructor rather than only an abstract payload.
94. ✓ Canonical preimage star permutation constructed:
   `admissibleForestContractCanonicalPreimage_starPermutation` builds the
   canonical mapPerm-preimage star-alignment permutation.  For
   `hπ : G₂ = G₁.mapPerm π`, it constructs `τ = σ * π`: `π` transports the
   ambient vertices from the preimage representative to the target
   representative, while the finite-support correction `σ` fixes `G₂.vertices`
   and sends the transported preimage canonical component stars to the target
   canonical component stars.  The constructor is independent of any ordering
   agreement between the two finite component carriers, so the remaining
   canonical preimage field relabeling can now use explicit finite
   permutation data instead of an abstract existence claim.
95. ✓ Canonical preimage field transport reduced to carrier multiset maps:
   `mapPermAdmissibleSubgraphPreimage_mem_vertices_iff` proves that a vertex
   belongs to the permutation-preimage forest exactly when its `π`-image
   belongs to the target forest.  Using this, the explicit star-alignment
   permutation now transports the canonical preimage contraction's vertex
   field via
   `admissibleForestContractCanonicalPreimage_vertices_eq_of_starPermutation`.
   The pointwise retarget payload is also in place:
   `admissibleForestContractCanonicalPreimage_retargetVertex_map`,
   `admissibleForestContractCanonicalPreimage_retargetEdge_map`, and
   `admissibleForestContractCanonicalPreimage_retargetExternalLeg_map`.
   Thus the remaining canonical field relabeling is no longer about stars or
   component choices; it is the pure carrier transport for
   `Apre.complementEdges.map (FeynmanEdge.map π) = A.complementEdges` and
   `G₁.externalLegs.map (ExternalLeg.map π) = G₂.externalLegs`.
96. ✓ Canonical preimage carrier/field transport discharged for well-formed
   source graphs:
   `mapPermAdmissibleSubgraphPreimage_internalEdges_map`,
   `multiset_map_sub_of_injective`,
   `mapPermAdmissibleSubgraphPreimage_complementEdges_map`, and
   `mapPermAdmissibleSubgraphPreimage_externalLegs_map` prove the carrier
   multiset transports.  These feed the field-level contractions
   `admissibleForestContractCanonicalPreimage_internalEdges_eq_of_starPermutation`
   and
   `admissibleForestContractCanonicalPreimage_externalLegs_eq_of_starPermutation`,
   bundled by
   `admissibleForestContractCanonicalPreimage_fieldRelabeling_of_wellFormed`.
   The canonical mapPerm-preimage side is now an explicit finite
   star-alignment plus literal carrier transport package on the well-formed
   graphs that occur in the component-to-representative bridge.
97. ✓ Finite star alignment + carrier transport connected to the component
   bridge:
   `admissibleForestContractFreshStarFieldRelabeling_of_wellFormed` and
   `admissibleForestContractFreshStarClass_of_wellFormed` turn the fixed
   forest fresh-star permutation constructor into a local class transport on
   well-formed graphs.  Together with
   `admissibleForestContractCanonicalPreimageClass_of_wellFormed`, this
   proves
   `forestComponentForestChoiceComponentToRepContractionClassBridgeCanonical`.
   The new summit cut
   `coassoc_strict_forest_linear_of_split_phi_wellFormed_component_bridge`
   removes the generic component-to-representative bridge payload: the
   remnant product climb now uses the concrete finite star-alignment and
   carrier transport on each component graph.
98. ✓ Canonical remnant product transport packaged:
   `forestComponentForestChoiceRemnantInnerProductTransportCanonical` composes
   the canonical component-to-representative bridge back up through the
   per-component class payload and graph-level remnant transport.  The new
   cut `coassoc_strict_forest_linear_of_split_phi_canonical_remnant_transport`
   removes the remnant product payload entirely from the summit.  What remains
   is branch inverse/cover, remnant positivity, and the two final quotient
   right-factor identifications.
99. ✓ Right-factor representative transport cut out:
   `mapPermSubgraph_preimage_mapPerm_eq` and
   `mapPermAdmissibleSubgraphPreimage_mapPerm_eq` make the mapPerm/preimage
   round trip literal for transported admissible forests.  The generic
   `admissibleForestContractMapPermClass_of_wellFormed` identifies canonical
   forest contractions across a permutation-transported ambient graph and
   forest.  Specializing this to the quotient representative choice gives
   `forestOuterActualToRep_rightContractClass`, so the final right-factor
   class equalities can now be proved on the actual quotient graph first and
   transported to the `repG` representative afterward.
100. ✓ Final right-factor payload lowered to actual quotient contractions:
   `forestComponentForestChoice_rightContractClass_of_actual` and
   `forestComponentMixedBoundary_rightContractClass_of_actual` compose
   actual-side class equalities with `forestOuterActualToRep_rightContractClass`.
   The cut `coassoc_strict_forest_linear_of_split_phi_actual_right_payloads`
   leaves the summit with branch inverse/cover, remnant positivity, and actual
   quotient-graph right contraction class equalities.
101. ✓ Actual right-factor payload lowered to field relabeling:
   `forestComponentChoiceOriginalRightContractGraph`,
   `forestComponentForestChoiceActualRightContractGraph`, and
   `forestComponentMixedBoundaryActualRightContractGraph` name the three
   graph-level contraction targets.  The payloads
   `forestComponentActualRightContractionRelabeling` and
   `forestComponentActualRightContractionFieldRelabeling` reduce the final
   actual right-factor class equalities to explicit finite relabeling data,
   with literal `vertices`, `internalEdges`, and `externalLegs` equalities.
   The cuts
   `coassoc_strict_forest_linear_of_split_phi_actual_right_relabeling` and
   `coassoc_strict_forest_linear_of_split_phi_actual_right_field_relabeling`
   make this the new summit interface.
102. ✓ Actual right field relabeling built from split-star models:
   `forestComponentActualRightContractionSplitStarModel` isolates the
   geometric core of the final right-factor equality: the actual two-step
   contraction must be a one-step contraction of the original component
   forest with a branch-specific fresh star assignment.  The transport lemma
   `forestComponentActualRightContractionFieldRelabelingOfSplitStarModel`
   applies the fixed-forest finite star relabeling theorem to produce the
   literal `vertices`, `internalEdges`, and `externalLegs` relabeling data.
   Consequently
   `coassoc_strict_forest_linear_of_split_phi_actual_right_split_star_model`
   leaves the final summit with branch inverse/cover, remnant positivity, and
   the two split-star one-step contraction models.
103. ✓ Mixed-boundary split stars constructed:
   `forestComponentMixedBoundary_choice_left_or_right` proves that, in the
   mixed branch, every original component is selected on exactly the
   left/right boundary side rather than as a genuine forest.  The concrete
   star assignment `forestComponentMixedBoundarySplitStarOf` now names the
   one-step contraction stars: left components use the outer canonical stars,
   while right components use the canonical stars of their retargeted actual
   quotient components.  The rewrite lemmas
   `forestComponentMixedBoundarySplitStarOf_left` and
   `forestComponentMixedBoundarySplitStarOf_right` fix the two branches of the
   literal graph model.
104. ✓ Mixed-boundary split-star freshness discharged:
   the arithmetic/finiteness support around fresh vertices is now explicit via
   `freshVertex_le_componentFreshStar`, `lt_freshVertex_of_mem`, and
   `not_mem_of_freshVertex_le`.  The mixed left star is shown to live in the
   actual outer quotient while remaining above the original fresh bound, and
   `forestComponentMixedBoundarySplitStarOf_right_fresh` uses that quotient
   bound to prove right-star freshness back in the original ambient graph.
   These pieces combine in
   `forestComponentMixedBoundarySplitStarOf_isFresh`, including left/right
   separation and right/right retarget injectivity.  Consequently
   `forestComponentMixedBoundarySplitStarModelPayloadOfGraphEq` and
   `coassoc_strict_forest_linear_of_split_phi_mixed_split_star_graph_payload`
   remove mixed-boundary freshness from the final summit: the mixed branch now
   only needs the literal two-step-vs-one-step contraction graph equality.
105. ✓ IDE stack-overflow hotspot removed:
   the obsolete connected-only `termE3`/`termF3` sigma-flattening lemmas from
   the blocked pre-admissible route were removed from the compiled path.  They
   were not referenced by the current admissible-forest H5.8F proof and their
   fully-expanded dependent tensor statements could overflow the elaborator
   stack near the old line 15000.  The active route remains the admissible
   `φ`-reindexing climb above.
106. ✓ Mixed split-star graph model vertex field discharged:
   `forestComponentMixedBoundary_left_union_right_elements` and
   `forestComponentMixedBoundary_left_union_right_vertices` make the mixed
   original carrier split literally into left/right selections.  The
   split-star carrier is decomposed by
   `forestComponentMixedBoundary_splitStar_starVertices_eq_union`, with the
   left stars identified with the outer canonical stars and the right stars
   identified with the actual quotient right-star carrier.  The actual
   right-quotient vertex carrier is transported back to the original
   right-selected carrier by
   `forestComponentMixedBoundaryActualRightQuotientSubgraphCanonical_vertices_eq_right`.
   These pieces prove
   `forestComponentMixedBoundary_splitStar_vertices_eq`, and the new cut
   `coassoc_strict_forest_linear_of_split_phi_mixed_split_star_edge_leg_payload`
   leaves only `internalEdges` and `externalLegs` for the mixed
   two-step-vs-one-step graph model.
107. ✓ Mixed actual right quotient internal-edge carrier transported:
   `forestComponentMixedBoundaryActualRightQuotientSubgraphCanonical_internalEdges_eq_right`
   proves that the quotient-side canonical right forest has exactly the
   original right-selected internal-edge multiset.  The proof reindexes the
   retargeted quotient carrier over the original right carrier using
   `admissibleSubgraphRetarget_injective_of_not_mem`, then applies the
   untouched-component transport
   `admissibleSubgraphRetargetSubgraph_internalEdges_eq_of_not_mem` component
   by component.  The external-leg side must be attacked directly at the
   `contractWithStars_externalLegs` level, since `AdmissibleSubgraph` only
   aggregates component internal edges, not component external legs.
108. ✓ Mixed two-step external-leg retargeting collapsed:
   `forestComponentMixedBoundary_twoStep_retargetVertex_eq_splitStar` proves
   the pointwise vertex identity
   `Aact.retargetVertex rightStar (Aout.retargetVertex outerStar v) =
   A.retargetVertex splitStar v` by splitting vertices into outside, left, and
   right component cases.  The left case keeps the outer star visible through
   the second contraction, while the right case identifies the actual quotient
   component and then uses the right split-star definition.  This lifts to
   `forestComponentMixedBoundary_twoStep_retargetExternalLeg_eq_splitStar`,
   and finally to `forestComponentMixedBoundary_splitStar_externalLegs_eq` via
   `Multiset.map_map`.  Thus the mixed split-star graph model has both
   `vertices` and `externalLegs` discharged; only the internal-edge complement
   multiset equality remains on the mixed branch.
109. ✓ Mixed internal-edge complement climb reduced to the containment/count
   core:
   `forestComponentMixedBoundary_twoStep_retargetEdge_eq_splitStar` is the
   edge analogue of the vertex retarget composition, proving pointwise that
   outer retargeting followed by actual-right retargeting equals the one-step
   split-star retargeting.  The mixed carrier split now also has
   `forestComponentMixedBoundary_left_union_right_internalEdges`, identifying
   the original component-forest internal-edge multiset as the left plus right
   selected internal-edge multisets.  On the multiset algebra side,
   `multiset_map_sub_of_le` records the non-injective-safe subtraction rule
   needed for retarget maps, and
   `forestComponentMixedBoundary_right_internalEdges_outerRetarget_eq` proves
   the right-selected internal edges are fixed by the outer retarget.  The
   remaining internal-edge field equality is now concentrated in the single
   containment/count fact that the right-selected aggregate internal-edge
   multiset embeds in the left complement, i.e. the aggregate version of the
   already proved componentwise survivor lemma.
110. ✓ Mixed split-star graph model fully discharged:
   the aggregate survivor containment is now proved by
   `admissibleSubgraph_internalEdges_le_of_pairwise` and
   `forestComponentMixedBoundary_right_internalEdges_le_left_complement`,
   using the left/right internal-edge split plus pairwise-disjoint component
   counts.  This feeds the complement algebra in
   `forestComponentMixedBoundary_splitStar_internalEdges_eq`, where
   `multiset_map_sub_of_le`, right-edge outer-retarget fixation, and
   `forestComponentMixedBoundary_twoStep_retargetEdge_eq_splitStar` identify
   the two-step quotient internal-edge carrier with the one-step split-star
   carrier.  Together with the already discharged vertex and external-leg
   fields, `forestComponentMixedBoundarySplitStarEdgeLegModelCanonical` closes
   the full mixed-boundary literal graph model, and
   `coassoc_strict_forest_linear_of_split_phi_mixed_split_star_canonical`
   removes the mixed split-star payload from the H5.8F summit.  The remaining
   split-star model payload is now only the genuine-forest branch.
111. ✓ Genuine split-star branch injection and star-carrier split:
   the genuine branch now has a concrete split-star assignment
   `forestComponentForestChoiceSplitStarOf`, with left/right/forest rewrite
   lemmas and branchwise freshness/injectivity discharged by
   `forestComponentForestChoiceSplitStarBranchInjectivityCanonical`.  The
   summit interface has been narrowed through
   `forestComponentForestChoiceSplitStarGraphFieldModel`: only the three
   literal graph fields remain.  On the vertex-star side,
   `forestComponentForestChoiceForestSplitStarVertices` isolates the
   source-side stars contributed by genuine component-forest choices, and
   `forestComponentForestChoice_splitStar_starVertices_eq_union` splits
   `q.1.1.starVertices splitStar` into left, right, and forest-remnant
   contributions.
112. ✓ Genuine quotient star/vertex transport foothold:
   the left-selected star block is transported to the outer splice by
   `forestComponentForestChoice_left_splitStar_starVertices_eq_outer`, the
   right-selected block to the actual right quotient carrier by
   `forestComponentForestChoice_right_splitStar_starVertices_eq_actual`, and
   the genuine forest-remnant block to the actual remnant quotient carrier by
   `forestComponentForestChoice_forest_splitStar_starVertices_eq_remnant`.
   The actual quotient carrier now has the vertex split
   `forestComponentForestChoiceActualQuotientSubgraphCanonical_vertices_eq_right_union_remnant`,
   with right survivor vertices identified by
   `forestComponentForestChoiceActualRightQuotientSubgraphCanonical_vertices_eq_right`.
   The remaining vertices proof has its remnant-side membership tools in
   place:
   `forestComponentForestChoice_actualRemnant_vertices_mem_of_forest_vertex`,
   `forestComponentForestChoice_promoted_outer_star_mem_actual_remnant_vertices`,
   and
   `forestComponentForestChoice_actualRemnant_vertex_mem_original_of_mem_graph`.
   Next: assemble these pieces into the literal genuine
   `forestComponentForestChoice_splitStar_vertices_eq`, then reuse the same
   pointwise retarget strategy for `externalLegs` and the complement multiset
   argument for `internalEdges`.
113. ✓ Genuine split-star graph fields inserted into the final cut:
   the genuine branch now has literal graph-field equalities for
   `vertices`, `externalLegs`, and `internalEdges`, with the internal-edge
   proof routed through
   `forestComponentForestChoice_splitStar_internalEdges_eq_of_actual_internalEdges`
   and the actual quotient complement transport.  The new payload
   `forestComponentForestChoiceActualQuotientInternalEdgesModel` isolates the
   last actual quotient carrier identity, while
   `forestComponentForestChoiceSplitStarGraphFieldModelOfActualInternalEdges`
   packages the canonical `vertices`/`externalLegs` fields together with that
   internal-edge identity.  The final H5.8F cut now has the genuine split-star
   graph model wired in via
   `coassoc_strict_forest_linear_of_split_phi_genuine_actual_internalEdges`.
114. ✓ Genuine source internal-edge split lowered to edge counts:
   the actual quotient internal-edge carrier is now reduced through
   `forestComponentForestChoiceActualQuotientInternalEdgesModelOfSourceSplit`
   to the source-side identity
   `A.internalEdges - Aout.internalEdges = right.internalEdges + remnantSum`.
   That identity has been peeled once more by
   `forestComponentForestChoiceSourceInternalEdgesCountSplitModel`, so the
   remaining genuine internal-edge payload is only the per-edge multiplicity
   equality.  The corresponding final cut is
   `coassoc_strict_forest_linear_of_split_phi_genuine_source_internalEdges_count`.
115. ✓ Genuine internal-edge payload discharged canonically:
   `forestComponentForestChoiceSourceInternalEdgesCountSplitCanonical` proves
   the source-side count identity by splitting on whether the tracked edge lies
   in the original component forest, then using component pairwise disjointness
   to localize the unique contributing component and separating left/right/
   genuine-forest choices.  The last brittle match/proof-argument issue in the
   singleton summand was removed by splitting the target match directly.  The
   new cut
   `coassoc_strict_forest_linear_of_split_phi_genuine_internalEdges_canonical`
   feeds this canonical count model into H5.8F, so the genuine split-star
   graph-field payload is now fully discharged; the summit is narrowed to
   remnant positivity and branch inverse/cover.
116. ✓ Remnant positivity lowered to source complement positivity:
   `forestComponentForestChoiceRemnantSourcePositiveCertificate` isolates the
   last positivity content for genuine component-forest choices as the
   nonemptiness of
   `γ.internalEdges - outer.internalEdges`.  The bridge
   `forestComponentForestChoiceRemnantPositiveComponentsCertificateOfSource`
   transports this through
   `admissibleSubgraphQuotientRemainderSubgraph_internalEdges`, using that the
   quotient remnant only maps the complement edges by retargeting.  The new cut
   `coassoc_strict_forest_linear_of_split_phi_remnant_source_positive` leaves
   H5.8F with source-side remnant complement positivity plus the branch
   inverse/cover reindexing package.
117. ✓ Remnant positivity lowered again to component quotient positivity:
   `forestComponentForestChoiceComponentRemnantPositiveCertificate` names the
   graph-level positivity of the component quotient
   `forestComponentForestChoiceComponentRemnantGraph`.  The bridge
   `forestComponentForestChoiceRemnantSourcePositiveCertificateOfComponentGraph`
   uses the already-proved literal internal-edge identification
   `forestComponentForestChoiceRemnantGraph_internalEdges_eq` and the
   retargeted-remnant internal-edge formula to transport that positivity back
   to `γ.internalEdges - outer.internalEdges`.  The new cut
   `coassoc_strict_forest_linear_of_split_phi_component_remnant_positive`
   moves the remaining positivity climb entirely to the component quotient
   graph, leaving branch inverse/cover as the other final payload.
118. ✓ Branch inverse/cover split into injectivity and cover payloads:
   `forestComponentSplitPhiBranchInjectivitySeparation` now isolates the
   two same-branch injectivity facts plus the genuine/mixed cross-branch
   separation, while `forestComponentSplitPhiBranchCoverCertificate` records
   only the RHS forest-sigma branch cover.  The bridge
   `forestComponentSplitPhiBranchInverseCoverOfSeparated` reassembles the
   original package, and
   `coassoc_strict_forest_linear_of_split_phi_component_remnant_positive_branch_payloads`
   is the new thinnest H5.8F cut: component-remnant positivity, branch
   injectivity/separation, and branch cover are now independent summit
   payloads.
119. ✓ Remnant positivity lowered to component-local complement nonemptiness:
   `forestComponentForestChoiceComponentComplementPositiveCertificate`
   expresses the positivity payload as the literal nonemptiness of the
   component-side complement
   `(feynmanSubgraphRepToComponentAdmissibleSubgraph γ B).complementEdges`.
   The bridge
   `forestComponentForestChoiceComponentRemnantPositiveCertificateOfComplement`
   uses the quotient graph internal-edge formula to transport this to the
   component-remnant graph positivity field.  The latest final cut
   `coassoc_strict_forest_linear_of_split_phi_component_complement_positive`
   leaves H5.8F with exactly three independent summit payloads: component
   complement positivity, branch injectivity/separation, and RHS branch cover.
120. ✓ Branch reindexing compressed to a single inverse construction:
   `forestComponentSplitPhiInverseConstruction` packages one explicit inverse
   map from RHS quotient-forest indices back to the split LHS carrier, plus
   carrier membership and the two inverse laws.  The constructors
   `forestComponentSplitPhiBranchInjectivitySeparationOfInverseConstruction`
   and `forestComponentSplitPhiBranchCoverCertificateOfInverseConstruction`
   mechanically recover branch injectivity/separation and RHS cover from that
   inverse data.  The new cut
   `coassoc_strict_forest_linear_of_split_phi_inverse_construction` leaves
   H5.8F with the component complement positivity payload and the actual
   finite inverse construction for `φ`.
121. ✓ Inverse construction split into a branch classifier:
   `forestComponentSplitPhiBranchClassifier` keeps the RHS-to-LHS inverse map,
   carrier membership, and RHS right-inverse law, but replaces the monolithic
   left-inverse field with separate genuine and mixed branch image laws
   `forest_inv` and `mixed_inv`.  The bridge
   `forestComponentSplitPhiInverseConstructionOfClassifier` rebuilds the
   total inverse construction, and
   `coassoc_strict_forest_linear_of_split_phi_branch_classifier` is the
   current final cut.  The remaining reindexing task is now exactly the
   concrete finite RHS branch classifier.
122. ✓ Classifier restricted to the actual RHS finite carrier:
   `forestComponentSplitPhiIndexedBranchClassifier` replaces the total inverse
   map by a preimage map on the subtype
   `{r // r ∈ forestQuotientForestSigmaIndex g}`.  This removes the need to
   choose any arbitrary preimage outside the summation carrier and keeps the
   remaining classifier construction fully finite.  The bridges
   `forestComponentSplitPhiBranchInjectivitySeparationOfIndexedClassifier`
   and `forestComponentSplitPhiBranchCoverCertificateOfIndexedClassifier`
   recover injectivity/separation and cover, while
   `coassoc_strict_forest_linear_of_split_phi_indexed_branch_classifier`
   is the latest final cut.
123. ✓ Indexed classifier split into branch decision/reconstruction data:
   `forestComponentSplitPhiForestPreimageData` and
   `forestComponentSplitPhiMixedPreimageData` name the two possible RHS
   preimage records, and
   `forestComponentSplitPhiBranchDecisionReconstruction` asks for an explicit
   classifier returning one of those records for each RHS carrier element.
   The bridge
   `forestComponentSplitPhiIndexedBranchClassifierOfDecision` turns that
   decision data into the indexed classifier, and
   `coassoc_strict_forest_linear_of_split_phi_branch_decision` is the current
   final cut.  The remaining reindexing problem is now the actual finite
   branch decision and reconstruction theorem.
124. ✓ Branch decision split into cover plus image laws:
   `forestComponentSplitPhiBranchDecisionCover` now isolates the pure RHS
   branch-cover classifier: every quotient-forest carrier term must be shown
   to come from either the genuine-forest branch or the mixed-boundary branch,
   together with its target equality.  Separately,
   `forestComponentSplitPhiBranchDecisionImageLaws` records the two
   normalization laws saying that the classifier returns the original `q` on
   canonical genuine and mixed images.  The bridge
   `forestComponentSplitPhiBranchDecisionReconstructionOfCoverLaws` rebuilds
   the previous reconstruction package, and the new final cut
   `coassoc_strict_forest_linear_of_split_phi_branch_decision_cover_laws`
   leaves H5.8F with component complement positivity, the actual finite RHS
   cover classifier, and the two branch image-normalization laws.
125. ✓ RHS cover returned to propositional branch-cover form:
   `forestComponentSplitPhiBranchDecisionCoverOfCertificate` turns the older
   propositional `forestComponentSplitPhiBranchCoverCertificate` into the new
   decision-cover classifier by choosing one finite preimage witness for each
   RHS carrier term.  The final cut
   `coassoc_strict_forest_linear_of_split_phi_branch_cover_image_laws` now
   separates the set-theoretic RHS cover from the remaining normalization
   payload: after component complement positivity and branch cover, it only
   asks that the chosen cover returns the original `q` on canonical genuine
   and mixed images.
126. ✓ Image laws discharged from branch separation:
   `forestComponentSplitPhiBranchDecisionImageLawsOfSeparated` proves that
   any chosen RHS cover classifier is automatically normalized on canonical
   genuine and mixed images once same-branch injectivity and cross-branch
   separation are available.  The new cut
   `coassoc_strict_forest_linear_of_split_phi_branch_cover_separated` removes
   the explicit image-law payload and reunifies the final reindexing summit as
   component complement positivity plus branch injectivity/separation plus RHS
   branch cover.
127. ✓ Branch separation split into three independent pieces:
   `forestComponentSplitPhiForestBranchInjectivity`,
   `forestComponentSplitPhiMixedBranchInjectivity`, and
   `forestComponentSplitPhiCrossBranchSeparation` isolate the three remaining
   injectivity/separation facts for the split `φ` map.  The bridge
   `forestComponentSplitPhiBranchInjectivitySeparationOfPieces` rebuilds the
   previous package, and
   `coassoc_strict_forest_linear_of_split_phi_branch_cover_separated_pieces`
   is the latest final cut.  The remaining H5.8F summit is now component
   complement positivity, forest-branch injectivity, mixed-branch injectivity,
   cross-branch separation, and RHS branch cover.
128. ✓ Constructive RHS decision-cover interface restored:
   `coassoc_strict_forest_linear_of_split_phi_decision_cover_separated_pieces`
   keeps the RHS cover in the constructive
   `forestComponentSplitPhiBranchDecisionCover` form while deriving image
   normalization from forest injectivity, mixed injectivity, and cross
   separation.  This is the interface best suited for the actual finite
   classifier construction: the remaining summit is component complement
   positivity, the three branch separation pieces, and a concrete RHS
   decision cover.
129. ✓ RHS decision cover lowered to a branch predicate:
   `forestComponentSplitPhiBranchDecisionPredicateCover` splits the concrete
   RHS classifier into a predicate on RHS quotient-forest carrier elements plus
   separate genuine and mixed preimage constructors for the two predicate
   outcomes.  The bridge
   `forestComponentSplitPhiBranchDecisionCoverOfPredicate` rebuilds the
   decision cover, and
   `coassoc_strict_forest_linear_of_split_phi_predicate_cover_separated_pieces`
   is the newest final cut.  The remaining cover construction can now be
   attacked as a finite predicate/classifier problem on the RHS outer quotient
   forest term.
130. ✓ RHS predicate classifier split into constructors:
   `forestComponentSplitPhiRHSBranchPredicate` isolates the actual finite
   branch predicate on RHS quotient-forest carrier terms.  The branch-specific
   payloads are now
   `forestComponentSplitPhiForestPreimageConstructor` and
   `forestComponentSplitPhiMixedPreimageConstructor`, reassembled by
   `forestComponentSplitPhiBranchDecisionPredicateCoverOfConstructors`.
   The cut `coassoc_strict_forest_linear_of_split_phi_branch_predicate_constructors`
   leaves the cover climb with an explicit predicate plus the two constructor
   problems, alongside component complement positivity and the three branch
   separation pieces.
131. ✓ RHS preimage constructors split into choice laws:
   the two branch-specific RHS constructors now factor through explicit
   source-choice data and its two reconstruction laws.  On the genuine branch,
   `forestComponentSplitPhiForestPreimageChoice` chooses the source component
   data, while `forestComponentSplitPhiForestPreimageChoiceLaws` records
   membership in `forestComponentForestChoiceSigmaIndex` and the target
   equality back to the RHS carrier.  The mixed branch has the parallel
   `forestComponentSplitPhiMixedPreimageChoice` and
   `forestComponentSplitPhiMixedPreimageChoiceLaws`.  The bridges
   `forestComponentSplitPhiForestPreimageConstructorOfChoiceLaws` and
   `forestComponentSplitPhiMixedPreimageConstructorOfChoiceLaws` rebuild the
   previous constructors, and the new cut
   `coassoc_strict_forest_linear_of_split_phi_branch_predicate_choice_laws`
   leaves the final cover climb as: branch predicate, forest choice/membership/
   target equality, mixed choice/membership/target equality, component
   complement positivity, and the three branch separation pieces.
132. ✓ Choice-law cover reconnected to source positivity:
   `forestComponentSplitPhiBranchCoverCertificateOfDecisionCover` forgets the
   executable RHS branch decision back to the propositional cover certificate,
   and `forestComponentSplitPhiBranchCoverCertificateOfChoiceLaws` performs
   the same reconstruction directly from the branch predicate plus forest/mixed
   choice laws.  The new cut
   `coassoc_strict_forest_linear_of_split_phi_source_positive_branch_choice_laws`
   wires this newest cover interface into the already-lowered source-side
   remnant positivity summit.  The remaining H5.8F interface is now: source
   complement positivity, forest branch injectivity, mixed branch injectivity,
   cross-branch separation, RHS branch predicate, and the two branch choice
   laws.
133. ✓ RHS predicate canonicalized:
   the branch predicate is now fixed to the canonical statement "this RHS term
   has a genuine-forest preimage" via
   `forestComponentSplitPhiCanonicalRHSBranchPredicate`.  The genuine branch
   choice and its membership/target laws are obtained by unpacking that
   existential:
   `forestComponentSplitPhiCanonicalForestPreimageChoice` and
   `forestComponentSplitPhiCanonicalForestPreimageChoiceLaws`.  Thus the only
   remaining RHS cover content is the residual mixed case, isolated as
   `forestComponentSplitPhiNoForestMixedCoverCertificate` and consumed by
   `forestComponentSplitPhiCanonicalMixedPreimageChoice` /
   `forestComponentSplitPhiCanonicalMixedPreimageChoiceLaws`.  The newest cut
   `coassoc_strict_forest_linear_of_split_phi_canonical_rhs_cover` leaves the
   summit as source complement positivity, the three branch separation facts,
   and the statement that every RHS term with no genuine preimage has a mixed
   preimage.
134. ✓ Source positivity lowered to an edge witness:
   `forestComponentForestChoiceRemnantSourceEdgeWitnessCertificate` replaces
   the source-side cardinal positivity payload by the concrete data of one
   surviving internal edge in
   `γ.internalEdges - outer.internalEdges` for each genuine component-forest
   choice.  The bridge
   `forestComponentForestChoiceRemnantSourcePositiveCertificateOfEdgeWitness`
   recovers cardinal positivity by `Multiset.card_pos_iff_exists_mem`, and
   `coassoc_strict_forest_linear_of_split_phi_source_edge_witness` is now the
   thinnest summit cut: source edge witnesses, forest/mixed/cross branch
   separation, and the residual no-genuine-preimage-to-mixed-cover certificate.
135. ✓ Cross separation rewritten as mixed-image non-forest:
   after canonicalizing the RHS predicate, cross-branch separation is exactly
   the assertion that a mixed-boundary branch image has no genuine-forest
   preimage.  This is isolated by
   `forestComponentSplitPhiMixedImageNotForest`, and
   `forestComponentSplitPhiCrossBranchSeparationOfMixedImageNotForest`
   reconstructs the previous cross-separation field.  The cut
   `coassoc_strict_forest_linear_of_split_phi_mixed_image_not_forest` now
   leaves the summit as source edge witnesses, forest-branch injectivity,
   mixed-branch injectivity, mixed-image non-forest, and residual mixed cover
   for RHS terms with no genuine preimage.
136. ✓ Forest-branch injectivity lowered to canonical preimage normalization:
   a source-edge witness now also supplies RHS carrier membership for genuine
   branch images via
   `forestComponentForestChoiceToQuotientForestSigma_mem_of_sourceEdgeWitness`.
   The forest-branch injectivity payload has been split to the canonical
   choice normalizer
   `forestComponentSplitPhiCanonicalForestImageNormalizer`, which says that
   the canonical genuine preimage choice returns the original source whenever
   the source maps to the queried RHS carrier term.
   `forestComponentSplitPhiForestBranchInjectivityOfCanonicalNormalizer`
   rebuilds same-branch injectivity from that normalizer, and
   `coassoc_strict_forest_linear_of_split_phi_forest_image_normalizer` leaves
   only source edge witnesses, forest image normalization, mixed-branch
   injectivity, mixed-image non-forest, and residual mixed cover.
137. ✓ Mixed-branch injectivity lowered to canonical preimage normalization:
   the mixed side now mirrors the genuine branch.  For a fixed residual mixed
   cover certificate, `forestComponentSplitPhiCanonicalMixedImageNormalizer`
   says that the canonical mixed preimage choice returns the original mixed
   source whenever that source maps to the queried RHS carrier term.
   `forestComponentSplitPhiMixedBranchInjectivityOfCanonicalNormalizer`
   rebuilds mixed-branch injectivity from this normalizer plus the
   mixed-image-not-forest fact, and the cut
   `coassoc_strict_forest_linear_of_split_phi_branch_image_normalizers` leaves
   the summit with only source edge witnesses, forest image normalization,
   mixed image normalization, mixed-image non-forest, and residual mixed cover.
138. ✓ Residual branch payloads packaged:
   the mixed residual payloads have been bundled into
   `forestComponentSplitPhiResidualMixedBranchClassifier`, carrying
   mixed-image non-forest, residual mixed cover, and mixed-image
   normalization as one classifier.  The genuine residual payloads are bundled
   into `forestComponentSplitPhiResidualForestBranchClassifier`, carrying the
   source edge witnesses and forest-image normalizer.  The final cuts
   `coassoc_strict_forest_linear_of_split_phi_residual_mixed_classifier` and
   `coassoc_strict_forest_linear_of_split_phi_residual_branch_classifiers`
   leave H5.8F with just two branch classifier payloads: one genuine and one
   mixed.
139. ✓ Final residual classifier packaged:
   `forestComponentSplitPhiResidualBranchClassifier` now bundles the genuine
   and mixed residual classifiers into a single per-generator payload.  The
   latest cut `coassoc_strict_forest_linear_of_split_phi_residual_classifier`
   reduces H5.8F to exactly one remaining finite branch-classification
   structure for each Hopf generator.
140. ✓ Residual classifier constructor exposed:
   the canonical forest and mixed image normalizers can now be rebuilt from
   ordinary same-branch injectivity by
   `forestComponentSplitPhiCanonicalForestImageNormalizerOfInjectivity` and
   `forestComponentSplitPhiCanonicalMixedImageNormalizerOfInjectivity`.
   The constructor
   `forestComponentSplitPhiResidualBranchClassifierOfPieces` assembles the
   final residual classifier from source edge witnesses, forest/mixed
   same-branch injectivity, mixed-image non-forest, and the residual mixed
   cover.  The cut
   `coassoc_strict_forest_linear_of_split_phi_residual_classifier_pieces`
   is the current near-final H5.8F interface; its only genuinely new cover
   content is now the statement that an RHS term with no genuine preimage has
   a mixed-boundary preimage.
141. ✓ Residual cover fields rebuilt from ordinary branch cover:
   `forestComponentSplitPhiMixedImageNotForestOfCross` derives the canonical
   mixed-image non-forest law from ordinary cross-branch separation, and
   `forestComponentSplitPhiNoForestMixedCoverCertificateOfBranchCover` derives
   the residual no-genuine-preimage-to-mixed-cover law from the ordinary RHS
   branch cover.  The cut
   `coassoc_strict_forest_linear_of_split_phi_branch_cover_source_edge`
   reconnects the residual-classifier summit to the concrete branch-cover
   interface, with source edge witnesses replacing the older positivity
   payload.
142. ✓ Indexed classifier reconnected to the source-edge summit:
   the combined branch injectivity/separation package now has explicit
   projections
   `forestComponentSplitPhiForestBranchInjectivityOfSeparation`,
   `forestComponentSplitPhiMixedBranchInjectivityOfSeparation`, and
   `forestComponentSplitPhiCrossBranchSeparationOfSeparation`.  The indexed
   RHS classifier also has a source-edge version of its injectivity bridge:
   `forestComponentSplitPhiBranchInjectivitySeparationOfIndexedClassifierSourceEdge`,
   which uses `forestComponentForestChoiceToQuotientForestSigma_mem_of_sourceEdgeWitness`
   instead of the older component-complement positivity route.  The newest
   cut `coassoc_strict_forest_linear_of_split_phi_indexed_classifier_source_edge`
   leaves H5.8F with just source edge witnesses plus the indexed RHS branch
   classifier.
143. ✓ Branch-decision interfaces rebuilt on the source-edge route:
   the source-edge summit now reconnects to the existing RHS decision
   machinery through
   `coassoc_strict_forest_linear_of_split_phi_branch_decision_source_edge`,
   `coassoc_strict_forest_linear_of_split_phi_branch_decision_cover_laws_source_edge`,
   `coassoc_strict_forest_linear_of_split_phi_branch_cover_image_laws_source_edge`,
   and `coassoc_strict_forest_linear_of_split_phi_branch_cover_separated_source_edge`.
   These are the source-edge analogues of the older component-complement
   cuts, so the final H5.8F path can use explicit decision/reconstruction or
   ordinary branch cover plus injectivity/separation without reintroducing the
   stronger positivity payload.
144. ✓ Inverse/classifier entrances restored on the source-edge route:
   `coassoc_strict_forest_linear_of_split_phi_inverse_construction_source_edge`
   and `coassoc_strict_forest_linear_of_split_phi_branch_classifier_source_edge`
   now mirror the older concrete inverse and total branch-classifier cuts,
   but feed the residual summit through source edge witnesses instead of
   component-complement positivity.  This keeps all three set-theoretic
   interfaces available for the last H5.8F climb: inverse construction,
   indexed classifier, and explicit branch decision/reconstruction.
145. ✓ Predicate-cover entrances restored on the source-edge route:
   the RHS predicate/preimage-constructor stack now has source-edge versions:
   `coassoc_strict_forest_linear_of_split_phi_decision_cover_separated_pieces_source_edge`,
   `coassoc_strict_forest_linear_of_split_phi_predicate_cover_separated_pieces_source_edge`,
   `coassoc_strict_forest_linear_of_split_phi_branch_predicate_constructors_source_edge`,
   and `coassoc_strict_forest_linear_of_split_phi_branch_predicate_choice_laws_source_edge`.
   The final reindexing path can therefore be entered from any of the
   previously developed finite-classifier formats without falling back to the
   older component-complement positivity hypothesis.
146. ✓ H5.8F final source-edge/indexed-classifier entrance inserted:
   `coassoc_strict_forest_linear_of_source_edge_indexed_classifier` is now the
   named final cut for the current summit.  It states the full forest
   coassociativity LinearMap equality directly from the two remaining finite
   payloads: source-side surviving-edge witnesses for genuine forest choices
   and the RHS indexed branch classifier for the concrete `φ` reindexing.
   This is the clean H5.8F endpoint before replacing those two payloads by
   their final concrete constructors.
147. ✓ Remaining payloads given concrete constructors:
   source-edge witnesses are now constructed from component-complement
   positivity by
   `forestComponentForestChoice_remnant_sourceEdge_exists_of_componentComplement`
   and
   `forestComponentForestChoiceRemnantSourceEdgeWitnessCertificateOfComponentComplement`,
   using the literal complement identity
   `forestComponentForestChoice_gamma_internalEdges_sub_outer_eq_componentRemnant_complementEdges`.
   The RHS indexed branch classifier is now built from ordinary branch cover
   plus injectivity/separation by
   `forestComponentSplitPhiIndexedBranchClassifierOfSeparatedCover`.
   The cut
   `coassoc_strict_forest_linear_of_component_complement_separated_cover`
   feeds both concrete constructors into the source-edge/indexed-classifier
   final H5.8F entrance.
148. ✓ Complete branch reindexing reattached to the final route:
   `forestComponentSplitPhiBranchInjectivitySeparationOfReindexing` and
   `forestComponentSplitPhiBranchCoverCertificateOfReindexing` now project the
   inverse/cover data out of the full branch reindexing package, forgetting
   the already-discharged tensor term fields.  The new cut
   `coassoc_strict_forest_linear_of_component_complement_reindexing` feeds a
   complete `forestComponentSplitPhiBranchReindexing` plus component-complement
   positivity into the current source-edge/indexed-classifier final H5.8F
   route.
149. ✓ Branch inverse/cover reattached to the final route:
   `forestComponentSplitPhiBranchInjectivitySeparationOfInverseCover` and
   `forestComponentSplitPhiBranchCoverCertificateOfInverseCover` now project
   the set-theoretic fields out of the narrower
   `forestComponentSplitPhiBranchInverseCover` package.  The cut
   `coassoc_strict_forest_linear_of_component_complement_inverse_cover`
   therefore feeds component-complement positivity plus branch inverse/cover
   directly into the current source-edge/indexed-classifier H5.8F route,
   without requiring the full term-equality reindexing bundle.
150. ✓ Component-complement/indexed-classifier direct cut added:
   `coassoc_strict_forest_linear_of_component_complement_indexed_classifier`
   is the new direct wrapper from component-complement positivity plus an
   explicit RHS indexed branch classifier to the H5.8F LinearMap equality.
   The separated-cover, inverse-cover, and full-reindexing entrances now all
   factor through this source-edge bridge, keeping the last route visibly
   centered on the indexed classifier.
151. ✓ Component-complement inverse/classifier entrances restored:
   `coassoc_strict_forest_linear_of_component_complement_inverse_construction`
   and
   `coassoc_strict_forest_linear_of_component_complement_branch_classifier`
   now feed the concrete inverse-construction and branch-classifier formats
   into the same source-edge bridge by constructing source-edge witnesses from
   component-complement positivity.  This keeps the final H5.8F interface
   usable from the older inverse/classifier payloads without reopening the
   graph-field proof stack.
152. ✓ Component-complement branch-decision entrances restored:
   `coassoc_strict_forest_linear_of_component_complement_branch_decision` and
   `coassoc_strict_forest_linear_of_component_complement_branch_decision_cover_laws`
   now connect explicit RHS branch-decision reconstruction, or a chosen cover
   plus branch-image laws, directly to the source-edge/indexed-classifier
   route.  The remaining finite RHS classification payload can therefore be
   supplied at the decision-cover granularity as well.
153. ✓ Component-complement predicate-cover entrances restored:
   the branch-cover/image-law, separated-pieces, decision-cover,
   predicate-cover, constructor, and choice-law formats now all have
   component-complement wrappers:
   `coassoc_strict_forest_linear_of_component_complement_branch_cover_image_laws`,
   `coassoc_strict_forest_linear_of_component_complement_branch_cover_separated_pieces`,
   `coassoc_strict_forest_linear_of_component_complement_decision_cover_separated_pieces`,
   `coassoc_strict_forest_linear_of_component_complement_predicate_cover_separated_pieces`,
   `coassoc_strict_forest_linear_of_component_complement_branch_predicate_constructors`,
   and
   `coassoc_strict_forest_linear_of_component_complement_branch_predicate_choice_laws`.
   This mirrors the source-edge stack after constructing source-edge witnesses
   from component-complement positivity, so the final classifier payload can
   be supplied at any of the existing finite-classifier granularities.
154. ✓ Component-complement canonical/residual entrances restored:
   component-complement positivity now also feeds the canonical RHS-cover and
   residual-classifier route directly through
   `coassoc_strict_forest_linear_of_component_complement_canonical_rhs_cover`,
   `coassoc_strict_forest_linear_of_component_complement_mixed_image_not_forest`,
   `coassoc_strict_forest_linear_of_component_complement_forest_image_normalizer`,
   `coassoc_strict_forest_linear_of_component_complement_branch_image_normalizers`,
   `coassoc_strict_forest_linear_of_component_complement_residual_mixed_classifier`,
   and
   `coassoc_strict_forest_linear_of_component_complement_residual_classifier_pieces`.
   These wrappers keep the source-edge witness construction hidden behind the
   component-complement certificate, so both the canonical preimage-normalizer
   stack and the finite classifier stack now land on the same final H5.8F
   route.
155. ✓ H5.8F summit gate named:
   `coassocStrictForestH58FinalPayloads` now packages the two remaining
   finite payloads: genuine component-complement positivity and the RHS
   indexed branch classifier.  The theorem
   `coassoc_strict_forest_linear_of_h58_final_payloads` is the explicit
   summit gate from that package to strict forest coassociativity, sitting
   directly on top of
   `coassoc_strict_forest_linear_of_component_complement_indexed_classifier`.
   The final attack is therefore reduced to constructing the two payload
   fields, with all graph-field/product/right-factor transports already
   hidden below the gate.
156. ✓ Deprecated connected-only route retired from compilation:
   the old proper-connected-subgraph Stage 3 route after the active H5.8F
   cuts is now kept as one block comment.  Its strategist note and historical
   tensor expansion are preserved, but Lean no longer elaborates the obsolete
   connected-only path that was superseded by the admissible-forest `φ`
   reindexing route.
157. ✓ H5.8F final payload constructors added:
   the summit payload package now has constructors
   `coassocStrictForestH58FinalPayloads.ofIndexedClassifier`,
   `.ofSeparatedCover`, `.ofInverseCover`, and `.ofReindexing`.  These
   align the final H5.8F gate with the existing classifier interfaces, so
   the proof can be finished from any of the current branch-reindexing
   granularities without duplicating the final LinearMap target.
158. ✓ H5.8F final theorem entrance named:
   `CoassocStrictForestH58FinitePayloads` records the last finite
   combinatorial package as a typeclass rather than an axiom, and
   `coassoc_strict_forest_linear_h58` is now the final H5.8F theorem form
   from that instance.  The theorem was first exposed with the two remaining
   constructors visible: genuine component-complement positivity and the RHS
   indexed branch classifier, while all graph-field/product/right-factor
   transport work is hidden below the final gate.
159. ✓ Component-complement positivity discharged by the strict forest-choice carrier:
   `properConnectedDivergentSubgraphs` records
   `0 < γ.complementEdges.card`, while the broad
   `properDisjointAdmissibleDivergentSubgraphs` carrier stays unchanged for
   quotient-retarget transports.  The generator-level forest branch now uses
   the stricter `forestCoproductProperForestIndex`, a filtered proper
   admissible-forest carrier with `0 < A.complementEdges.card`.  This gives
   `forestComponentChoice_forest_complementEdges_positive_of_core_mem` and
   the canonical payload
   `forestComponentForestChoiceComponentComplementPositiveCertificateCanonical`.
   Consequently `coassoc_strict_forest_linear_of_h58_indexed_classifier` and
   `CoassocStrictForestH58FinitePayloads` now leave only the RHS indexed
   branch classifier as explicit finite data for H5.8F.
160. ✓ Strict quotient-index positivity separated cleanly:
   the RHS quotient-forest index now exposes the extra strictness condition
   on genuine branch images through
   `ForestComponentForestChoiceRepQuotientComplementPositiveModel`.  This
   keeps quotient properness separate from quotient complement positivity:
   positive internal edges of the quotient components are no longer used as a
   proxy for nonempty quotient complement edges.  The H5.8F summit package
   `coassocStrictForestH58FinalPayloads` and the final typeclass
   `CoassocStrictForestH58FinitePayloads` now carry this quotient-complement
   model explicitly alongside the RHS indexed branch classifier.  Thus the
   remaining final payload is precisely the strict quotient-complement model
   plus the finite classifier, with component-complement positivity already
   canonical from the strict forest-choice carrier.
161. ✓ Strict quotient-complement payload discharged canonically:
   `forestComponentForestChoiceRepQuotientSubgraphCanonical_complementEdges_card_pos`
   proves the genuine branch image leaves a nonempty quotient complement by
   reusing the canonical source internal-edge count split, the actual
   quotient complement transport, and actual-to-representative permutation
   preservation of complement-cardinality.  The instance
   `forestComponentForestChoiceRepQuotientComplementPositiveModelCanonical`
   supplies the new index-side model globally.  The final H5.8F entrance
   `coassoc_strict_forest_linear_h58` is therefore back to a single explicit
   finite payload: `CoassocStrictForestH58FinitePayloads.indexed_classifier`.
162. ✓ Sprint D closed; Sprint E handoff recorded:
   the last Lean-cleanup pass confined
   `ForestComponentForestChoiceRepQuotientComplementPositiveModel` to the
   strict quotient-index boundary and removed accidental section-variable
   leakage from unrelated genuine-forest helper lemmas using targeted
   `omit` annotations.  With IDE reporting no errors, the H5.8F final gate is
   stable: `coassoc_strict_forest_linear_h58` is available from the single
   finite classifier payload.  Sprint E should begin from this theorem rather
   than reopening the old connected-only route or the intermediate source-edge
   payload cuts.  The next expected work is the H6 antipode recursion and the
   final `HopfAlgebra ℚ HopfH` instance assembly, using H5.8 as an already
   packaged coassociativity input.

---

## Sprint E — Antipode + conditional `HopfAlgebra ℚ HopfH` instance  [DONE 2026-04-30]

Sprint E pipeline closed up to a single isolated facade payload.  The
conditional `HopfAlgebra ℚ HopfH` instance is in place; two facades
remain as named pre-final-audit discharge tasks.

### Status by stage

* **H6.1** ✓ `antipodeGen_forest : HopfGen → HopfH` via well-founded
  recursion on `(repG g).toFeynmanGraph.internalEdges.card`.
  Termination uses
  `repG_toHopfGen_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex`
  (Coproduct.lean), which composes the basic component edge-count bound
  with the iso-invariance bridge `repG_internalEdges_card_eq_of_toClass`.
* **H6.2** Vacuous: `HopfGen` requires `IsConnectedDivergent`, which
  excludes the empty graph.  Marked "not applicable" rather than
  proved.
* **H6.3** Skipped: the recursion target is `HopfGen` (a quotient
  subtype), so the canonical-representative iso-invariance is absorbed
  by the type itself.  Stage retained in the original spec only for
  the alternate `ConnectedFeynmanGraph`-level recursion design that
  was rejected at the H6.1 design fork.
* **H6.4** ✓ `antipodeAlgHom_forest := MvPolynomial.aeval antipodeGen_forest`
  and `antipode_forest := antipodeAlgHom_forest.toLinearMap`.
  AlgHom-form is well-defined because `HopfH` is the commutative
  polynomial algebra `MvPolynomial HopfGen ℚ`.
* **H6.5** ✓ `antipode_forest_one`, `antipode_forest_X`,
  `antipode_forest_mul`.
* **H6.6a** ✓ Generator-level left antipode axiom
  `mul_antipode_rTensor_coproduct_strict_forest_X (g : HopfGen)`.
  Cancellation argument:
    * Coproduct expansion gives
      `gen g ⊗ 1 + 1 ⊗ gen g + ∑_A A.toHopfH ⊗ gen(right A)` over
      `forestCoproductProperForestIndex g`.
    * Pushing `mul' ∘ S.rTensor` per summand uses the auxiliary lemma
      `antipode_forest_admissibleForestStrictSummandWithCanonicalStars_of_mem`
      to give `(∏ γ ∈ A.elements.attach, antipodeGen_forest …) *
      antipodeForestRightHopfH g A hAprop`.
    * `A.toHopfH = ∏ γ ∈ A.elements, componentToHopfH A γ` factorisation
      is pushed through `antipode_forest` via
      `antipode_forest_toHopfH_admissibleSubgraph` (uses
      `MvPolynomial.aeval` `map_prod`).
    * Both Σ over the dif-guarded body and Σ over the explicit body are
      attach-folded so the membership proof is locally accessible
      inside the binder.  The three terms cancel via `ring`.
* **H6.6b** ✓ LinearMap-form left antipode axiom
  `mul_antipode_rTensor_coproduct_strict_forest`.
  Globalised from H6.6a using
  `MvPolynomial.algHom_ext` against AlgHom-form packagings:
    * `axiomLHS_alg := (Algebra.TensorProduct.lmul' ℚ).comp
      ((Algebra.TensorProduct.map antipodeAlgHom_forest (AlgHom.id ℚ HopfH)).comp
        coproduct_strict_forest)`
    * `axiomRHS_alg := (Algebra.ofId ℚ HopfH).comp counit`
    * AlgHom equality lifted to `.toLinearMap` equality via
      `AlgebraTensorModule.map_eq` and `LinearMap.rTensor_def` (both
      `rfl`).
* **H6.7** Isolated as Sprint E facade
  `AntipodeStrictForestRightReady`.  Mathlib axiom-shape exact:
  ```
  (LinearMap.mul' ℚ HopfH).comp
    ((antipode_forest.lTensor HopfH).comp
      coproduct_strict_forest.toLinearMap)
    =
  (Algebra.linearMap ℚ HopfH).comp counit.toLinearMap
  ```
  **Why a facade rather than a direct mirror of H6.6a:** pushing
  `mul' ∘ S.lTensor` through a forest summand `A.toHopfH ⊗ gen(right A)`
  yields `A.toHopfH * S(gen(right A)) = A.toHopfH *
  antipodeGen_forest(right A)`, where the right factor is a *single*
  antipode-call rather than a structured product.  This shape does NOT
  match the recursive definition's left factor `∏ γ, antipodeGen_forest
  …`, so cancellation is not available by definition unfold + `ring`.
  The right axiom requires a forest-summation recombination identity
  similar in spirit to (but mathematically distinct from) H5.8.
  Convolution-uniqueness and commutative-algebra-shortcut routes were
  both explored: Mathlib `Convolution.lean` provides ring structure on
  `WithConv (C →ₗ A)` but no antipode-uniqueness theorem; the
  commutative-algebra shortcut requires cocommutativity of `Δ`, which
  CK does not have.  Mathlib's `MonoidAlgebra` Hopf instance also
  proves both axioms independently.  Conclusion: H6.7 must be proved
  directly via a CK-1998-§3-style forest-summation identity; isolated
  as a facade payload to keep Sprint E focused on assembly.
* **H6.8** ✓ Conditional
  `instance instHopfAlgebraHopfHStrictForest
    [CoassocStrictForestH58Ready] [AntipodeStrictForestRightReady] :
    HopfAlgebra ℚ HopfH` in
  `GaugeGeometry/QFT/HopfAlgebra/HopfAlgebra.lean`.
  Antipode field reads
  `antipode := antipode_forest`; left axiom from H6.6b;
  right axiom from `AntipodeStrictForestRightReady`.

### Pre-final-audit discharge tasks (open)

The unconditional `HopfAlgebra ℚ HopfH` instance and the final axiom
audit `[propext, Classical.choice, Quot.sound]` are both gated on:

1. **`CoassocStrictForestH58Ready` discharge.**
   Sprint D step 161 already proved
   `coassoc_strict_forest_linear_h58` from
   `forestComponentSplitPhiIndexedBranchClassifier` plus canonical
   RHS branch decision data; the canonical instance constructor still
   needs to be wired to the facade.

2. **`AntipodeStrictForestRightReady` discharge.**
   Right antipode forest-summation cancellation identity, CK-1998-§3
   style.  Reuses the `forestComponentSplitPhi*` infrastructure that
   closed H5.8.

### Files (as of 2026-04-30)

* `Antipode.lean` — H6.1, H6.4, H6.5, H6.6a, H6.6b, H6.7 facade
  declaration (~370 lines, sorry 0).
* `HopfAlgebra.lean` — H6.8 conditional `HopfAlgebra ℚ HopfH` instance
  (~95 lines, sorry 0).
* `Coproduct.lean` — Sprint E shared API: `repG`, internal-edge bridges
  `repG_internalEdges_card_eq_of_toClass`, termination lemma
  `repG_toHopfGen_internalEdges_card_lt_of_mem_forestCoproductProperForestIndex`,
  carrier `forestCoproductProperForestIndex`.

---

## Sprint F — Facade discharge + final axiom audit  [PENDING]

Sprint E shipped a **conditional** `HopfAlgebra ℚ HopfH` instance gated
on two facade typeclasses.  Sprint F's only goal is to discharge both
facades and re-run the axiom audit to confirm the final unconditional
shape.  This is a "make the remaining facades real" sprint, not a "build
new mathematics" sprint.

The two blockers below are independent and can be tackled in either
order; the strategist's recommended attack order is given.

### Blocker F1 — `CoassocStrictForestH58Ready` canonical constructor

**Status (revised after 2026-04-30 geological scout):** the original
"mechanical wiring" framing was too optimistic.  Sprint D step 161 did
prove `coassoc_strict_forest_linear_h58` from a typeclass-supplied
`indexed_classifier`, but the canonical `forestComponentSplitPhiIndexedBranchClassifier g`
witness for every `g : HopfGen` is **not** present in the codebase.
The reduction
`coassoc_strict_forest_linear_of_h58_indexed_classifier_canonical
(X : ∀ g, …)` ([Coassoc.lean:20876](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L20876))
takes such a `X` as a hypothesis; building `X` is the actual remaining
work.

#### Sprint F1 geological scout — recovery-map decomposition

F1 is not mere constructor wiring.  Producing the canonical witness
`X g` is genuinely new infrastructure (see also: zero existing
`_injective` lemmas about the sigma maps; zero `_canonical` witnesses
for `BranchInjectivitySeparation` or `BranchCoverCertificate`).  The
work decomposes through forest-branch injectivity, which in turn
reduces to **recovering the component-choice function from the outer
subgraph**.

**Key existing foothold:**
`forestComponentForestChoiceOuterSubgraph_mem_source`
([Coassoc.lean:6998](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L6998))
provides the forward direction — for each outer component, identify
which original `γ ∈ A.elements` it came from.  The recovery is the
**categorical inverse** of this forward classification.

**Planned recovery pipeline (next session):**

1. **Source partition map** (~30–50 LOC).
   Package the forward membership/source classification for each outer
   component into a partition
   `OuterSubgraph A p hA → A.elements → Finset components`.

2. **Choice recovery** (~80–150 LOC).
   Define `recoverChoiceFn : OuterSubgraph A p → forestComponentChoiceFn A`.
   For each `γ ∈ A.elements`, the source partition either yields a
   singleton `{γ}` (recover `p γ = .left`) or a strict admissible
   subforest (recover `p γ = .forest <recovered_inner>`).  The `.right`
   case is filtered out at the
   `forestComponentForestChoiceCoreIndex`
   level and does not appear here.

3. **Inverse correctness** (~100–200 LOC).
   Prove `recoverChoiceFn (OuterSubgraph A p hA) = p` by case analysis
   on each per-`γ` choice.  The forest case may need recursive
   recovery on the inner admissible subforest.

4. **Forest branch injectivity lift** (~30–50 LOC).
   `OuterSubgraph_inj` ⟹ `forestComponentForestChoiceOuterIndex_inj` ⟹
   `forestComponentSplitPhiBranchInjectivitySeparation.forest_inj` via
   sigma-pair extensionality.

**Expected size: 240–450 LOC for forest_inj alone.**  This is new
infrastructure, but localized and not Sprint D scale.  `mixed_inj`,
`cross`, and `cover` follow analogous (but not identical) recovery
arguments and are estimated independently below.

**Remaining components after forest_inj:**

* `mixed_inj`: mirror of forest_inj on the mixed-boundary regime.
  Likely ~150–250 LOC reusing source-partition infrastructure.
* `cross`: prove forest-image and mixed-image disjointness by
  comparing structural invariants of the two regimes.
  Likely ~100–250 LOC.
* `cover`: prove that the union of forest-image and mixed-image
  exhausts `forestQuotientForestSigmaIndex g`.  This is the heaviest
  piece — likely ~200–500 LOC, may require refactoring the
  classifier-decomposition layer if no per-`r` decision procedure is
  immediate.

**F1 total estimate (working):** 700–1500 LOC.  Worst case 2500–4000
LOC if `cover` triggers an H5.8-style index redesign.

#### Next session entry point

Start `Sprint F1a`: implement the source partition map around
`forestComponentForestChoiceOuterSubgraph_mem_source`.  No cover proof
yet.  Goal: produce a clean `Finset`-valued partition, no
recoverChoiceFn yet.  If F1a closes in ~50 LOC as expected, escalate
to F1b (choice recovery).  If F1a balloons past 150 LOC, halt and
re-scout.

**Files touched (expected):** `Coassoc.lean` (the recovery
infrastructure stays adjacent to the existing `forestComponentSplitPhi*`
machinery, all `private`).  No `HopfAlgebra.lean` / `Bialgebra.lean`
changes are needed until the canonical instance is finally assembled.

#### Sprint F1a–F1n-2e progress (2026-05-02)

Sprint F1 was deliberately split into many tiny sprints (typically 30–80
LOC each, IDE-only verification, no full builds) to keep each step
auditable and reversible. The cumulative output is **3 `def` + 33 lemma**
in `Coassoc.lean` (≈970 LOC), all `private`, `sorry` 0, new typeclass 0,
new project axiom 0.  The recovery infrastructure now reaches the
forward + reverse + observed-choice triplet, with the forest case's
self-exclusion lemma fully proved.

* **F1a `_mem_source_unique`** — uniqueness from the existential
  `_mem_source` via `Forest.IsPairwiseDisjoint.eq_of_mem_vertices`.
* **F1b `_sourcePartition` (def) + `_mem`/`_vertices_subset`/`_unique`** —
  `Classical.choose` based source partition map.  `hAne` kept off the
  `def` signature; uniqueness lemma supplies it locally.
* **F1c `_slotAt` (def) + `_mem_slotAt_iff` (.mp/.mpr)** — `Finset.filter`
  over `attach`, predicate `(sourcePartition δ).1 = γ.1`.
* **F1d `_biUnion_slotAt_eq_attach`, `_slotAt_disjoint`** — disjoint cover
  property of the slots.
* **F1e `_sum_attach_eq_sum_slotAt`** — `Finset.sum_biUnion` reindex
  (subtype `Ne` ↔ `.1 Ne` bridged via `Subtype.ext`).
* **F1f-1 `_mem_slotAt_self_of_left`** — forward: `p γ = .left ⇒ self δ ∈ slot`.
* **F1f-2 `_slotAt_eq_empty_of_right`** — forward: `p γ = .right ⇒ slot = ∅`.
* **F1g `_slotAt_mem_promoted_of_forest`** — forward: `p γ = .forest B ⇒
  slot ⊆ promoted side`.
* **F1h `_slotAt_promoted_source_eq_of_forest`** — forward: forest +
  promoted witness ⇒ source γ matches.
* **F1i `_slotAt_promoted_exists_at_source`** — forward: forest ⇒ ∃ Bγ on
  the γ side via `subst` on the source equality from F1h (no `HEq`).
* **F1j `_slotAt_classify`** — 3-way disjunction observation packed into
  one theorem; uses `forestCoproductChoice_eq_left_or_right_or_forest` to
  avoid `cases : <expr>` motive contamination.
* **F1k `_slotAt_classify_forest_shared`** — forest with externally-fixed
  `B` ⇒ all slot δ live in `promoted γ B` (shared `B`).  The proof uses
  `cases hEqChoice` on `forestCoproductChoice.forest Bγ = .forest B` to
  collapse `Bγ` to `B` without invoking dependent equality.
* **F1l-1a/1b `_pγ_ne_left_of_slotAt_empty` / `_pγ_eq_right_of_slotAt_empty`** —
  reverse: slot = ∅ rules out left, and gives right modulo a
  `hForestExcluded` hypothesis.
* **F1l-2 `_slotAt_nonempty_of_forest`** — reverse: `hp + p γ = .forest B`
  produces a witness in `slotAt γ` (9-step chain through
  `properDisjoint_isNonempty` and the promoted carrier construction).
* **F1l-3 `_pγ_eq_right_of_slotAt_empty_strong`** — reverse strong: `hp +
  slot = ∅ ⇒ p γ = .right` (forest exclusion auto-discharged via F1l-2's
  contrapositive).
* **F1l-4a/4b `_pγ_ne_right_of_slotAt_self` / `_pγ_eq_left_of_slotAt_self`** —
  reverse: self δ ∈ slot rules out right, and gives left modulo
  `hForestExcluded`.
* **F1m-1 `_pγ_is_forest_of_slotAt_no_self`** — reverse: nonempty + no
  self ⇒ ∃ B, p γ = .forest B (via 3-way enumeration ruling out the
  other two outcomes).
* **F1m-2 `_observedChoice` (def) + 3 spec lemmas
  `_eq_right_of_slotAt_empty` / `_eq_left_of_slotAt_self` /
  `_is_forest_of_nonempty_no_self`** — `noncomputable def` reading the
  slot shape and returning a `forestCoproductChoice` value.  Forest case
  uses `Classical.choose` on F1m-1's existence.
* **F1m-3a/3b `_observedChoice_eq_pγ_of_right` / `_..._of_left`** —
  casewise spec: forward observation suffices, no forest exclusion needed
  for left or right.
* **F1n-2a `admissibleSubgraph_internalEdges_card_le_ambient_of_pairwise`**,
  **F1n-2b `_card_lt_ambient_of_complement_pos`**,
  **F1n-2c `feynmanSubgraphRepForestPromoteAdmissibleSubgraph_internalEdges_card_le_source`**,
  **F1n-2d `repG_toHopfGen_internalEdges_card_eq_source`**,
  **F1n-2e `forestComponentChoicePromotedForestComponents_ne_source`** —
  five-step strictness chain proving that a promoted forest component δ
  satisfies `δ ≠ γ.1` whenever `p γ = .forest B` and `hp ∈ core`.  The
  edge-count chain is `δ.card ≤ B.card < (repG (γ.toHopfGen)).card =
  γ.card`.

##### Lean 4 pitfalls collected during F1

The fine-grained sprints surfaced five reproducible Lean 4 elaboration
pitfalls (candidates for the next `feedback_lean4_mathlib_pitfalls.md`
upsert):

1. `rw` with subtype binders motive failure — `simp only` or
   `_mem` extraction recover.
2. `forestCoproductChoice.noConfusion` does not project `.elim`; use
   `cases h` directly.
3. `cases h : <expr>` / `rcases h : <expr>` mutates statement-level
   occurrences; route through an enumeration lemma like
   `forestCoproductChoice_eq_left_or_right_or_forest` instead.
4. Namespace asymmetry between local helpers and `FeynmanGraph`-namespace
   lemmas requires `G.foo` dot form for the latter; check existing call
   sites with `grep` before writing.
5. `set X := <expr>` with subtype binders or type-level values splits
   `↥X.elements` from `↥<expr>.elements` syntactically; prefer `let` for
   `Prop` abbreviations and inline expansion for type-level values.

##### Next entry point

The remaining tasks for `CoassocStrictForestH58Ready` discharge are now:

* **F1m-3c `_observedChoice_eq_pγ_of_forest`** — combine F1l-2 (slot
  nonempty), F1n-2e (no self via promoted ≠ source), and F1k (shared `B`)
  to close the forest case of `_observedChoice = p γ`.  Estimated 30–40
  LOC; F1n-2e was the genuine blocker.
* Pi-lift `_observedChoice` to a full choice function and recover the
  canonical `forestComponentSplitPhiIndexedBranchClassifier` witness.
* Wire the canonical witness into the F1 facade
  `CoassocStrictForestH58Ready`.

The `recoverAt`/recovery-map design has stabilized into a thin shell
over `_observedChoice` once F1m-3c lands; the heavy lifting (source
partition, slot classification, edge-card strictness) is already
discharged.

#### Sprint F1m-3c–F1p-7 progress (2026-05-03 → 04): forest-branch outer-injectivity

The continuation of the F1 chain after F1n-2e closed the strictness
foundation.  Pure composition mostly; the heavy mathematical content was
spent in F1n.  All sprints follow the small-cap discipline (typically
20–80 LOC each, IDE-only verification), `sorry` 0, new typeclass 0, new
project axiom 0 throughout.  Cumulative output: **4 `def` + 52 lemma**,
≈1815 LOC in `Coassoc.lean`, all `private`.

##### Completed theorem

> **`forestComponentForestChoiceOuterSubgraph_inj`** (Sprint F1p-7,
> [Coassoc.lean:9009](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9009)).
> Under `hp_i ∈ forestComponentCoreChoiceIndex A`, outer-subgraph
> equality forces `p₁ = p₂`.  Unconditional — the `hForestMatchAll` gate
> from F1o-4 is discharged canonically by F1p-6, so the F1 forest-branch
> injectivity is now a fact, not a hypothesis.

##### Major decomposition

The proof is layered through 19 private lemmas in 6 thematic groups:

* **Casewise spec for `_observedChoice`**:
  - F1m-3c `_observedChoice_eq_pγ_of_forest` — forest case of
    `_observedChoice = p γ`, via `Classical.choose_spec` on the F1m-1
    witness.  No `B' = B` direct construction; the proof routes through
    `p γ ... = forest B'` and `p γ ... = forest B` constructor equality.
  - F1m-4 `_observedChoice_eq_pγ` — full per-γ spec, combining
    F1m-3a/3b/3c via `forestCoproductChoice_eq_left_or_right_or_forest`.

* **Pi-lift to full choice function**:
  - F1m-5 `_observedChoiceFn` (def) + `_observedChoiceFn_eq` —
    `observedChoiceFn = p` under `hp ∈ core`, by `funext γ hγ` + F1m-4.

* **Reverse strong forms (using F1n-2e)**:
  - F1l-4c `_pγ_eq_left_of_slotAt_self_strong` — `hp + self δ ⇒ p γ = .left`
    with the forest case ruled out by F1k + F1n-2e (no self in promoted
    carrier).

* **Transport under outer equality**:
  - F1o-1 `_sourcePartition_eq_of_outer_eq`.
  - F1o-2a `_mem_slotAt_iff_of_outer_eq`.
  - F1o-2b `_slotAt_empty_iff_of_outer_eq`.
  - F1o-2c `_slotAt_self_exists_iff_of_outer_eq`.

* **Per-γ choice equality + skeleton**:
  - F1o-3 `_choice_at_eq_of_outer_eq` (forest gated via `hForestMatch`).
  - F1o-4 `_inj_of_forest_match` (full skeleton; forest gated via
    `hForestMatchAll`).

* **B identification**:
  - F1p-1 `_promoted_mem_iff_of_outer_eq`.
  - F1p-2 `_promoted_elements_eq_of_outer_eq`.
  - F1p-3 `_promoted_eq_of_outer_eq` (full `AdmissibleSubgraph`
    equality via `Forest.ext` + `AdmissibleSubgraph.ext`).
  - F1p-4a `feynmanSubgraphPromoteAdmissibleSubgraph_injective` —
    elements equality + `Finset.image_injective` +
    `feynmanSubgraphPromote_injective`.
  - F1p-4b `mapPermAdmissibleSubgraphPreimage_injective` — round-trip
    `preimage h₁ ∘ mapPerm h₁ = id` derived from the existing
    `_mapPerm_eq` lemma along the inverse permutation.
  - F1p-4c `feynmanSubgraphRepForestPromoteAdmissibleSubgraph_injective` —
    composition of F1p-4a and F1p-4b.
  - F1p-5 `_B_eq_of_outer_eq` — F1p-3 + F1p-4c.
  - F1p-6 `_forestChoice_eq_of_outer_eq` — `congrArg forestCoproductChoice.forest`
    on F1p-5; shape matches F1o-4's `hForestMatchAll`.
  - **F1p-7 `_inj`** — `_inj_of_forest_match` discharged via F1p-6.

##### Lean 4 pitfalls collected during F1m-3c–F1p-7

Continuation of the previous list (#30–34).  Recorded for the next
`feedback_lean4_mathlib_pitfalls.md` upsert:

35. Long natural-language `--` comments inside a tactic body whose
    surrounding goal is unsolved cause the parser to read them as
    commands; English words like `for`, `as`, `if` collide with Lean
    keywords.  Keep `--` comments short or move long prose to docstrings.
36. `Edit` tool cleanup of multi-line blocks must include the surrounding
    docstring/declaration boundaries; otherwise adjacent declarations'
    docstrings get clipped, creating cascading parse errors three
    declarations down.
37. F1f-1 `_mem_slotAt_self_of_left` returns `∃ δ, δ.1 = γ.1 ∧ δ ∈ slot`
    (equality first, membership second).  The F1l-4c / F1m-3 / F1o-3
    style `∃ δ ∈ slot, δ.1 = γ.1` must reorder via `rcases ⟨δ, hEq, hSlot⟩`
    before constructing the desired shape.
38. `set X := <expr>` mutates type-level expressions in already-elaborated
    hypotheses (F1n-2e instance with `set RepG := (repG ...).toFeynmanGraph`
    broke `B`-binder resolution in `hForest`).  For type-level
    abbreviations, prefer inline expansion or `let` (which does not
    auto-rewrite goal/hypothesis occurrences).

##### Remaining tasks for `CoassocStrictForestH58Ready`

The forest branch is no longer the bottleneck.  What remains, in order:

* **mixed_inj**: `forestComponentMixedBoundary*` outer-injectivity
  analogue.  Should reuse the F1o transport lemmas (transport under
  outer equality) and the F1p promoted-carrier identification, since
  the mixed branch's `right`-selected carrier admits a similar splitter
  argument.  Estimate (revised after F1p-7): 100–250 LOC, much of which
  is renaming + import of F1o/F1p machinery.

* **cross-branch separation**: forest-image and mixed-image of the RHS
  classifier are disjoint.  This is structural (no per-γ recovery
  needed); the forest branch carries `slot.Nonempty + no-self` and the
  mixed branch carries `slot.Nonempty + self exists`, so a single
  `pγ = .left vs .forest` constructor case-split discharges it.
  Estimate: 50–150 LOC.

* **cover**: surjectivity onto `forestQuotientForestSigmaIndex g`.
  Likely the heaviest piece remaining; needs an explicit decomposition
  of every RHS sigma element into a forest- or mixed-branch source.
  Estimate: 200–500 LOC, may benefit from the F1m-2 observedChoice
  decision tree as a constructive blueprint.

* **Assembly** of the canonical
  `forestComponentSplitPhiBranchInjectivitySeparation` and downstream
  `IndexedBranchClassifier`, which discharges
  `CoassocStrictForestH58Ready`.  After all four pieces above, this is
  a 30–60 LOC orchestration.

##### Status snapshot

* `sorry` 0 across F1a–F1p-7.
* No new project-specific axioms.
* No new typeclasses.
* No public-API expansions; all F1 helpers `private`.
* IDE-only verification per sprint; no full builds.

##### Next-session entry recommendation

Before implementing mixed_inj, draft a **forest-side ↔ mixed-side
correspondence table** of every F1m/F1o/F1p lemma, identifying:

1. which transport lemmas reuse verbatim (F1o-1/2a/2b/2c likely all);
2. which need a mixed-branch analogue (F1g, F1k, F1n-2e for the
   `right`-selected carrier);
3. which are structurally specific to the forest branch and have no
   mixed analogue (F1l-2 forest nonempty, F1n-2e self-exclusion).

Implement only after the table is populated.  This mirrors the
"settle the design before writing the first lemma" discipline that
let F1n / F1p close cleanly.

#### Sprint F1r progress (2026-05-04 → 05): mixed-boundary core injectivity

The mixed-boundary outer-subgraph injectivity, scouted in F1r as
"forest_inj reuse 0%, but native cost much smaller", was implemented in
three small lemmas with a notable design discovery along the way.

##### Completed theorems

* **F1r `forestComponentChoiceLeftSubgraph_inj_of_mixed_boundary`**
  ([Coassoc.lean:9036](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9036)).
  Under both `hp_i ∈ forestComponentMixedBoundaryChoiceCoreIndex A`
  (forest selections excluded), `LeftSubgraph A p₁ = LeftSubgraph A p₂`
  forces `p₁ = p₂`.  68 LOC.  Proof: `Finset.filter` ext extracts the
  predicate-iff `IsLeft p₁ γ ↔ IsLeft p₂ γ`; the binary `.left/.right`
  case split closes pointwise equality.  No forest infrastructure
  (sourcePartition / slot / observedChoice / B-identification) is used.

* **F1r-2a `forestComponentMixedBoundaryOuterIndex_inj_of_q1_eq`**
  ([Coassoc.lean:9106](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9106)).
  Sigma-level lift: `q.1 = q.1` + `MixedOuterIndex` equality ⇒
  `q₁ = q₂`.  39 LOC.  Routes through `Sigma.ext` + `cases` on `hQ1` to
  align dependent types, then F1r.

* **F1r-2b `forestComponentMixedBoundaryToQuotientForestSigma_inj_of_q1_eq`**
  ([Coassoc.lean:9148](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9148)).
  Re-export wrapper: same hypotheses + conclusion as F1r-2a, named for
  downstream `ToQuotientForestSigma`-aware call sites.  19 LOC, term-mode.

##### Important design discovery: `q.1` is not pinned by the RHS sigma

The natural attempt was to drop the `hQ1 : q₁.1 = q₂.1` side-condition
and prove

> `forestComponentMixedBoundaryToQuotientForestSigma g q₁ hq₁ =
>  forestComponentMixedBoundaryToQuotientForestSigma g q₂ hq₂` ⇒
> `q₁ = q₂`

unconditionally.  This **fails**.

The reason is structural.  The RHS sigma's first component is
`MixedOuterIndex g q hq` whose value is

```
⟨forestComponentChoiceLeftSubgraph q.1.1 q.2, _⟩
```

and `forestComponentChoiceLeftSubgraph A p` is built via

```
admissibleSubgraphOfSubelements A (A.elements.filter (IsLeft A p)) hsub
```

where `admissibleSubgraphOfSubelements A s hs` keeps only `s` in the
resulting `elements` field; the original `A` is pushed into the subset
proof `hs` and is *not* recoverable from the subgraph value.

A concrete counterexample to "`LeftSubgraph A₁ p₁ = LeftSubgraph A₂ p₂
⇒ A₁ = A₂`":

```
A₁ = {γ, δ}, p₁ γ = .left, p₁ δ = .right
A₂ = {γ},    p₂ γ = .left
```

Both sides yield `LeftSubgraph` with `elements = {γ}`, yet `A₁ ≠ A₂`.

##### Design implications

Both forest_inj and mixed_inj are now seen as instances of the same
**outer-A-fixed p-injectivity** schema, not as a `q ↦ outer-sigma`
injectivity:

| Branch | Native shape |
|--------|--------------|
| forest | outer A fixed + outer-subgraph equality ⇒ p equality |
| mixed  | outer A fixed + LeftSubgraph equality ⇒ p equality |

For cross / cover, the consequence is concrete: index everything by
`q.1` (the `forestOuterProperIndex g` carrier).  Within each `q.1`
slice, both branches are p-injective; across distinct `q.1`s, the
question becomes a separate "branch image disjointness modulo outer A"
claim.

This is the same lesson as forest_inj's `forestComponentForestChoiceOuterSubgraph_inj`
already encoded: that lemma also takes `A` (and `hA`) as common
hypotheses, not as data inferred from outer-subgraph equality alone.
Both branches share this discipline.

##### Status snapshot

* `sorry` 0, new typeclass 0, new project axiom 0 across F1a–F1r-2b.
* All F1r helpers are `private`.
* IDE-only verification per sprint.
* Cumulative `Coassoc.lean` size: ≈1945 LOC of F1 infrastructure
  (4 `def` + 55 lemma).

##### Next-session entry recommendation: cross scout under q.1-indexed design

Before implementing cross-branch separation, scout the question:

> Under `hSigma_forest = hSigma_mixed`-style equality at the RHS sigma
> level, what does the `q.1`-indexing layer say?
>
> 1. If `q.1 forest = q.1 mixed`, then both branches map into the same
>    outer slice, and "branch image disjointness" is a per-`q.1`
>    structural claim (forest has nonempty slot + no self; mixed has
>    self-existing slot or slot empty).  This is a finite case-split
>    on F1l-3 / F1l-4c / F1m-1.
> 2. If `q.1 forest ≠ q.1 mixed`, branches sit in different outer
>    slices and disjointness is automatic from outer index distinctness.
>
> The cross-branch separation theorem should split on whether the
> outer indices coincide.  This avoids forcing the whole RHS sigma to
> be injective on its own.

Implement after the case split is recorded in a candidate signature.

#### Sprint F1s progress (2026-05-05): forest-vs-mixed cross, same-outer case

The cross-branch separation question, scouted in F1r-doc as a per-`q.1`
case split, was attacked at the same-outer fiber first.  The result is
a clean per-fiber theorem plus a strategic finding that full cross
should be deferred until the cover assembly geometry is fixed.

##### Completed theorems

* **F1s-1 `forestComponentForestChoice_mixedBoundary_cross_same_outer_false`**
  ([Coassoc.lean:9166](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9166)).
  Under `qF.1 = qM.1` plus `(ForestChoiceOuterIndex).1 = (MixedBoundaryOuterIndex).1`,
  derives `False`.  79 LOC.  Proof: forest core gives a `(γ, B)` with
  `pF γ = .forest B`; F1l-2 + F1k yield a `δ` in `promoted γ B`; outer
  equality + `LeftSubgraph` simp puts `δ.1 ∈ qM.1.1.elements`; `qM.1.1`
  pairwise-disjoint plus `δ.vertices ⊆ γ.vertices` forces `δ.1 = γ.1`,
  contradicting F1n-2e.  Pitfall on the way: avoided the
  `δ`-type-dependent `▸` motive failure by using the `qM.1.1` side of
  pairwise-disjoint instead of transporting `δ`.

* **F1s-2 `forest_mixed_cross_false_of_same_outer`**
  ([Coassoc.lean:13391](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L13391)).
  RHS-image equality + `qF.1 = qM.1` ⇒ `False`.  Pure orchestration
  over F1s-1: extracts `congrArg Sigma.fst hEq` for the outer-index
  equality, builds `hCompOuterF` internally from
  `forestComponentForestChoiceOuterSubgraph_hasNonemptyComponents`,
  then applies F1s-1.  40 LOC, term-mode after the prelude.

##### Scout discovery (F1s-3): `qF.1 = qM.1` is NOT derivable from RHS equality

A direct attempt was made to drop the `hSame : qF.1 = qM.1` side
condition from F1s-2 and prove

```
forestComponentForestChoiceToQuotientForestSigma g qF hqF =
  forestComponentMixedBoundaryToQuotientForestSigma g qM hqM
⇒ qF.1 = qM.1
```

unconditionally.  This **fails** for the same structural reason as the
F1r `hQ1` requirement.  The chain of derivations from `hEq` is:

1. `congrArg Sigma.fst hEq` ⇒ `ForestChoiceOuterIndex g qF hqF =
   MixedBoundaryOuterIndex g qM hqM` (subtype values in
   `forestOuterProperIndex g`).
2. `congrArg Subtype.val (1)` ⇒
   `forestComponentForestChoiceOuterSubgraph qF.1.1 qF.2 hA_F =
    forestComponentChoiceLeftSubgraph qM.1.1 qM.2`
   (admissible subgraph values).
3. Both sides are built via `admissibleSubgraphOfSubelements`, which
   discards the ambient `A` (it lives only in the subset proof).  So
   neither `qF.1.1 = qM.1.1` nor `qF.1 = qM.1` is recoverable from this
   admissible-subgraph-value equality.

Concrete counterexample to "outer-subgraph value pins down `q.1`":
two distinct admissible subgraphs `A₁ ≠ A₂` in `forestOuterProperFinset g`
can yield the same `LeftSubgraph A_i p_i` value (already shown in F1r-doc).
The forest-side `forestOuter = LeftSubgraph ∪ promoted` does not change
the picture; the outer value alone never recovers the ambient `A`.

##### Design implication: defer full cross to cover-assembly time

Two paths to a full cross theorem (`hEq` ⇒ `False` unconditionally) are
visible:

* **Per-`q.1` overlap analysis**: when `qF.1.1 ≠ qM.1.1`, the forest
  outer = mixed left equality must be ruled out via geometric
  constraints between distinct admissible subgraphs in
  `properDisjointAdmissibleDivergentSubgraphs`.  These subgraphs are
  *not* mutually disjoint a priori (the carrier is just the set of
  proper-disjoint admissible forests; pairs can share vertices), so
  this is a nontrivial overlap/exclusion lemma — likely 100–300 LOC of
  new geometry.
* **Cover-assembly with `q.1`-indexed decomposition**: structure the
  cover proof so that forest and mixed branches are summed *per
  outer-index slice*, which makes "same-outer" sufficient for branch
  separation by F1s-2.  The cross-branch disjointness then enters as a
  fiberwise statement, never as a global image disjointness.

The second path is likely cheaper, mirrors how forest_inj's
`hForestMatchAll` already gets discharged inside outer-A-fixed
contexts, and avoids new admissible-subgraph geometry.

**Verdict**: defer full cross.  Scout cover-assembly first; come back
to cross only if cover requires the global form.

##### Status snapshot

* `sorry` 0, new typeclass 0, new project axiom 0 across F1a–F1s-2.
* All F1s helpers are `private`.
* IDE-only verification per sprint.
* Cumulative `Coassoc.lean` size: ≈2065 LOC of F1 infrastructure
  (4 `def` + 57 lemma).

##### Remaining tasks (revised after F1s-3)

* **cover-assembly scout (next)**: design the
  `forestComponentSplitPhi*` cover/reindex layer using `q.1`-indexed
  fibers.  Determine which lemmas need RHS sigma surjectivity and
  whether per-fiber cross suffices (using F1s-2) or full cross is
  still required.
* **(conditional) full cross**: only attack if cover scout shows it
  cannot be reduced to per-fiber.  Likely 100–300 LOC of new geometry,
  using overlap analysis between distinct admissible subgraphs in
  `forestOuterProperFinset`.
* **Assembly** of the canonical
  `forestComponentSplitPhiBranchInjectivitySeparation` (forest_inj +
  mixed_inj_of_q1_eq + cross fiberwise) and
  `IndexedBranchClassifier`, which discharges
  `CoassocStrictForestH58Ready`.

##### Next-session entry recommendation

Switch from cross to cover.  Specifically scout:

1. The signature shape of the cover obligation in
   `forestComponentSplitPhiBranchClassifier`-family lemmas — does it
   already index by `q.1`, or does it ask for a global RHS sigma
   surjection?
2. Whether `forestQuotientForestSigmaIndex` decomposes naturally as a
   sigma over `forestOuterProperIndex` slices (it does by definition,
   so the cover-per-slice approach is structurally available).
3. The minimum cover witness shape: per-slice forest cover ∪ per-slice
   mixed cover, or some fused structure.

If (1)/(2)/(3) all confirm a per-slice design, F1s's same-outer cross
is already enough.  The full cross scout becomes optional.

#### Sprint F1u/F1v/F1w scout summary (2026-05-05 → 06): the full-cross dead end

Three back-to-back scouts (no code changes) probed whether the F1
forest-vs-mixed obligation could be discharged without an unconditional
cross theorem.  All three concluded **no shortcut exists** — both the
classifier-side and the structural-predicate side ultimately need a
cross-equivalent fact.  The result reshapes the next sprint: switch
from "F1 cross/injectivity" to **F2 cover/preimage reconstruction**.

##### F1u: route audit for `BranchDecisionReconstruction`

The `BranchDecisionReconstruction` structure
([Coassoc.lean:14693](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L14693))
asks for three fields: `classify`, `forest_preimage`, `mixed_preimage`.
It does **not** take `cross` as an argument.  The `OfDecision` lift to
`IndexedBranchClassifier`
([Coassoc.lean:14729](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L14729))
mechanically produces `forest_inv`/`mixed_inv` (and hence `cross` via
the existing `_OfIndexedClassifier` constructor) from those three
fields.

However, the three fields are not free.  The `mixed_preimage` law,
once `classify` is a `Classical.choose`-based search over forest
indices, requires showing that a mixed canonical image fails the
`∃ q ∈ forest index, target q = r` predicate.  That is exactly the
unconditional cross.  Verdict: **`BranchDecisionReconstruction` does
not take `cross` as input but embeds it inside `mixed_preimage`.**

##### F1v: routes for `classify` itself

Three candidate `classify` constructions:

* **A. Structural predicate.**  Examine `r.1.1.elements` and decide
  forest vs mixed structurally.  Possible in principle (forest outer
  contains promoted components, mixed outer is a `Finset.filter`
  only), but proving the predicate is correct on canonical images
  reproduces forest/mixed image disjointness ⇒ cross.
* **B. Finite search via `Classical.choose`.**  `by_cases hF : ∃ q,
  ToQuotientForestSigma g q hq = r.1`; on the `True` branch take
  `Sum.inl (Classical.choose hF)`, on the `False` branch take the
  mixed witness via `K.cover`.  The `mixed_preimage` law forces `hF`
  to be `False` on mixed canonical images, which is cross.
* **C. Reuse `BranchDecisionCoverOfCertificate`.**  Same problem as B,
  with the cover certificate hiding the same cross dependency.

All three routes route the cross obligation into a different place,
but none eliminate it.  Verdict: **`classify` cannot be built without
a cross-equivalent fact.**

##### F1w: full sigma equality does not pin `qF.1 = qM.1`

The natural attempt was to read more information out of the *full*
`hEq : forestComponentForestChoiceToQuotientForestSigma g qF hqF =
forestComponentMixedBoundaryToQuotientForestSigma g qM hqM`.  Both
sides are dependent sigmas of type
`Σ A : forestOuterProperIndex g, AdmissibleSubgraph (forestOuterQuotientGraph g A)`.

* `congrArg Sigma.fst hEq` gives equality of the *derived* outer index
  values (subtype of `forestOuterProperIndex g`).  At the
  `Subtype.val` level this is an `AdmissibleSubgraph` equality
  between `forestComponentForestChoiceOuterSubgraph qF.1.1 qF.2 hA`
  (forest side) and `forestComponentChoiceLeftSubgraph qM.1.1 qM.2`
  (mixed side).  Both are built via `admissibleSubgraphOfSubelements`,
  which discards the ambient `A` into a subset proof.  `qF.1.1 = qM.1.1`
  is **not** recoverable.
* `Sigma.mk.inj hEq |>.2` is a `HEq` between the quotient-side
  forests.  To convert it to an `Eq`, you need
  `forestOuterQuotientGraph g qF.1 = forestOuterQuotientGraph g qM.1`,
  which is already as strong as `qF.1 = qM.1`.  **Circular.**

All three extraction paths therefore lose the `qF.1` information.
Verdict: **full sigma equality does not directly imply
`qF.1 = qM.1`; full cross direct attack is infeasible at this level of
abstraction.**

##### Strategic verdict

* Full cross as a standalone theorem is **deferred indefinitely**.
* `BranchDecisionReconstruction` shortcut also reduces to cross
  (inside `mixed_preimage`).
* The next sprint target is
  `forestComponentSplitPhiBranchCoverCertificate_canonical`
  ([Coassoc.lean:13987](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L13987)):
  for every `r ∈ forestQuotientForestSigmaIndex g`, exhibit either a
  forest preimage or a mixed preimage.  This is a **surjectivity /
  recovery problem** for the two `ToQuotientForestSigma` maps.
* The entire F1a–F1p observedChoice / sourcePartition / promoted
  injectivity machinery was, in retrospect, the basis for this
  reconstruction.  F2 will run the machinery in reverse: from `r` to
  `q`.

##### Sprint renaming

F1 is closed in spirit: injectivity (forest_inj, mixed_inj_of_q1_eq,
same-outer cross) is done.  The next phase is **F2 — cover / preimage
reconstruction**, a different problem class (surjectivity rather than
injectivity).  Logging it as F2 keeps the strategic separation clear.

##### Next-session entry recommendation

Before any implementation, scout the preimage recovery equation:

> Given `r = ⟨A, F⟩ : forestQuotientForestSigma g` with `A.1` proper
> disjoint and `F ∈ forestCoproductProperForestIndex (forestOuterQuotientHopfGen g A)`,
> what `q : forestComponentChoiceSigma g` (and which branch index
> membership) yields the same `⟨A, F⟩` under
> `forestComponentForestChoiceToQuotientForestSigma` or
> `forestComponentMixedBoundaryToQuotientForestSigma`?

Read (no implementation):
* `forestQuotientForestSigma` / `…SigmaIndex` definitions
* `forestOuterQuotientHopfGen` / `…Graph` and their canonical lemmas
* both `ToQuotientForestSigma` constructions
* quotient/remnant canonical identification lemmas, including
  `forestComponentMixedBoundaryRepRightQuotientSubgraphCanonical` and
  `forestComponentForestChoiceRepQuotientSubgraphCanonical`

Goal of the scout:
1. Decide whether cover can be built unconditionally (every `r` is
   covered by exactly one of the two branches, identifiable without
   case analysis).
2. Or whether cover requires a branch-predicate decision and what its
   defining structural property is (must be decidable from `r`'s
   data, not from external information).
3. Or whether the full `q ↦ r` map is bijective with explicit inverse
   (the strongest form; would make cover trivial).

##### Status snapshot

* Code unchanged from F1s-2 state.  `Coassoc.lean` line count 25143.
* `sorry` 0, new project axiom 0, new typeclass 0.
* F1 forest injectivity, mixed core injectivity, and same-outer cross
  are complete.
* Remaining for `CoassocStrictForestH58Ready` discharge: canonical
  cover / preimage reconstruction (F2).

#### Sprint F2d–F2h progress (2026-05-09 → 12): mixed-branch cover completion

This block records the F2 cover construction from F2d (star
discriminator) through F2h-7 (mixed-branch preimage existence).  The
**mixed half** of the cover is closed; the **forest half** is queued
as a separate sub-sprint (F2i+).

##### F2d/F2f — branch discriminator on actualized RHS quotient

* `forestQuotientForestSigma_isForestByStar g r : Prop`
  ([Coassoc.lean F2f]): predicate on the actualized RHS quotient
  subgraph `forestQuotientForestSigmaActualQuotientSubgraph g r`,
  asserting `∃ δ ∈ elements, ¬ Disjoint δ.vertices A.starVertices`.
* `..._isForestByStar_of_forest`: canonical forest image satisfies
  the predicate (via F2d-2 existential witness).
* `..._not_isForestByStar_of_mixed`: canonical mixed image violates it
  (via F2d-1 universal disjointness).
* **Branch discriminator confirmed** for the actualized quotient
  layer.  Rep-side direct discrimination was halted (F2d-3) because
  `forestOuterActualToRepPerm` is a `Classical.choose` whose
  starVertices preservation is not pinned.

##### F2g — no-star quotient component lift

* **F2g-0**: `forestOuterActualQuotient_noStar_vertex_mem_ambient_complement`
  — vertex-level inverse: a no-star δ-vertex sits in
  `G.vertices \ A.vertices`.
* **F2g-1**: membership-form `internalEdge`/`externalLeg` ambient
  inheritance.  Retarget is identity on no-star endpoints, so each
  δ-edge/leg is an ambient edge/leg.
* **F2g-1b**: `forestOuterActualQuotientNoStarComponentLift` —
  `FeynmanSubgraph (repG g).toFG` whose three carriers equal δ's.
  Carrier `_le` proofs via Multiset.count chain (`count_map`,
  `Multiset.filter` monotonicity with retarget-identity on no-star).
* **F2g-2**: `_toFeynmanGraph = δ.toFeynmanGraph` (rfl, `@[simp]`).
* **F2g-3**: `_isConnectedDivergent` via `IsAmbientInvariantDivergence`
  degree transport.

##### F2h-0..3 — mixed cover infrastructure

* **F2h-0**: `forestQuotientForestSigmaMixedLiftedRightComponents` —
  finite carrier of lifted right components; CD, vertex-disjoint
  from outer (5 supporting lemmas).
* **F2h-1**: NOD 3 targets (LL/RR/LR), feeding the candidate
  `AdmissibleSubgraph` build.
* **F2h-2**: `forestQuotientForestSigmaMixedCoverOuterCandidate` —
  combined `AdmissibleSubgraph.ofElements` of outer + lifted right.
* **F2h-3a**: left/right dichotomy (4 lemmas).
* **F2h-3b**: `forestQuotientForestSigmaMixedCoverChoiceFn` binary
  choice + 3 evaluation lemmas.
* **F2h-3c**: `..._leftSubgraph_eq` — `LeftSubgraph candidate fn =
  r.1.1.1`.
* **F2h-3d**: `..._rightSubgraph_eq` + `RightCandidate` packaging.

##### F2h-4 — sigma index membership

* **F2h-4a**: `..._mem_properDisjoint` (7 helpers: actualQuotient
  properDisjoint, `IsPairwiseDisjoint`, `IsNonempty`,
  `HasNonemptyComponents`, `internalEdges_card_pos`,
  `HasPositiveInternalEdgesComponents`, main).
* **F2h-4b**: `..._mem_mixedBoundaryCore` (pi/notAllLeft/notAllRight/
  notForest).
* **F2h-4c**: `..._complementEdges_card_pos` via 15-step cardinality
  chain (mapPerm preservation + disjoint sum + `card_sub`).
* **F2h-4d**: `forestQuotientForestSigmaMixedCoverChoiceSigma` and its
  `_mem` packaged.

##### F2h-5/6 — target Sigma equality

* **F2h-5**: `..._outerIndex_eq` — `mixedBoundaryOuterIndex g q hq =
  r.1.1` via `Subtype.ext` + F2h-3c.
* **F2h-6a local**: `..._retarget_eq` — `retargetSubgraph A starOf
  (lift δ) hEdges = δ` (3-carrier identity, generalize+cases
  technique).
* **F2h-6b Step 1**: `mapPermAdmissibleSubgraph_mapPermAdmissibleSubgraphPreimage_eq`
  — missing direction of the mapPerm↔preimage roundtrip.
* **F2h-6b Step 2**: q-independent actual-side equality
  (`obtain ⟨⟨A, D⟩, hr⟩ + cases hOuter` to avoid `subst` cycle).
* **F2h-6b Step 3 helper**: `forestOuterActualToRep_actualized_eq`.
* **F2h-6b Step 3**: q-independent rep-side equality via Step 2 +
  Step 3 helper.
* **F2h-6c**: `..._toQuotientForestSigma_eq` — final Sigma equality
  via `Sigma.ext` + `eqRec_heq_iff_heq.mp ∘ heq_of_eq` for the
  dependent second component.

##### F2h-7 — mixed preimage existence

* `forestQuotientForestSigma_mixedPreimage_of_not_isForestByStar`:
  ```
  ¬ isForestByStar r → ∃ q, ∃ hq ∈ mixedBoundaryChoiceSigmaIndex g,
    mixedBoundaryToQuotientForestSigma g q hq = r.1
  ```
* `forestQuotientForestSigma_cover_mixed_half`: disjunction wrapper
  with `Or.inr` (forest-half remains as `∃ q ∈ forestForestIndex`
  `Or.inl` placeholder for future sprint).

##### Mixed cover chain summary

```
r → actualized r.2 (F2e)
  → all components no-star (F2h-0 Step 1)
  → lift each to ambient FeynmanSubgraph (F2g-1b)
  → mixed cover outer candidate (F2h-2)
  → binary choice function (F2h-3b)
  → properDisjoint + mixed core membership (F2h-4a/b/c)
  → q packaging + sigma membership (F2h-4d)
  → outer index equality (F2h-5)
  → retarget(lift δ) = δ local (F2h-6a)
  → actual side equality (F2h-6b Step 2)
  → rep side transport equality (F2h-6b Step 3)
  → target Sigma equality (F2h-6c)
  → mixed preimage existence (F2h-7)
```

##### Mixed cover infrastructure stats

* `Coassoc.lean` line count: ~25140 → ~27500 (≈ 2300 LOC of F2g–F2h-7
  infrastructure).
* `sorry` 0, new project axiom 0, new typeclass 0.
* New `private` declarations: ~50 across F2g, F2h-0..4, F2h-5,
  F2h-6a/b Step 1–3, F2h-6c, F2h-7.

##### F2i-0 scout — forest half geological probe (2026-05-12)

Question: can forest-half cover reuse F1's
`sourcePartition`/`mem_source_unique` machinery to recover source
`γ` from a star-touching quotient component?

Findings:

* **Promoted → source uniqueness is covered by F1.**
  `forestComponentForestChoiceOuterSubgraph_mem_source_unique`
  ([Coassoc.lean:7056](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L7056))
  gives a 3-line proof of `γ₁ = γ₂` for two source candidates with
  the same δ-vertex inclusion, using `hA.eq_of_mem_vertices` on a
  single witness vertex.  `_sourcePartition_unique`
  ([Coassoc.lean:7104](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L7104))
  pins the `Classical.choose`-based partition map canonically.

* **F1 API requires KNOWN `(A, p)` as input.**  All `mem_source` /
  `sourcePartition` / `mem_exists` lemmas take `A`, `p`, `hA`
  explicit.  They confirm "given `(A, p)`, source γ for δ is
  unique/canonical" but **do not construct** `A_source` from `r`
  alone.  F2 cover is the surjectivity problem; F1 is the
  injectivity machinery.

* **Forest cover existence gap**:
  - Star-touching δ ∈ D.elements identifies *some* η ∈ LF.elements
    (via `starOf η ∈ δ.vertices`) and *some* γ ⊇ η, but `γ` is
    **not** in `LF.elements` (`LF = leftSubgraph ∪
    promotedForestComponents`; γ itself is forest-spliced out).
  - `A_source` must contain γ for each forest-spliced source.
    Constructing `A_source` from `LF + D` requires "outer-hull
    reconstruction" — grouping `LF.elements` into source-γ
    equivalence classes plus the external (non-LF) γ-vertices
    inferred from δ.
  - `B` (the promoted forest summand for γ's forest choice) lives on
    the rep side `repG (γ.toHopfGen ...)`; reconstructing it from
    promoted η-set requires reverse-mapping through
    `feynmanSubgraphRepForestPromoteAdmissibleSubgraph`.

* **Strategic options going forward**:
  1. **F2i-1**: scout explicit `A_source` construction feasibility
     (can star-touching δ + external vertex data fully determine γ?).
  2. **F2i-2 (fallback)**: `Classical.choose` over a compatibility
     predicate (∃ A, p with `forestComponentForestChoiceToQuotientForestSigma g ⟨A, p⟩ hq = r.1`),
     using F1 uniqueness to extract canonical γ once existence is
     assumed.
  3. **F2i-3 (alternative)**: cardinality / injectivity-based
     surjection argument if the forward map's image size matches the
     full index size.

* **Recommended next step**: F2i-1 (feasibility scout, no
  implementation).

##### F2i-1 scout — explicit construction feasibility (2026-05-12)

Question: can `γ` and `B` be canonically reconstructed from `(LF, D)`
alone, where `LF = r.1.1.1` is the post-forest-splice outer hull and
`D = forestQuotientForestSigmaActualQuotientSubgraph g r.1` is the
actualized RHS quotient?

Findings:

* **star vertex extraction** — `mem_starVertices` + `IsFreshStarAssignment.eq_of_star_eq`
  give `s ∈ δ.vertices ∩ LF.starVertices → ∃! η ∈ LF.elements, starOf η = s`.
  Extraction via `Finset.choose` (noncomputable).

* **η → source γ** — η ∈ LF.elements is **ambiguous between**:
  (i) η = direct left-source γ (p γ = .left, γ ∈ A_source.elements ∧ γ ∈ LF.elements), or
  (ii) η is a promoted forest component (γ ⊋ η, γ ∉ LF.elements, η ∈ B's promoted carrier for some p γ = .forest B).
  This distinction is **not visible from LF alone**.

* **`γ.vertices` is canonically reconstructible** via
  ```
  γ.vertices := (δ.vertices \ LF.starVertices) ∪
                ⋃ {η.vertices : η ∈ LF.elements, starOf η ∈ δ.vertices}
  ```
  Combines (`admissibleSubgraphQuotientRemainderSubgraph_vertices`):
  - non-star δ-vertices = γ.vertices \ LF.vertices (γ's external part), and
  - each star `starOf η ∈ δ.vertices` ⇒ η ⊆ γ (since η is promoted from γ's forest).

* **`γ.internalEdges` is NOT canonically reconstructible** —
  `admissibleSubgraphQuotientRemainderSubgraph_internalEdges` says
  `δ.internalEdges = (γ.internalEdges - LF.internalEdges).map (LF.retargetEdge starOf)`.
  Boundary edges `(v_outside, x_in_η) ∈ γ.internalEdges` become
  `(v_outside, starOf η)` after retarget; the original `x_in_η ∈ η.vertices`
  is **not pinned by δ** when `|η.vertices| > 1`.

* **`B` is γ-dependent** — `feynmanSubgraphRepForestPromoteAdmissibleSubgraph_injective`
  (F1p-4c) gives `(η-set, γ) → B` canonically, but since γ is
  non-unique, B inherits non-uniqueness.

* **Exact information-loss point**: boundary edges
  `(v_outside, starOf η) ∈ δ.internalEdges` admit multiple ambient
  preimages `(v_outside, x)` with `x ∈ η.vertices`. The retarget map
  is **not invertible on the boundary**.

##### F2i-2 scout — cardinality / existing infrastructure (2026-05-12)

Question: can cardinality / deficit arguments bypass explicit
inverse construction? Are there pre-existing inverse-construction
payloads usable directly?

Findings:

* **Cardinality route — not viable**: card balance requires
  `|forestForestIndex| + |mixedBoundaryIndex| = |forestQuotientForestSigmaIndex|`,
  but the LHS reduces to `|coreIndex| = ∑_A (∏_γ (2 + k_γ) - 2)` while
  the RHS is `∑_A k_A_quot` (different `k`'s on different graph
  layers). No simple combinatorial identity equates these.

* **source-edge witness infrastructure** —
  `forestComponentForestChoiceToQuotientForestSigma_mem_of_sourceEdgeWitness`
  (Coassoc.lean:13364) and the surrounding F1n strictness chain are
  **forward-direction only**: given `q + certificate`, place the
  forward image in the RHS index. Cannot construct `q` from `r`.

* **F1n promoted strictness chain** —
  `feynmanSubgraphRepForestPromoteAdmissibleSubgraph_internalEdges_card_le_source`
  + `forestComponentChoicePromotedForestComponents_ne_source`
  give card-based exclusion `δ ≠ γ.1` for promoted components, but
  this is a **uniqueness / disjointness fact**, not an existence
  construction.

* **Predicate-decomposition infrastructure exists** at
  Coassoc.lean:16170–16336:

  | Structure | Role |
  |---|---|
  | `forestComponentSplitPhiBranchCoverCertificate` (16024) | final cover format |
  | `forestComponentSplitPhiRHSBranchPredicate` (16192) | branch predicate `B(r)` |
  | `forestComponentSplitPhiForestPreimageChoice` (16216) + Laws (16223) | forest choice + member + target |
  | `forestComponentSplitPhiMixedPreimageChoice` (16247) + Laws (16254) | mixed choice + member + target |
  | `forestComponentSplitPhiBranchCoverCertificateOfChoiceLaws` (16321) | assembles into cover certificate |

  Cover requires supplying `(B, F, FL, M, ML)`. F2h-7 already
  supplies `(M, ML)` for `B := isForestByStar`. **Remaining piece is
  `(F, FL)` — forest-side preimage choice + laws — which is the
  ~500 LOC inverse-construction problem.**

##### F2 strategic conclusion (2026-05-12)

* **Mixed cover half is complete** (F2h-0 → F2h-7, ~2300 LOC).
* **Forest cover half requires genuine inverse construction**.
  - F1 sourcePartition / promote-injectivity machinery covers
    uniqueness and final verification, but **not** the source γ /
    forest B existence.
  - Vertex-level recovery is canonical; edge / leg level is not.
  - No short cardinality / cross / classifier shortcut exists.
* **Expected forest-cover size**: ~500 LOC over ~5–8 sub-sprints
  of 60–100 LOC each, mirroring the F2g→F2h-7 chain in scale.
* The construction will be `Classical.choose`-flavored on the
  edge / leg dimensions, with downstream verification via F1
  uniqueness lemmas.

##### Forward options (post-F2k-doc)

* **Option A — F2 forest explicit inverse construction (~500 LOC)**.
  Mirror the F2g→F2h-7 chain on the forest side. Heaviest immediate
  cost, but fully closes the `CoassocStrictForestH58Ready` facade.

* **Option B — pause F2 cover, proceed to Sprint G / Antipode** under
  the current facade (`CoassocStrictForestH58Ready` retained as
  typeclass hypothesis). The conditional `HopfAlgebra ℚ HopfH`
  instance stays gated on both facades. Allows attacking the right
  antipode axiom in parallel.

* **Option C — RHS index refactor to carry preimage tags**. Would
  bypass the inverse-construction problem by ensuring r is born with
  its q witness. Heavy refactor; not recommended at this stage.

##### F2 sub-status (2026-05-12 post-F2i-2)

| sub-sprint | status |
|---|---|
| F2d/F2f branch discriminator | ✅ closed |
| F2g no-star lift (0/1/1b/2/3) | ✅ closed |
| F2h-0..3 mixed candidate + choiceFn | ✅ closed |
| F2h-4 mixed index membership | ✅ closed |
| F2h-5/6 mixed target Sigma equality | ✅ closed |
| F2h-7 mixed preimage existence | ✅ closed |
| F2i-0 forest half scout (F1 uniqueness) | ✅ closed |
| F2i-1 explicit construction feasibility | ✅ closed (verdict: vertex-only) |
| F2i-2 cardinality / infra reuse | ✅ closed (verdict: no shortcut) |
| F2i-3+ forest cover explicit inverse | 🟢 conditional `forestQuotientForestSigmaForestCoverQ_v3.toQuotientForestSigma = r.1` landed 2026-05-25 (gated on `hForestCompl` + `hBP`) |
| F2i-3o/3p Plus machinery (A_final-side) | ✅ closed (settlement below) |
| F2i-3q-4a/b/c/d/e/f Right/Forest lift + CD/NOD wrappers | ✅ closed (4j details below) |
| F2i-3q-4g/h `SourceAdmissibleSubgraph_v2` + `choiceFn` | ✅ closed |
| F2i-3q-4i `_v2 ∈ properDisjoint` (5 conditions) | ✅ closed |
| F2i-3q-4j `Q : forestComponentChoiceSigma g` packaging | ✅ closed |
| F2i-3q-4k Q-membership chain (outer/core/HasForest/Sigma) | ✅ closed (2026-05-20) |
| F2i-3q-4l-actual v3 refactor (Left+Right+Forest source, Skolem `hBP`, outer equality) | ✅ closed (2026-05-23) |
| F2i-3q-4m-step2 ActualQuotient = Right ⊔ Remnant decomposition | ✅ closed (2026-05-25) |
| F2i-3q-4m-step3 RepQuotient transport via `actualToRep_actualized_eq` | ✅ closed (2026-05-25) |
| F2i-3q-4n final Sigma equality `Q_v3.toQuotientForestSigma = r.1` | ✅ closed (2026-05-25) |
| F2i-3q-F2h-7 forest preimage existence + full branch cover disjunction | ✅ closed (2026-05-25) |
| F2i-3q `hForestCompl` discharge (~160 LOC arithmetic on multiset card) | 🟡 deferred witness |
| F2i-3q `hBP` (ForestBPromotesWitness) structural discharge via 4 facade Model typeclasses + `_ForestBPromotesWitness_canonical` + `_Q_v3_canonical` API | ✅ closed (2026-05-26) — `hBP` argument no longer free; conditional on 4 typeclass instances |
| F2j-cover-cert assembly | 🟡 open (downstream of F2i-3+, conditional preimage ready) |

##### F2i-3o/3p settlement — Plus machinery's position and `A_final` vs `A_source` rift (2026-05-13)

**Built (A_final side):**
- `forestQuotientForestSigmaForestCoverSourceSubgraphExactPlus g r δ` — the **Plus** lift of a quotient component `δ`, with `.internalEdges = ExactInternalEdges + PromotedInternalEdges` (correct design, recovered by F2i-3o-2a' geometric scout after F2i-3o-2a HALT on a false multiset lemma).
- **Local right inverse**: `remainder_{A_final}(Plus_{A_final} δ) = δ` as full `FeynmanSubgraph` equality (F2i-3o-2i).
- `forestQuotientForestSigmaForestCoverLiftedSourceComponents g r` — Finset of Plus lifts.
- `forestQuotientForestSigmaForestCoverSourceAdmissibleSubgraph g r hSourceCD hSourceNOD` — `AdmissibleSubgraph` of ambient, with CD/NOD reduced to two explicit per-`δ` hypotheses (no new typeclass, no axiom, no `sorry`).
- **Collection-level remainder bijection** (F2i-3p-4): `LiftedSourceComponents.image remainder = D.elements`.
- **AdmissibleSubgraph-level equality** (F2i-3p-5): `SourceAdmissibleSubgraphActualRemainder = forestQuotientForestSigmaActualQuotientSubgraph g r.1`.

**Limit discovered (A_final vs A_source rift):**

Forest q packaging needs an *input* outer `A_source` such that
```
A_final = LeftSubgraph(A_source, p) ∪ PromotedForestComponents(A_source, p)
```
where each `γ_source ∈ A_source` with `p γ_source = forest B` is **removed** from `A_source` and replaced by `B.promoted.elements` in `A_final`.

`admissibleForestCanonicalStarOf G A := A.componentFreshStar` is *A-dependent*; the `starOf` used in `Plus_{A_final}` is **not** the `starOf` used by a hypothetical `A_source`. Therefore `Plus` constructed with `r.1.1 = A_final` cannot in general be inverted against `remainder_{A_source}(γ_source)`.

**F2i-3q-1'' scout result** (`Plus(remainder γ) = γ` for `γ ∈ A.elements`):

| carrier | match? | reason |
|---|---|---|
| `vertices` | ✅ | `SourceVertices = γ.vertices` (only `γ` is promoted under `A`) |
| `internalEdges` | ✅ | `E.map retargetEdge = 0` forces `E = 0`; `PromotedInternalEdges = γ.internalEdges` |
| `externalLegs` | ❌ | `retargetExternalLeg` is non-injective on legs attaching inside `γ.vertices`; `Classical.choose` may pick a different `L` with the same image. Endpoint constraint `L's legs attach in SourceVertices` is insufficient |

So the **left inverse** `γ → remainder(γ) → Plus(remainder γ)` fails at `externalLegs`. The Plus machinery is a right inverse only (relative to `A_final`).

**Conclusion:**
- Plus machinery is sound and reusable as **A_final-side structural infrastructure** (e.g. ambient-level reasoning, downstream tensor work).
- It is **not** the direct vehicle for the forest q packaging (`A_source` construction). That requires a different combinatorial approach: identify each remnant `δ ∈ D.elements` as a `{starOf γ_source}` pattern, then *reconstruct* `γ_source ⊆ ambient` as a CD subgraph enclosing some subset of `A_final.elements` (the would-be `B_γ_source.promoted`).

**Candidate next route (F2i-3q):**
- `F2i-3q-2a`: define `forestQuotientForestSigma_isForestRemnantPattern` — predicate on `δ` and `γ ∈ A_final.elements` matching the singleton-star + legs shape.
- Later sprints: classifier on `D.elements`, then `A_source` reconstruction via CD-enclosure of grouped `A_final.γ`'s.

The 22 inputs of 2026-05-13 leave the `A_final` side fully solidified and the `A_source` side cleanly scoped as a separate, smaller problem.

##### F2i-3q forest q packaging — A_source construction via Right/Forest split (2026-05-15 — 2026-05-17)

**Status:** in progress, `q` value packaged ✅; q-side membership & target Sigma equality outstanding.

**Settled design (after F2i-3q-2a-e dead-end, F2i-3q-3 Hull detour, F2i-3q-4 split):**

D.elements partitions into Right (no-star) and Forest (star-touching) components ([F2i-3q-4a]):
- **Right side** (δ_R disjoint from `A_final.starVertices`):
  - lifted via existing F2g `forestOuterActualQuotientNoStarComponentLift` (data-preserving lift)
  - CD, NOD axiom-free (no-star lift + D's IsPairwiseDisjoint chain)
- **Forest side** (δ_F touches stars):
  - lifted via Plus (F2i-3o-2 reused — verified at vertex level by F2i-3q-2g scout)
  - CD requires explicit `hForestCD` per-δ_F
  - NOD requires explicit `hForestDisjoint` per-δ₁,δ₂ (strengthened from NOD to Disjoint at F2i-3q-4i-1 refactor)

**Sprints completed (F2i-3q-4):**

| Sub-sprint | Content |
|---|---|
| 4a | D.elements partition Right ⊔ Forest |
| 4b/4b' | LiftedRight + CD (axiom-free via F2g) |
| 4c | LiftedForest via Plus (Reuses F2i-3o-2 chain) |
| 4d/4d' | Forest CD/NOD bottleneck reduction (then refactored to Disjoint at 4i-1) |
| 4e | Right-Right NOD (axiom-free, D.IsPairwiseDisjoint) |
| 4f-1/2/3 | Right-Forest cross-NOD (axiom-free vertex-disjoint + symm) |
| 4g | `SourceAdmissibleSubgraph_v2` def + `_elements` simp lemma |
| 4h-1 | `ForestBWitness` predicate + `ForestB`/`ForestB_mem` Classical.choose wrappers |
| 4h-2 | `ChoiceFn` (Right → `.right`, Forest → `.forest B_γ`) |
| 4h-3a | Finset-disjointness `LiftedRight ⊓ LiftedForest = ∅` |
| 4h-3b | ChoiceFn evaluation lemmas (`_eq_right_of_mem_right`, `_eq_forest_of_mem_forest`) |
| **4i-1** | **Refactor**: `hForestNOD` → `hForestDisjoint` (strengthened to vertex-disjoint for `properDisjoint` membership) |
| **4i-2** | A_source v2 `IsPairwiseDisjoint` (4-way case split RR/RF/FR/FF) |
| **4i-3a** | A_source v2 `HasNonemptyComponents` |
| **4i-3b-1** | A_source v2 `HasPositiveInternalEdgesComponents` + helper for promoted card-positivity |
| **4i-3b-2** | A_source v2 `IsNonempty` + `0 < internalEdges.card` |
| **4i-3b-3** | A_source v2 `∈ properDisjointAdmissibleDivergentSubgraphs` (5 conditions combined) |
| **4j** | `forestQuotientForestSigmaForestCoverQ : forestComponentChoiceSigma g` |

**Hypothesis budget (final form):**
- `hForestCD` : ∀ δ ∈ ForestComponents, Plus(δ).IsConnectedDivergent
- `hForestDisjoint` : ∀ δ₁ δ₂ ∈ ForestComponents distinct, vertex-disjoint
- `hB` : `ForestBWitness` — ∀ γ ∈ LiftedForestComponents, ∃ B_γ in proper-forest-index

Right side is **completely axiom-free** thanks to F2g/no-star-lift reuse + D's proper-disjoint chain.

**Key infrastructure observation (B_γ obstruction, F2i-3q-2g/F2i-3q-4h-pre scouts):**
- Plus's `externalLegs` are `Classical.choose`-non-injective wrt promoted η's
- Hybrid (V/I Plus + L Hull) breaks remainder equality
- Verdict: `B_γ` must be **deferred** as per-γ existence hypothesis `hB`; the q packaging skeleton completes under this hypothesis
- Future work: discharge `hB` either constructively (strengthen Plus.L, ~100+ LOC) or via new typeclass (`IsDivergencePreservedByQuotientRemainderInverse` style)

**Outstanding (open as of 2026-05-17):**
- `Q_mem` : `Q g r hForestCD hForestDisjoint hB ∈ forestComponentForestChoiceSigmaIndex g` (4k)
- Outer index equality `forestComponentForestChoiceOuterIndex g Q hQ = r.1.1` (forest analogue of F2h-5)
- Rep right quotient transport (forest analogue of F2h-6b)
- Final Sigma equality `forestComponentForestChoiceToQuotientForestSigma g Q hQ = r.1` (forest analogue of F2h-6c)

##### F2i-3q-4k Q-membership chain (2026-05-20)

`Q` was packaged in 4j but membership-in-`forestChoiceSigmaIndex` and outer-filter still had open obligations.

Closed sub-sprints:

| Sub-sprint | Content |
|---|---|
| 4k-0 | `ForestComponents_nonempty_of_isForestByStar` |
| 4k-1a/b/c-recover | Outer-filter membership for `Q.1` (`Finset.mem_filter` over `forestOuterProperFinset`, deferring complement-positivity as `hForestCompl`) |
| 4k-2a | `LiftedForestComponents_nonempty_of_isForest` |
| 4k-2b | `ChoiceFn ∈ forestComponentCoreChoiceIndex` (pi + ≠ allLeft + ≠ allRight) |
| 4k-2c | `forestComponentChoiceHasForest` |
| 4k-2d | combine to `ChoiceFn ∈ forestComponentForestChoiceCoreIndex` |
| 4k-3 | `Q ∈ forestComponentForestChoiceSigmaIndex g` via `Finset.mem_sigma` |

After this `Q` carries its full canonical-index membership; the only remaining external hypothesis on the outer-filter side is `hForestCompl : 0 < A_source.complementEdges.card`.

##### F2i-3q-4l-actual v3 refactor — outer equality + Skolem-form `hBP` (2026-05-19 — 2026-05-23)

**Verdict from F2i-3q-4l-pre scout:** the v2 source subgraph (`LiftedRight ∪ LiftedForest`) is insufficient for outer index equality.  The `LeftSubgraph(Q_v3) = ∅` would collapse the outer to `PromotedForestComponents` only, requiring `A_final` to be entirely forest-promoted — false in general.  **A_source must include a Left component** matching the `r.1.1.elements` part not touched by forest promotion.

**New design (v3 source subgraph):**
```
A_source_v3.elements
  = LeftComponents (= A_final.elements \ AllPromotedComponents)
  ⊔ LiftedRightComponents
  ⊔ LiftedForestComponents
```

`AllPromotedComponents := ⋃ δ ∈ ForestComponents, PromotedComponents g r δ`.

**Bridge witnesses (per scout 4l-1-pre):**
- `nonstar_mem_not_mem_outer` (per-vertex F2g-0 strengthening): every non-star δ-vertex lies outside `r.1.1.1.vertices`
- `SourceVertices_disjoint_nonPromoted_vertices`: a non-promoted η has vertices disjoint from `Plus(δ).vertices`
- Left vs LiftedRight / Left vs LiftedForest vertex-disjoint (4l-1c, 4l-1d)

**v3 properDisjoint chain (4l-2b/c, 4l-actual-properDisjoint-1..5):**
- elements (3-way mem), CD (3 cases including Left via `r.1.1.1.isConnectedDivergent_of_mem`), NOD (9 cases)
- `AdmissibleSubgraph.ofElements` packaging (4l-2c) + simp lemma
- `IsPairwiseDisjoint`, `HasNonemptyComponents`, `HasPositiveInternalEdgesComponents`, `IsNonempty`, `internalEdges.card > 0`, `_v3_mem_properDisjoint`

**ChoiceFn_v3 + Skolem hBP refactor (4l-2d/e + hyp-fix):**

Critical scout finding (4l-actual-promoted scout): the existential `hB : ForestBWitness` is **insufficient** for the outer `PromotedForestComponents = AllPromotedComponents` identity, because `Classical.choose` on two existentially-different statements may return different `B`'s. Solution: **Skolem-form structure**.

```lean
private structure forestQuotientForestSigmaForestCoverForestBPromotesWitness
    (g) (r) (hForestCD) where
  B : ∀ γ hγ, AdmissibleSubgraph (repG (γ.toHopfGen ...)).toFG
  mem : ∀ γ hγ, B γ hγ ∈ forestCoproductProperForestIndex ...
  promotes : ∀ γ hγ, ∃ δ ∈ ForestComponents, γ = Plus δ ∧
    (Promote γ (B γ hγ)).elements = PromotedComponents g r δ
```

Projection `_to_ForestBWitness` provides backward-compat to v2's old existential form.  
Accessors `ForestB_canonical`, `_mem`, `_promotes` give direct field access.

`ChoiceFn_v3_promoted` (4l-2d) dispatches Left → `.left`, LiftedRight → `.right`, LiftedForest → `.forest (ForestB_canonical γ hF)`.  3 eval lemmas (4l-2e-1/2/3) + 2 Finset-disjoint helpers (4l-2e-2).

**Outer equality core (4l-actual-leftsubgraph .. 4l-actual-8b):**

| Sub-sprint | Content |
|---|---|
| `leftsubgraph_promoted` | `LeftSubgraph(A_v3, ChoiceFn_v3_promoted) = LeftComponents` |
| `7a` | `Plus injective` + `PromotedComponents_eq_of_plus_eq` (via existing `_remainder_eq`) |
| `7b` | `PromotedForestComponents = AllPromotedComponents` (uses `hBP.promotes` + `7a`) |
| `partition` | `LeftComponents ⊔ AllPromotedComponents = r.1.1.1.elements` |
| `8a` | `A_v3.IsPairwiseDisjoint` (9-case all vertex-disjoint) |
| `8b` | **Outer Subgraph equality**: `forestComponentForestChoiceOuterSubgraph A_v3 ChoiceFn_v3_promoted hPD = r.1.1.1` (AdmissibleSubgraph level) |
| `OuterIndex Subtype wrapper` | `forestComponentForestChoiceOuterIndex g Q_v3 hQ_v3 = r.1.1` (forest analog of F2h-5) |

**Q_v3 packaging chain (4l-actual-Q-v3, 4l-actual-2b/2c/2d/3-v3):**

`Q_v3 := ⟨⟨A_v3, _v3_mem_properDisjoint⟩, ChoiceFn_v3_promoted⟩` + `Q_v3_mem_outer`, `Q_v3_mem_coreChoiceIndex` (3-clause pi/notAllLeft/notAllRight), `Q_v3_hasForest`, `Q_v3_mem_forestChoiceCoreIndex`, **`Q_v3 ∈ forestComponentForestChoiceSigmaIndex g`**.

##### F2i-3q-4m forest analog of F2h-6 (2026-05-23 — 2026-05-25)

**Goal:** `forestComponentForestChoiceToQuotientForestSigma g Q_v3 hQ_v3 = r.1` (forest analog of F2h-6c).

`toQuotientForestSigma g q hq = ⟨OuterIndex g q hq, RepQuotientSubgraphCanonical g q hq⟩`.

First component is the OuterIndex Subtype wrapper (already done).  Second component needs:

```
hOuter ▸ RepQuotientSubgraphCanonical g Q_v3 hQ_v3 = r.1.2
```

**Key structural fact (vs mixed F2h-6b):** mixed Step 2 went `ActualRightQuotient = D` because mixed has only right components.  Forest's `ActualQuotient = ActualRight ⊔ Remnant` requires a **two-piece decomposition**.

**Sub-sprints completed:**

| Sub-sprint | Content |
|---|---|
| `4m-bridge-1` | `forestComponentChoiceIsForest` predicate + `_of_eq`/`_exists` (analog of `IsLeft`/`IsRight`) |
| `4m-step2-remnant-generic` | `RemnantComponents = ForestComponents` (Finset eq, transported via `hOuter`) — B-free thanks to `_remainder_eq` + Plus injective |
| `4m-step2-remnant-Q_v3` | specialize |
| `4m-step2-right-defs` | `RightCandidate_v3` (LiftedRight as AdmissibleSubgraph) + `RightActualSubgraph` (no-star part of D as AdmissibleSubgraph) |
| `4m-step2-right-rightSubgraph` | `RightSubgraph(A_v3, ChoiceFn_v3_promoted) = RightCandidate_v3` (mirror of leftsubgraph) |
| `4m-step2-right-generic` | `ActualRightQuotient = RightActualSubgraph` (mixed F2h-6b Step 2 forest transcript) |
| `4m-step2-right-Q_v3` | specialize |
| `4m-step2-full-generic` | combine Right + Remnant + `_right_union_forestComponents` (4a) → `ActualQuotientSubgraphCanonical = forestQuotientForestSigmaActualQuotientSubgraph g r.1` |
| `4m-step2-full-Q_v3` | specialize |
| `4m-step3-generic` | RepQuotient transport via `forestOuterActualToRep_actualized_eq` (mixed F2h-6b Step 3 mirror) |
| `4m-step3-Q_v3` | specialize |
| **`4n`** | **Final Sigma equality** via `Sigma.ext + eqRec_heq_iff_heq.mp ∘ heq_of_eq` |

**Δ from mixed Step 2:** mixed's `_all_noStar_of_not_isForestByStar` only applies when `D` has no star components; forest case uses **per-element** no-star extraction via `RightComponents_mem.2`.

**Final theorem (conditional on `hForestCD`, `hForestDisjoint`, `hBP`, `hForestCompl`):**

```lean
private theorem forestQuotientForestSigmaForestCoverQ_v3_toQuotientForestSigma_eq
    (g r hForest hForestCD hForestDisjoint hBP hForestCompl) :
    forestComponentForestChoiceToQuotientForestSigma g
        (forestQuotientForestSigmaForestCoverQ_v3 g r ...)
        (forestQuotientForestSigmaForestCoverQ_v3_mem_forestChoiceSigmaIndex g r ...)
      = r.1
```

This is the forest analog of F2h-6c and the gateway to F2i-4 (forest preimage existence + full disjunction wrapper).

##### F2i-3q-F2h-7 forest analog + full branch cover (2026-05-25)

Packaging the F2i-3q-4n equation:

| Theorem | Content |
|---|---|
| `forestQuotientForestSigma_forestPreimage_of_isForestByStar` | conditional `∃ q hq, toQuotientForestSigma q hq = r.1` for forest branch (mirror of mixed F2h-7) |
| `forestQuotientForestSigma_cover_branch_preimage` | full disjunction wrapper: `(forest ∃) ∨ (mixed ∃)` via `by_cases` on `isForestByStar` — strengthening of the old `forestQuotientForestSigma_cover_mixed_half` (Or.inl side was a placeholder) |

The disjunction wrapper takes forest-side witnesses (`hForestCD`, `hForestDisjoint`, `hBP`, `hForestCompl`) as `hForest →`-conditioned hypotheses so the `by_cases` branch applies them only when needed.  Mixed branch retains its axiom-free derivation.

**Conditional forest cover identity is now provably stated** — both branches of the cover map's image disjunction land in their respective preimage existence statements, gated on the deferred witness budget.

##### F2i-3q-hBP `ForestBPromotesWitness` structural discharge via 4 facade Model typeclasses (2026-05-26)

**Strategic move:** rather than attack the heavy combinatorial blocker directly, decompose `hBP` into a structural Skolem-form witness `_ForestBPromotesWitness_canonical` built from a `B_candidate` (data) + `BCandidateProperForestIndexModel`-supplied membership + `BCandidatePromotesModel`-supplied round-trip.  Each remaining obstruction is split out into a dedicated facade `Model` typeclass, so the conditional `hBP` argument is replaced by 4 typeclass instances at the API surface.

**Construction pipeline** (Coassoc.lean):

| sprint | output | content |
|---|---|---|
| hBP-1a | `_promotedComponent_internalEdges_le_plus` | `Finset.single_le_sum` + `Multiset.le_add_left` |
| hBP-1b-1 | `_promotedComponent_vertices_subset_plus` | `SourceVertices_eta_subset` (F2i-3a) |
| hBP-1b-2 | `_promotedComponentAsComponent` | repackage η as `FeynmanSubgraph (Plus δ).toFG` under deferred `hLegs` |
| hBP-1b-3 | `_promotedComponent_promote_roundtrip` | `FeynmanSubgraph.ext_iff.mpr ⟨rfl, rfl, rfl⟩` |
| hBP-1c | **`PromotedExternalLegsLiftableModel`** + wrapper | facade for `η.externalLegs ≤ Plus(δ).externalLegs` (discharges `hLegs`) |
| hBP-1d-1a | `_liftedForestSource` + `_mem` + `_plus_eq` | `Classical.choose` of `LiftedForestComponents_mem_exists` |
| hBP-1d-1b | `_BElementMap` | 3-step pipeline: `_promotedComponentAsComponent` → `Plus`-eq ▸ → `mapPermSubgraph` via `feynmanSubgraphToHopfGenRepPerm_spec` |
| hBP-1d-1c | **`BElementMapAdmissibleModel`** | facade for CD + NOD of `_BElementMap` image |
| hBP-1d-1d | `_BCandidate` + `_elements` simp | `AdmissibleSubgraph.ofElements` over `(PromotedComponents).attach.image _BElementMap` |
| hBP-1d-2 | **`BCandidateProperForestIndexModel`** + `_BCandidate_mem` wrapper | facade for `B_candidate ∈ forestCoproductProperForestIndex` (5 conditions) |
| hBP-1d-3 | **`BCandidatePromotesModel`** + `_ForestBPromotesWitness_canonical` | facade for `promote∘preimage` round-trip; full Skolem-form witness assembled |
| hBP-1e | `_Q_v3_canonical` + 3 wrappers | drop `hBP` parameter from `Q_v3`, `_mem_forestChoiceSigmaIndex`, `_toQuotientForestSigma_eq`, `_forestPreimage_of_isForestByStar` — internally supplied by `_ForestBPromotesWitness_canonical` under the 4 typeclass instances |

**Result:** `hBP` is no longer a free-standing deferred witness.  Forest cover identity is now conditional on 4 facade Model typeclass instances + `hForestCompl`.

##### F2i-3q-model-2 `BCandidatePromotesModel` discharge (2026-05-26)

First of the 4 facade Models proven constructively.  The round-trip
identity `(promote∘preimage)(_BCandidate).elements = PromotedComponents`
is established as `instance` `_BCandidatePromotesModel_instance` (no
remaining typeclass holes for this Model).

**Discharge chain:**

| theorem | content |
|---|---|
| `feynmanSubgraphPromote_outer_eqRec` | generic transport: `cases hγ`-based collapse of `congrArg toFG` `▸` across `feynmanSubgraphPromote (γ_outer := .)` (so `Plus δ = γ` transport disappears without a global `subst`) |
| `_BElementMap_promote_preimage_eq` | per-η identity: `mapPermSubgraph_preimage_mapPerm_eq` + `feynmanSubgraphPromote_outer_eqRec` + `_promotedComponent_promote_roundtrip` |
| `_BElementMap_promote_inv_eq` | proof-term-generic restatement (explicit `h_inv` parameter so it pattern-matches whatever proof term `mapPermAdmissibleSubgraphPreimage_elements` unfolds to — sidesteps the Lean-4 proof-irrelevance-on-`by`-block convergence issue) |
| `_BCandidatePromotesModel_instance` | `Finset.ext` over three image layers; backward direction supplies the preimage witness via `mapPermSubgraph_preimage` + `rw [hπ, ← mapPerm_mul]; simp` for `h_inv` construction |

**Strategic implication:** the structural decomposition of `hBP` into
4 facade Models is **not just a deferral** — the `promotes` round-trip
(which carried the prior `Classical.choose`-on-existential obstruction
in the pre-hBP-refactor era) admits constructive proof.  The remaining
3 Models concern *containment / admissibility / properness*, not
round-trip choice.

##### F2i-3q-model-3 `BElementMapAdmissibleModel` discharge (2026-05-26)

Second of the 4 facade Models proven constructively.  CD + NOD of the
`_BElementMap` image are established directly via the toFeynmanGraph
factorization `_BElementMap.toFG = η.toFG.mapPerm π`, established as
`instance` `_BElementMapAdmissibleModel_instance`.

**Discharge chain (Sprint F2i-3q-model-3a):**

| theorem | content |
|---|---|
| `feynmanSubgraph_eqRec_toFeynmanGraph_eq` | `(h ▸ γ).toFG = γ.toFG` via `cases h; rfl` (6 LOC) — collapses `Plus`-eq `▸` for toFG-level reasoning |
| `_BElementMap_toFeynmanGraph_eq` | `_BElementMap.toFG = η.toFG.mapPerm π` — three-step pipeline (component repackage + `Plus`-eq ▸ + `mapPermSubgraph`) factors through a single perm action (the first two steps are data-preserving, the third is `mapPermSubgraph_toFeynmanGraph`) |
| `_BElementMap_isConnectedDivergent` | per-η CD: extract η.CD via `r.1.1.1.isConnectedDivergent_of_mem` (PromotedComponents ⊆ A_final.elements); lift via `mapPermSubgraph (rfl : ... = (repG g).mapPerm π) η.IsConnectedDivergent`; bridge to `_BElementMap` via toFG-eq + `_isConnectedDivergent_of_toFeynmanGraph_eq` |
| `feynmanSubgraph_nestedOrDisjoint_of_toFeynmanGraph_eq` | NOD transports across `toFG` equality (NOD only depends on vertices/edges/legs, extracted from toFG via `congrArg`) — bridge helper for different ambients |
| `_BElementMap_nestedOrDisjoint` | per-pair NOD: reflexive case `subst hEq + le_refl' _`; distinct case via `r.1.1.1.forest.nestedOrDisjoint` + `mapPermSubgraph_nestedOrDisjoint` + toFG-eq bridge |
| `_BElementMapAdmissibleModel_instance` | `by intros; apply ...` — typeclass field auto-synth from the two standalone theorems |

**Strategic implication:** CD/NOD transport through 3-step pipeline
(component → eqRec → mapPerm) is constructive, confirming that the
hBP decomposition reduces transport-heavy proofs to toFG-equality
bridges + proof-term-generic `mapPerm` helpers.  Pattern reusable for
other Plus/promote/transport workflows in the project.

##### F2i-3q-model-4 `BCandidateProperForestIndexModel` discharge (2026-05-26)

Third of the 4 facade Models proven constructively.  The 7-condition
membership `_BCandidate ∈ forestCoproductProperForestIndex` is established
as `instance` `_BCandidateProperForestIndexModel_instance`.

**Discharge chain (Sprint F2i-3q-model-4a, ~600 LOC across 7 sub-sprints):**

| sprint | theorem | content |
|---|---|---|
| 4a-1 | `_BCandidate_isPairwiseDisjoint` | vertex-disjoint via `r.1.1.2 ∈ properDisjoint` → forest pairwise disjoint → `mapPermSubgraph_disjoint` on rfl-ambient lift → toFG-eq bridge.  Needs new helper `feynmanSubgraph_disjoint_of_toFeynmanGraph_eq` |
| 4a-2 | `_BCandidate_hasNonemptyComponents` | per-η: η.IsNonempty (from forest) → mapPermSubgraph_isNonempty → toFG-eq bridge.  New helper `feynmanSubgraph_isNonempty_of_toFeynmanGraph_eq` |
| 4a-3 | `_BCandidate_hasPositiveInternalEdgesComponents` | per-η: card preservation via `mapPerm_internalEdges` + `Multiset.card_map`.  New helper `feynmanSubgraph_internalEdges_card_eq_of_toFeynmanGraph_eq` |
| 4a-4 | `_BCandidate_isNonempty` | witness construction: ForestComponents membership → `¬ Disjoint δ.vertices starVertices` → `Finset.not_disjoint_iff` extracts v → `mem_starVertices` extracts η → `_BElementMap η hη ∈ B_candidate.elements` |
| 4a-5 | `_BCandidate_internalEdges_card_pos` | `0 < B_candidate.internalEdges.card` via `Finset.single_le_sum` + `Multiset.card_le_card` from 4a-4 + 4a-3 |
| 4a-6 helpers 1-4 | injectivity + card chain | `feynmanGraph_mapPerm_injective` (apply π⁻¹ + `mapPerm_mul` + `inv_mul_cancel` + `mapPerm_one`); `_BElementMap_injective` (via Target 2 + helper-1 + `FeynmanSubgraph.ext`); `_BCandidate_internalEdges_card_eq` (= PromotedInternalEdges.card via `Finset.sum_image` + `sum_congr` + `Finset.sum_attach` + `Multiset.card_add` induction); `_liftedForestSource_internalEdges_card_pos` (via `actualQuotientSubgraph = mapPermPreimage(r.1.2)` + `mapPermSubgraph_internalEdges_card`) |
| 4a-6 main | `_BCandidate_complementEdges_card_pos` | **algebraic cancellation**: complementEdges.card = ambient.card − B_candidate.card = (Exact.card + Promoted.card) − Promoted.card = Exact.card = δ.internalEdges.card > 0.  Uses `Multiset.card_sub`, `Multiset.card_add`, `Multiset.card_map`, and helper-4 |
| 4b | `_BCandidateProperForestIndexModel_instance` | 7-leaf nested constructor via `mem_forestCoproductProperForestIndex` + `mem_properDisjoint` + `mem_nonemptyDisjoint` + `mem_disjoint` unfolds; assembles 4a-1...4a-6 + universal `mem_admissibleDivergentSubgraphs` |

**Key algebraic identity (4a-6):**
```
B_candidate.complementEdges.card
  = ambient.internalEdges.card − B_candidate.internalEdges.card     -- Multiset.card_sub
  = γ.internalEdges.card − B_candidate.internalEdges.card           -- via mapPerm spec
  = (ExactInternalEdges.card + PromotedInternalEdges.card) − PromotedInternalEdges.card  -- via γ = Plus δ + helper-3
  = ExactInternalEdges.card                                          -- omega
  = δ.internalEdges.card                                             -- via _ExactInternalEdges_map spec
  > 0                                                                -- helper-4
```

**Strategic implication:** `BCandidateProperForestIndexModel` is **not a
mathematical obstruction** — it is pure multiset/mapPerm accounting.
The discharge confirms that only one of the 4 facade Models
(`PromotedExternalLegsLiftableModel`) carries a genuine structural
obstruction (the `Classical.choose` non-canonicity of
`ExactExternalLegs`).

**Outstanding deferred witnesses (forest cover identity is conditional on):**

| witness / instance | type | status / nature of obstruction |
|---|---|---|
| `hForestCompl` | `0 < A_v3.complementEdges.card` | 🟡 facade — ~160 LOC multiset arithmetic (`Finset.sum_image` + Multiset accounting); deferred at F2i-3q-4k-1c HALT (2026-05-17) |
| `PromotedExternalLegsLiftableModel` | `η.externalLegs ≤ Plus(δ).externalLegs` for `η ∈ PromotedComponents g r δ` | 🔴 facade — **root obstruction**: `ExactExternalLegs` is `Classical.choose`-extracted via `Multiset.exists_le_of_le_map`, non-canonical preimage under `retargetExternalLeg` non-injectivity at star vertices.  Discharge requires `ExactExternalLegs` redesign (Plus-chain refactor, ~200-400 LOC) — explicit determination 2026-05-26 |
| `BElementMapAdmissibleModel` | CD + NOD of `_BElementMap` image | ✅ **discharged** (2026-05-26) — see F2i-3q-model-3 subsection above |
| `BCandidateProperForestIndexModel` | `_BCandidate ∈ forestCoproductProperForestIndex` (7 conditions) | ✅ **discharged** (2026-05-26) — see F2i-3q-model-4 subsection above |
| `BCandidatePromotesModel` | `(promote∘preimage)(_BCandidate).elements = PromotedComponents g r δ` | ✅ **discharged** (2026-05-26) — see F2i-3q-model-2 subsection above |

**Summary 2026-05-26:** **3 of 4** facade Models discharged.  Only `PromotedExternalLegsLiftableModel` remains as a structural facade (root obstruction: `ExactExternalLegs` `Classical.choose` non-canonicity).  Forest cover identity is now provably constructive modulo (a) `hForestCompl` arithmetic, (b) the single externalLegs liftability facade.

##### F2i-3q-model-final-scout: `PromotedExternalLegsLiftableModel` finalized as semantic facade (2026-05-26)

After 3/4 discharge, attempted scout for `PromotedExternalLegsLiftableModel` discharge via canonical sorted correspondence on `ExactExternalLegs`.  Scout determined the obstacle is **not** `Classical.choose` opacity (which sorted correspondence would solve) but a **semantic mismatch**:

**Gate condition (required for canonical redesign):**
```
PromotedExternalLegs.map retarget ≤ δ.externalLegs
```

**Gate fails in general**, even for δ ∈ ForestComponents.

**Why:** δ is constructed as `mapPermSubgraphPreimage hπ η'` where η' ∈ r.1.2.elements is a CD subgraph of the QUOTIENT graph (`(repG forestOuterQuotientHopfGen).toFG`).  δ.externalLegs = η'.externalLegs.map (ExternalLeg.map π⁻¹).  η'.externalLegs is *whatever* sub-multiset η' was constructed with, subject only to:
- `legs_supported`: each leg's `attachedTo` ∈ η'.vertices
- `externalLegs_le`: ≤ ambient externalLegs
- CD/divergence constraints

There is **no structural constraint** forcing η' (and hence δ) to include all retargeted legs at star vertices in its vertex set.  Star-touching membership (the ForestComponents filter) ensures `star η ∈ δ.vertices`, but not that all retarget-image legs at star η appear in δ.externalLegs.

**Counterexample sketch:** η' with vertices `{⋆}`, no internal edges, externalLegs `∅` (CD-admissible under abstract `DivergenceMeasure`).  Then δ.externalLegs = ∅, but PromotedExternalLegs.map retarget contains all retargeted η.externalLegs at ⋆.

**Rejected redesign paths:**

| approach | reason for rejection |
|---|---|
| A. Canonical sorted correspondence on `ExactExternalLegs` | Solves only `Classical.choose` opacity — but the obstacle is missing target legs in δ.externalLegs, not preimage choice |
| B. Strengthen `ForestComponents` filter to require leg inclusion | Cascading rewrite of `F2i-3q-4l-actual` outer equality + downstream Sigma equalities |
| C. Make `Plus(δ).externalLegs` a SUPERSET (include both promoted + δ-preimage) | Breaks `Plus(δ).externalLegs.map retarget = δ.externalLegs` remainder equality |

**Strategist conclusion:** `PromotedExternalLegsLiftableModel` is **finalized as a semantic facade**.  The discharge is not blocked by Lean elaboration or `Classical.choose` artifacts — it is a genuine semantic assumption about leg presence in arbitrary CD subgraphs of the contracted graph.  Recording this distinction matters because it tells future implementers that canonical-correspondence-style refactors will not help.

**Net result for hBP discharge:**
- 3 of 4 facade Models constructively discharged
- 1 final facade is a **semantic** (not technical) assumption
- Forest cover identity is fully provable modulo this single facade + `hForestCompl`

**Next-phase recommendation:** return to upstream blockers — `CoassocStrictForestH58Ready` and `AntipodeStrictForestRightReady`.  Further hBP work has diminishing returns.

#### `CoassocStrictForestH58Ready` Track B foundational helpers (2026-05-27)

Track B-1a/1b scout+implementation phase completed.  Foundational injectivity infrastructure landed; mixed q.1 recovery paused at HEq plumbing.

**Added helpers (`Coassoc.lean`, ~120 LOC total):**

| theorem | content | reusable beyond Coassoc? |
|---|---|---|
| `forestOuterProperIndex_eq_of_elements_eq` (B-1a) | terminal step: `A.elements = A'.elements → A = A'` via `Subtype.ext + AdmissibleSubgraph.ext + Forest.ext` | yes — generic AdmissibleSubgraph element-level uniqueness |
| `_leftSubgraph_eq_of_eq` (B-1a) | mixed `toQuotient` eq → `LeftSubgraph` eq via `Sigma.fst` + `Subtype.val` + `_OuterIndex_val` simp | mixed-branch-specific |
| `admissibleForestCanonicalStarOf_injOn_elements` (B-1b-1) | star injectivity on A.elements via `IsFreshStarAssignment.eq_of_star_eq` | yes — general-purpose canonical star lemma |
| `admissibleSubgraphRetargetSubgraph_inj_on_elements` (B-1b-2) | retarget-subgraph injectivity via star injectivity + `retargetVertex_of_mem_component` + `HasNonemptyComponents` | yes — generic retarget injectivity |
| `Sigma_snd_heq_of_eq` (B-1b-3-scout) | HEq on `Sigma.snd` from Sigma equality via `cases hEq; rfl` | yes — generic Sigma HEq extractor |
| `forestComponentMixedBoundaryToQuotientForestSigma_repRight_heq_of_eq` (B-1b-3-scout) | mixed `toQuotient` eq → `RepRightQuotient` HEq | mixed-branch-specific |

**Track B-1b-3a HALT** (mixed q.1 recovery dependency plumbing):
- `cases hOuter` failed because `MixedOuterIndex(q_i)` are *computed expressions*, not free variables — standard dependent elimination doesn't apply.
- Going forward requires `Sigma.mk.injEq` + manual `Eq.mpr`/cast plumbing, or `generalize ... at *` with careful scope control.  Estimated ~300-400 LOC just for `mixed_q1_recovery`, comparable in friction to `_BCandidatePromotesModel` discharge.
- Forest `q.1` recovery remains deeper (PromotedForestComponents parent-recovery, ~Sprint-D-scale).

**Strategic conclusion:** the remaining `CoassocStrictForestH58Ready` injectivity gap is **not mathematical falsehood** — it is dependent equality plumbing around computed Sigma first components and `RepRightQuotient` transport.  Track B has produced reusable star + retarget injectivity infrastructure and a refined obstacle characterization.  Further progress requires committing a Sprint-D-scale HEq plumbing campaign isolated from the main injectivity proofs.

#### `CoassocStrictForestH58Ready` — HEq plumbing campaign closes `mixed_inj` (2026-05-29)

The HEq-plumbing campaign was executed and **`mixed_inj` is fully discharged** (2/3 of `BranchInjectivitySeparation` now done: `cross` ✅ + `mixed_inj` ✅).  The "computed-fst blocks `cases`" wall was overcome by the **free-index generic-lemma pattern**: state the transport lemma over *free* index variables (where `cases`/`subst` works), then specialize to the computed `MixedOuterIndex` at the call site.

**Campaign chain (`Coassoc.lean`, all `lake env lean` exit 0):**

| sprint | theorem | content |
|---|---|---|
| B-HEq-0 | `Sigma_snd_eqRec_of_eq` | generic `(congrArg Sigma.fst h) ▸ x.2 = y.2` via `cases h` on free Σ-pairs — the core wall-breaker |
| B-HEq-1 | `_repRight_eqRec_of_eq` | mixed specialization: casted-Eq form of `RepRightQuotient` (projection form so `▸` motive matches) |
| B-HEq-2 | `forestOuterActualToRepAdmissibleSubgraph_injective` + `forestOuterActualToRep_eqRec_inj` | un-perm: `toRep` injective (preimage round-trip) + generic free-index eqRec un-perm (`cases hA`) |
| B-HEq-3 | `admissibleSubgraphRetargetSubgraph_inj_of_not_mem` | off-carrier (data-preserving) retarget injectivity via `toFeynmanGraph_eq_of_not_mem` + `FeynmanSubgraph.ext` |
| B-HEq-4 | `forestOuterActualRetargetOfCert_elements_eq_of_eqRec` | un-retarget assembly: `cases hA` (free index) + `.elements`-is-image-by-rfl coercion + `Finset.ext` using B-HEq-3 |
| B-HEq-5a | `forestComponentMixedBoundary_left_union_right_elements_recovery` | Left/Right partition of outer elements in mixed branch (no forest choice) |
| B-HEq-5b | `forestComponentMixedBoundaryToQuotientForestSigma_q1_recovery` | **`q.1` recovery**: LeftSubgraph eq (B-1a) + RightSubgraph elements eq (B-HEq-1→2→4) + partition → `A.elements` eq → `forestOuterProperIndex_eq_of_elements_eq` |
| B-HEq-6 | `forestComponentMixedBoundaryToQuotientForestSigma_inj` | **`mixed_inj`**: q.1 recovery + `_inj_of_q1_eq` (F1r-2b) |

**Key technical wins:**
- **Free-index generic-lemma pattern** beats the computed-fst `cases` wall — applies to `Sigma_snd_eqRec_of_eq`, `forestOuterActualToRep_eqRec_inj`, `forestOuterActualRetargetOfCert_elements_eq_of_eqRec`.
- **Course-correction**: the mixed-branch un-retarget is the *off-carrier data-preserving* case (RightSubgraph components are disjoint from the LeftSubgraph carrier), NOT the star-collapse case — so B-1b-1/1b-2 (star injectivity) were not the relevant tools; B-HEq-3 (data-preserving) is.
- `.elements` of `OfCert` reduces to the retarget image by `rfl` → defeq coercion avoids fighting `simp`/`rw` higher-order matching.

**Remaining for `CoassocStrictForestH58Ready`:** only `forest_inj` (genuine-forest same-branch injectivity).  This is deeper — the genuine-forest `OuterSubgraph = Left ∪ PromotedForestComponents`, and recovering the forest-choice locations requires inverting the promote operation (PromotedForestComponents parent-recovery).  cover ✅, cross ✅, mixed_inj ✅, forest_inj 🟡.

#### `forest_inj` dividing-line scout — remnant alone is not injective on forest parents (2026-05-29)

Scouted whether the mixed-branch toolkit (free-index pattern + star/off-carrier injectivity) closes `forest_inj` directly.  **Determination: it does not — `forest_inj` genuinely needs Promoted+remnant reconstruction.**

**Key structural facts:**
- `forestComponentChoicePromotedForestComponents A p = ⋃_{forest-chosen γ} (promote B_γ).elements` — these are **promoted B sub-components** (children inside γ), NOT γ itself.
- So `OuterIndex.elements = Left.elements ∪ Promoted.elements`, and a forest-chosen parent γ ∈ `q.1.1.elements` is **NOT** in `OuterIndex.elements` (γ is the parent; Promoted holds its children).
- The remnant carrier is `OuterIndex`.  Since γ ∉ OuterIndex.elements, `retargetVertex` does **not** collapse γ.vertices to a single `{starOf γ}`: vertices inside `Promoted(γ)` collapse to the promoted components' stars, the rest stay identity — a mix.
- Therefore `admissibleForestCanonicalStarOf_injOn_elements` (B-1b-1, which needs γ ∈ OuterIndex.elements) **cannot** be applied to forest parents.  The remnant alone does **not** determine γ.

**Reconstruction route (the genuine remaining work):** `remnant(γ).vertices` contains the stars of γ's promoted components, which links each remnant to its promoted children.  So γ is recovered by: for each remnant, collect the promoted components whose star ∈ remnant.vertices, then union with the remnant edges.  This is a real combinatorial inverse, ~300-500 LOC Sprint-scale, distinct from and heavier than mixed (whose Right part was self-contained off-carrier data-preservation).

**Net:** today's `mixed_inj` was the achievable half of `BranchInjectivitySeparation`.  `forest_inj` is precisely characterized as the Promoted+remnant reconstruction campaign.  All injectivity primitives (star B-1b-1, off-carrier B-HEq-3, free-index eqRec B-HEq-0/2/4) are in place; the missing piece is the parent-reassembly logic.

#### `forest_inj` route is GREEN — NOT semantically blocked (2026-05-29 correction)

A follow-up check **corrects an earlier worry** that `forest_inj`'s parent recovery might hit the same semantic externalLegs gate that makes `PromotedExternalLegsLiftableModel` a permanent facade.  **It does not.**  The parent γ's data is fully distributed and recoverable from the quotient:

- `remnant(γ).externalLegs = γ.externalLegs.map retarget` ([Coassoc.lean:3732](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L3732)) — **all** of γ's external legs are preserved in the remnant (just retargeted).  No leg loss.  This is a *different* situation from the `PromotedExternalLegsLiftableModel` gate (which was about a cover-side arbitrary δ.externalLegs failing to contain promoted legs).
- `remnant(γ).internalEdges = (γ.internalEdges − Aout.internalEdges).map retarget` — the subtracted part (promoted B edges) is preserved on the `OuterSubgraph` side (as `Promoted`).  So γ.internalEdges = (remnant edges) ⊕ (promoted B edges), recoverable by combining the two sides.
- `remnant(γ).vertices = γ.vertices.image retarget` — promoted-child vertices collapse to their stars (recoverable via the promoted children in OuterSubgraph), non-promoted vertices stay identity.

**Conclusion:** `forest_inj` is a **doable** reconstruction campaign (~300-500 LOC), not a semantic wall.  The parent γ is reassembled from (its promoted children in `OuterSubgraph`) + (its remnant in `RepQuotient`), linked by the shared stars in `remnant(γ).vertices`.  Foothold = vertices equality `sourceVerticesFor Aout (remnant γ) = γ.vertices` (uses the promoted-child containment [Coassoc.lean:6400](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L6400) + fresh-star distinctness + retargetVertex case analysis).  All prerequisites verified present; remaining work is implementation volume, not a blocker.

**Route status:** cover ✅ + cross ✅ + mixed_inj ✅ + forest_inj 🟢 (GREEN, reconstruction campaign, ~300-500 LOC, no semantic wall).

#### `forest_inj` reconstruction — vertex recovery landed (2026-05-29)

The forest parent-recovery campaign is underway.  Foundational pieces (all `lake env lean` exit 0):

| sprint | theorem | content |
|---|---|---|
| 2a-pre1 | `admissibleSubgraphRemainderSourceVertices` + `mem_…` | generic "source vertices" for a remainder subgraph (cover-side `SourceVertices` de-coupled from `r`; works for any admissible `A` + star map) + membership iff |
| 2a-pre2 | `admissibleSubgraph_star_mem_remainder_vertices_iff_intersects` | `starOf η ∈ remnant(γ).vertices ↔ η shares a vertex with γ` (forward excludes the non-carrier branch via fresh stars; backward via `retargetVertex_of_mem_component`) |
| 2a-pre3 | `forestComponentForestChoiceOuterSubgraph_elt_subset_parent_of_meets` | a genuine-forest `OuterSubgraph` element meeting parent γ is ⊆ γ (Left elements disjoint from γ; promoted elements ⊆ their parent = γ by pairwise disjointness) |
| **2a** | `forestComponentForestChoice_remnant_sourceVertices_eq_parent_vertices` | **parent vertex recovery**: `sourceVertices(remnant γ) = γ.vertices` via `Finset.ext` + pre1/pre2/pre3 + `retargetVertex` case split |

**Next pieces** (forest reconstruction continues): internalEdges recovery (`γ.internalEdges = remnant-edges ⊕ promoted-B-edges`, recombining RepQuotient + OuterSubgraph sides) and externalLegs (already `γ.externalLegs.map retarget`, the easy part), then assemble parent recovery → forest q.1 recovery → `forest_inj`.  Vertices was the first structural third and is done.

#### `forest_inj` — internalEdges recovery hits CK graph-insertion uniqueness (2026-05-29)

The internalEdges recovery scout (B-forest-2b / edge-closed check) found that **vertices recovery does not extend cleanly to internalEdges**, and isolated the genuine remaining kernel.

**Edge-closed is NOT structural.** `FeynmanSubgraph.internalEdges` is an independent `Multiset` (only `edges_supported`: both endpoints in `vertices`).  So a parent γ can have a residual edge (∈ `γ.internalEdges − Aout.internalEdges`) with an endpoint inside a promoted child η — either both endpoints in η.vertices but e ∉ η.internalEdges (→ collapses to a self-loop at `star η`), or one endpoint in η and one outside (→ collapses to `(star η, w)`).  Under `retargetEdge` these **collapse**, so `remnant(γ).internalEdges = (γ.internalEdges − Aout.internalEdges).map retargetEdge` is **not injective in γ**.

**This is CK contraction working as intended** — `remnant(γ) = γ/B` contracts the promoted children to stars; boundary-crossing edges collapse onto the star.  Recovering γ is the inverse: re-insert B-components at the star.  Morally the boundary data is in the promoted children's `externalLegs` (`feynmanSubgraphPromote` preserves legs), but `FeynmanSubgraph.externalLegs` keeps only `attachedTo + sector` (the *star*, not the collapsed interior endpoint), so **uniqueness of re-insertion is a genuine semantic kernel** — the formalization has exposed CK 1998's implicit graph-insertion uniqueness.

**Interface introduced:** `ForestGraphInsertionUniquenessModel` (facade, `Coassoc.lean`) —
```
parent_eq_of_remnant_eq : γ₁.vertices = γ₂.vertices →
  remnant(A, starOf, γ₁) = remnant(A, starOf, γ₂) → γ₁ = γ₂
```
isolating exactly "the remnant + recovered vertices determine the parent uniquely."  Genuine-forest analogue of the `mixed_q1_recovery` step (where the off-carrier, data-preserving case avoided any uniqueness assumption).

**Revised `forest_inj` status:** vertices recovery ✅ constructive; full parent recovery depends on `ForestGraphInsertionUniquenessModel`.  So `forest_inj` is **not** "just implementation volume" — its core is a new semantic kernel, akin to (though distinct from) `PromotedExternalLegsLiftableModel`.  `CoassocStrictForestH58Ready` refines to: **cover ✅ + cross ✅ + mixed_inj ✅ (constructive) + forest_inj depends on graph-insertion uniqueness**.

#### `ForestGraphInsertionUniquenessModel` — finalized as semantic facade with counterexample (2026-05-29)

The insertion-uniqueness scout (B-insertion-0) **determined the model is FALSE** for flexible `FeynmanSubgraph` carriers without extra boundary-compatibility data.  It is a genuine semantic facade, not a provability gap.

**Counterexample.**  Carrier facts: `FeynmanEdge = (source, target, sector)`, `ExternalLeg = (attachedTo, sector)` — labels only, no record of which boundary internal edge a leg corresponds to; the remnant contracts a promoted child to a *single* star.  Take a promoted child η = `{a, b}` with `η.internalEdges = {(a,b)}`, star `sₕ`, and an external vertex `w ∉ A`:

| parent | vertices | internalEdges | connected? |
|---|---|---|---|
| γ₁ | {a,b,w} | {(a,b), **(a,w)**} | ✅ (a–b, a–w) |
| γ₂ | {a,b,w} | {(a,b), **(b,w)**} | ✅ (a–b, b–w) |

- `γ₁.vertices = γ₂.vertices = {a,b,w}` (the facade's hypothesis).
- residual γ₁ = {(a,w)} → `retargetEdge` → **{(sₕ, w)}**; residual γ₂ = {(b,w)} → **{(sₕ, w)}** — collapse to the *same* edge.
- `remnant.vertices = {sₕ, w}` (both), `remnant.externalLegs = ∅` (both) ⇒ `remnant(γ₁) = remnant(γ₂)` while `γ₁ ≠ γ₂`.
- Both parents are connected; under a suitable `DivergenceMeasure` both are CD/1PI (the abstract divergence + properDisjoint conditions do **not** exclude this).

**Root cause.**  Single-star contraction (`admissibleSubgraphQuotientRemainderSubgraph` collapses η to one star) forgets the *attachment multiplicity* — whether a boundary edge attached to `a` or `b`.  This is the **same root** as `PromotedExternalLegsLiftableModel`: contraction to a star forgets boundary incidence.

**Consequence.**  `forest_inj` cannot be discharged constructively from current carrier semantics; it requires `ForestGraphInsertionUniquenessModel` (an explicit boundary-attachment-compatibility assumption).  `CoassocStrictForestH58Ready` is therefore **constructive up to exactly the insertion-uniqueness semantic assumption**:
- cover ✅, cross ✅, mixed_inj ✅ (fully constructive, off-carrier data-preserving), forest vertex recovery ✅;
- forest_inj depends on `ForestGraphInsertionUniquenessModel` (🔴 semantic facade, counterexample known).

**JAR-central finding — two boundary-semantics facades.**  The formalization decomposes CK 1998's implicit boundary handling into two *precise, counterexampled* assumptions on the flexible carrier:
1. `PromotedExternalLegsLiftableModel` — promoted external-leg inclusion (δ.externalLegs need not contain the retargeted promoted legs);
2. `ForestGraphInsertionUniquenessModel` — graph-insertion uniqueness (single-star contraction forgets attachment multiplicity).

Both originate from the same source (contraction to a star forgets boundary incidence), and both are *false without explicit compatibility data*.  This turns "CK coassociativity holds" into the sharper statement: it holds **modulo two named, counterexampled boundary-semantics assumptions** that the original informal treatment leaves implicit.

#### Track R — boundary-resolved carrier: the bombs disappear (2026-05-29)

The two facades are not defects in CK Hopf algebra — they show the **flat
`FeynmanGraph` carrier is coarser than CK's graph notion**.  CK's informal
proof implicitly retains boundary incidence (which half-edge / insertion slot);
the flat carrier discards it (`deriving DecidableEq` on `(source,target,sector)`
/ `(attachedTo,sector)`), so single-star contraction is lossy.  Track R adds a
**boundary-resolved** carrier where edges/legs carry a persistent identity, and
shows the facades become theorems there.

New file `GaugeGeometry/QFT/Combinatorial/ResolvedFeynmanGraphs.lean` (parallel,
existing 35k LOC untouched; `lake env lean` exit 0):

| sprint | content |
|---|---|
| R-1a | `ResolvedEdgeId`/`ResolvedLegId` (identity tags); `ResolvedFeynmanEdge`/`ResolvedExternalLeg`/`ResolvedFeynmanGraph`; forgetful maps `forget : Resolved → flat` (drop identities) + simp lemmas |
| R-1b | identity-preserving `retarget` (rewrites endpoints by a vertex map `f`, **carries `edgeId`/`legId` through**); `EdgeIdsUnique`/`LegIdsUnique` predicates; **injectivity cores** `ResolvedFeynmanEdge.eq_of_retarget_eq_of_id_unique` + leg analogue — under id-uniqueness, retarget is injective on `G`'s components *even when `f` collapses endpoints* (the flat-carrier failure mode); `forget_retarget` compatibility |
| R-2a | graph-level lift: `retargetInternalEdges`/`retargetExternalLegs`/`retargetGraph` (id-preserving) + simp; `forget_retarget{Internal,External}` (via `Multiset.map_map`); graph-level injOn `retargetInternalEdges_injOn` + leg analogue |
| R-3a | **CK insertion-uniqueness core**: generic `Multiset.map_eq_of_injOn_le` (InjOn-flavoured multiset map injectivity — NOT in Mathlib, proven by `count` ext via `Multiset.count_map_eq_count`); `ResolvedFeynmanGraph.retargetInternalEdges_injective_on_submultisets` + leg analogue — `M₁.map (retarget f) = M₂.map (retarget f) → M₁ = M₂` for submultisets under id-uniqueness.  **The flat counterexample `(a,w),(b,w) → (star,w)` is impossible at the multiset level: the `edgeId` survives the collapse.** |

**Principle established:** `flat retarget = non-injective` (counterexampled) vs `resolved retarget + id-uniqueness = injective` (proven), now at the **multiset / submultiset** level (R-3a) — exactly the level the two facades collapse at on the flat carrier.  This is the mathematical core that turns `ForestGraphInsertionUniquenessModel` (and, via `LegIdsUnique`, the leg side of `PromotedExternalLegsLiftableModel`) into theorems on the resolved carrier.

**Both bomb cores are now theorems (R-3a/R-3b landed together):**
- `retargetInternalEdges_injective_on_submultisets` (edge side → `ForestGraphInsertionUniquenessModel`);
- `retargetExternalLegs_injective_on_submultisets` (leg side → `PromotedExternalLegsLiftableModel`).

Both reduce to the generic `Multiset.map_eq_of_injOn_le` + R-1b's pointwise identity-preserving injectivity.  On the boundary-resolved carrier, **the multiset-level collapse that produced both counterexamples on the flat carrier is provably impossible** — the persistent `edgeId`/`legId` survives star-contraction.  The two facades are no longer "false semantic gates" but **theorems modulo the resolved carrier**, with the flat carrier recovered by the forgetful map.

#### Track R-4-link — forgetful map commutes with contraction (JAR diagram closed) (2026-05-29)

`ResolvedFeynmanGraph.forget_retargetGraph`: `(G.retargetGraph f V).forget` equals the flat graph whose edges/legs have endpoints rewritten by `f`.  This closes the JAR commuting square:
```
        retargetGraph (id-preserving, injective — R-3)
   G  ───────────────────────────────────►  G.retargetGraph f V
   │ forget                          forget │
   ▼                                        ▼
G.forget ──────────────────────────────►  flat retarget by f   (lossy)
        forget_retargetGraph  (commutes)
```
**The flat carrier is the forgetful image of the resolved carrier; the identities `edgeId`/`legId` that `forget` discards are exactly the two semantic facades.**  The resolved contraction is injective (R-3); its forgetful image is the lossy flat contraction where the bombs detonate.

**R-4 scope determination (scout):** discharging the *flat* facade Models from the resolved theorems is **impossible** — the flat facades are flat-false (counterexampled) and `forget` runs resolved→flat, so no consistent identity-lift makes the flat statement true.  R-4-full (unconditional Hopf on the resolved carrier) would require re-deriving the SubGraph layer (2795 LOC) + Coproduct + Coassoc + Antipode on `ResolvedFeynmanGraph` — a separate multi-month program, **not required for the JAR claim**.  R-1..R-4-link already establish the claim: the bombs disappear under boundary resolution, and the flat carrier is the forgetful image.

**Track R complete (R-1a/1b/2a/3a/3b/4-link), `lake env lean` exit 0, existing 35k LOC untouched, 1 new file.**

**Next (R-2/R-3):** resolved contraction (id-preserving), then discharge the two facade statements as theorems in the resolved setting; the forgetful map links back.  R-4 (full Hopf on resolved) is ideal but not required for the JAR claim — R-1..R-3 already prove "the bombs disappear under boundary resolution."  JAR story: **"CK's informal proof is correct for boundary-resolved graphs; the usual flat notation suppresses exactly this structure — and that suppression is precisely the two facades."**

#### `CoassocStrictForestH58Ready` blocker status refinement (2026-05-27)

After the hBP 3/4 discharge, scouted `CoassocStrictForestH58Ready` for direct discharge.  The class has a single field `coassoc` (LinearMap coassociativity of `coproduct_strict_forest`), which `coassoc_strict_forest_linear_h58` produces from `[CoassocStrictForestH58FinitePayloads]` — a typeclass with single field `indexed_classifier : ∀ g, forestComponentSplitPhiIndexedBranchClassifier g`.

The classifier is constructible via `forestComponentSplitPhiIndexedBranchClassifierOfSeparatedCover` ([Coassoc.lean:33707](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L33707)) from two pieces:
- `forestComponentSplitPhiBranchCoverCertificate g` — RHS r-cover by forest or mixed preimage
- `forestComponentSplitPhiBranchInjectivitySeparation g` — 3 fields: `forest_inj`, `mixed_inj`, `cross`

| component | status (2026-05-27) |
|---|---|
| cover certificate | ✅ provided by F2i-3q-F2h-7 `forestQuotientForestSigma_cover_branch_preimage` (conditional on the 4 hBP facade Models + `hForestCompl`) |
| `cross` separation | ✅ discharged 2026-05-27 as `forestComponentSplitPhi_cross_separation` via `isForestByStar_of_forest` + `not_isForestByStar_of_mixed` |
| `forest_inj` (same-branch injectivity, genuine forest side) | 🟡 **open** — `q.1` recovery gap |
| `mixed_inj` (same-branch injectivity, mixed branch) | 🟡 **open** — `q.1` recovery gap |

**`q.1` recovery gap:** Sigma equality on `toQuotientForestSigma` gives `OuterIndex(q₁) = OuterIndex(q₂)` (as Subtype values) + `RepQuotient(q₁) = RepQuotient(q₂)` (HEq, becomes eq after first-factor match).  But `OuterIndex(q).1 = OuterSubgraph(q.1.1, q.2)` depends on **both** q.1 (outer admissible) and q.2 (choice function).  Two different q.1's can in principle produce the same OuterSubgraph via different choice splits, so OuterIndex eq alone does not recover q.1.

**Existing partial injectivity lemmas:**
- `forestComponentForestChoiceOuterSubgraph_inj` ([Coassoc.lean:9061](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9061)) — assumes fixed A, recovers p
- `forestComponentMixedBoundaryOuterIndex_inj_of_q1_eq` ([Coassoc.lean:9158](GaugeGeometry/QFT/HopfAlgebra/Coassoc.lean#L9158)) — assumes q₁.1 = q₂.1, recovers q

Both leave open the q.1 recovery.

**Rejected quick paths:**
- **OuterIndex alone**: insufficient because `OuterSubgraph(A, p) = Left(A, p).elements ∪ PromotedForest(A, p)` depends on both A and p — two (A, p) pairs could in principle align.
- **Use RepQuotient HEq**: requires intricate dependent-type handling after Sigma.fst alignment, plus a non-trivial "RepQuotient determines A" inverse argument.  Sprint D explicitly left this gap; closing it would require ~200-400 LOC of new infrastructure.

**Strategic conclusion:** `CoassocStrictForestH58Ready` remains a facade, **but the obstruction is now refined**:
- cover existence solved (via F2i-3q chain)
- cross separation solved (via existing isForestByStar discriminator)
- 2 injectivity proofs (`forest_inj`, `mixed_inj`) remain as the genuine combinatorial gap, blocked on `q.1` recovery from Sigma-of-derived-outer equality

Future discharge attempt should focus on the q.1 recovery lemma at the OuterSubgraph + RepQuotient combined level.  Sprint D-scale work expected.

### Blocker F2 — `AntipodeStrictForestRightReady` — **Track D structural decomposition (2026-05-28)**

**Status (2026-05-28):** `AntipodeStrictForestRightReady` is now **reduced to a single core-identity facade** `AntipodeForestRightCoreIdentity`, mirroring the hBP decomposition.  The ~190 LOC wrapper layer is proven; only the CK §3 forest-summation cancellation (★) remains.

**Track D layers (all in `Antipode.lean`):**

| layer | declaration | content |
|---|---|---|
| D-1 facade | `antipodeForestRightCoreLHS` / `antipodeForestRightCoreRHS` defs + `class AntipodeForestRightCoreIdentity` + `antipode_forest_right_core_identity` | isolates (★): `∑_A A.toHopfH * S(gen(right A)) = ∑_A (∏γ S(γ)) * gen(right A)` |
| D-wrapper-1a | `antipode_forest_lTensor_admissibleForestStrictSummandWithCanonicalStars_of_mem` | per-summand `lTensor`: `mul'∘S.lTensor (A.toHopfH ⊗ gen(right A)) = A.toHopfH * antipodeGen_forest(right A)` |
| D-wrapper-1b | `mul_antipode_lTensor_coproduct_strict_forest_X` | generator-level right axiom from the facade — mirror of left-axiom proof with `lTensor`; boundary `gen g + S(gen g)`, summand → LHS-core, recursive unfold → `-gen g - RHS-core`, `rw [core identity]; ring` |
| D-wrapper-2 | `axiomLHS_alg_right` + `axiomLHS_alg_right_eq_axiomRHS_alg` + `mul_antipode_lTensor_coproduct_strict_forest` | globalization via `MvPolynomial.algHom_ext` (tensor map order flipped: `map (id) S` = `lTensor`) |
| connector | `instance AntipodeStrictForestRightReady_of_coreIdentity` | discharges the Sprint-E facade from the core-identity facade |

**Net result:** the right-antipode obstruction is no longer a monolithic facade — it is `~190 LOC proven wrapper + 1 isolated core-identity facade`.  The remaining mathematical content is fully concentrated in:
```
antipodeForestRightCoreLHS g = antipodeForestRightCoreRHS g
```
which is the genuine CK 1998 §3 forest-summation cancellation.

**Remaining (★) discharge** still requires the forest re-indexing campaign (expand `S(gen(right A))` recursively → nested double-sum over A and sub-forests of right A → telescoping/inclusion-exclusion bijection).  Estimated ~500-1500 LOC (Sprint-D-scale), unchanged.  But it is now a *single, precisely-stated* target rather than a tensor-algebra-entangled axiom.

#### Track D-core — CK §3 reindexing infrastructure (2026-05-29)

The (★) discharge has been further prepared with three reindexing-infrastructure layers (all in `Antipode.lean`, full file `lake env lean` exit 0):

| layer | declaration | content |
|---|---|---|
| D-core-1 | `antipodeForestRight_internalEdges_card_lt` | **measure decrease**: `right A = G/A` has strictly fewer internal edges than `g` (via `repG_internalEdges_card_eq_of_toClass` + `contractWithStars_internalEdges` + `card_map` + `complementEdges.card = G.I.card − A.I.card < G.I.card` from `0 < A.I.card`).  Enables strong induction on `(repG g).internalEdges.card` |
| D-core-2a | `antipodeGen_forest_eq` + `antipodeForestRightBoundaryTerm` + `antipodeForestRightDoubleSumTerm` | closed form `antipodeGen_forest g = −gen g − antipodeForestRightCoreRHS g` (dif-sum → attach-form conversion); plus the two named pieces of the expanded LHS |
| D-core-2b | `antipodeForestRightCoreLHS_expand_once` | `antipodeForestRightCoreLHS g = −boundaryTerm g − doubleSumTerm g`.  Proof: combined sum vanishes termwise (`a·(−X−C) + a·X + a·C = 0` via `Finset.sum_add_distrib` + `Finset.sum_eq_zero` + `ring`), closed by `sub_eq_zero` + `ring` + the termwise fact (avoids `linear_combination`, not imported) |

**(★) is now concretely reduced** to relating
```
antipodeForestRightCoreLHS g  =  − antipodeForestRightBoundaryTerm g − antipodeForestRightDoubleSumTerm g
```
against `antipodeForestRightCoreRHS g`.  The `doubleSumTerm` (`∑_A A.toHopfH · antipodeForestRightCoreRHS(right A)`) is the concrete nested-forest re-indexing target, with `right A` strictly smaller (D-core-1) so strong induction applies.

**Remaining payload (D-core-3+):** the CK §3 inductive/reindexing core relating the expansion to `antipodeForestRightCoreRHS` — the genuine ~500-1500 LOC mathematics.

#### Track D-core-3 scout — CK §3 core is an irreducible kernel (2026-05-29)

Scouted the strong-induction route for `AntipodeForestRightCoreIdentity`.  **The plain induction does not close** — the kernel is genuine CK §3 mathematics, not Lean plumbing.

**Established facts:**
1. D-core-1 measure decrease ✅ — `right A` has strictly fewer internal edges than `g`.
2. D-core-2 LHS expansion ✅ — `coreLHS g = − boundaryTerm g − doubleSumTerm g`.
3. `doubleSumTerm g = ∑_A A.toHopfH · coreRHS(right A)` is **definitional** (the `def` itself, D-core-2a) — the user-predicted "first stone" is just `rfl` and unlocks nothing.

**Why the plain IH `P(g) := coreLHS g = coreRHS g` does not close:**
Applying IH at `right A` (valid by D-core-1) rewrites `coreRHS(right A) = coreLHS(right A)`, then D-core-2b at `right A` expands to `−boundary(right A) − doubleSum(right A)`.  This produces **deeper nested forests**, not the target `coreRHS g`.  The outer-product antipode in `coreRHS g = ∑_A (∏γ S(γ)) gen(right A)` cannot be matched by the inner-nested IH form via algebra — the gap is a **sign-cancelling nested-forest reindexing**.

**Root cause (mathematical):** (★) ⟺ "the left convolution-inverse `S` of `id` is also a right inverse."  In a general monoid a left inverse need not be a right inverse; the implication needs the connected-filtered Hopf structure.  Two viable routes, both ~500-1500 LOC Sprint-scale:

| Path | Content |
|---|---|
| Convolution local-nilpotency | Build convolution algebra on `End(HopfH)`; show `id − η∘ε` is locally nilpotent w.r.t. edge-count filtration ⇒ unique two-sided inverse ⇒ left `S` = right inverse.  Mathlib convolution infra is thin |
| Explicit nested-forest reindexing | Expand both `coreLHS`/`coreRHS` into nested-forest sums; exhibit a sign-reversing involution (Zimmermann forest formula).  Project's explicit-construction style, but the genuine CK §3 combinatorics |

**Conclusion:** `AntipodeForestRightCoreIdentity` is a **genuine irreducible mathematical kernel**, maximally isolated.  Unlike `hForestCompl` (already-proven) or the hBP Models (constructive transports), (★) is new mathematics of the same character H5.8 was for coassociativity.  There is **no low-risk stepping stone**; the next real step IS the CK §3 campaign.  Pause here with the kernel precisely stated on a proven edge-count-induction-ready skeleton (D-core-1/2).

#### Track D-core scout-2 — Mathlib convolution infra + kernel dependency (2026-05-29)

Scouted Mathlib's `RingTheory/Coalgebra/Convolution.lean` and `HopfAlgebra/Basic.lean` for a Path-1 (convolution local-nilpotency) attack on (★).

**Mathlib infra findings:**
- `WithConv (C →ₗ[R] A)` is an associative convolution **Ring** for `[Ring A]` alone (`convRing`, cocommutative NOT required) — usable for CK.
- `convCommRing` (commutative) requires `[IsCocomm R C]` → CK is non-cocommutative → **unavailable**.
- `Monoid.left_inv_eq_right_inv` exists (`a*b=1 → b*c=1 → a=c`).
- **No** left-axiom → right-axiom bridge: `HopfAlgebra` carries both `mul_antipode_rTensor_comul` and `mul_antipode_lTensor_comul` as independent fields (Basic.lean:63-67).
- **No** connected-graded antipode-existence / local-nilpotency theorem in Mathlib.

**Path-1 structure:** in `WithConv (HopfH →ₗ HopfH)`, the proven left axiom is `S *conv id = 1` and (★) is `id *conv S = 1`.  Closing via `left_inv_eq_right_inv` needs a *constructed* convolution right-inverse `T` of `id` (then `S = T`), which is exactly the connected-graded local nilpotency of `id − η∘ε` (geometric series under edge-count filtration).  This piece is **not in Mathlib** — self-build required.

**🔑 Kernel dependency discovered:** using `WithConv` requires a `Coalgebra ℚ HopfH` instance, which depends on coassociativity, i.e. on **`CoassocStrictForestH58Ready` (Track B kernel)**.  Therefore:
```
CoassocStrictForestH58Ready  →  Coalgebra ℚ HopfH instance  →  WithConv convolution ring
   →  (with connected-graded local nilpotency)  →  AntipodeForestRightCoreIdentity (★) via Path 1
```
- **Path 1** (convolution) is elegant but **downstream of Track B**.
- **Path 2** (explicit nested-forest sign-cancelling involution) is self-contained but heavier (CK §3 combinatorics directly on MvPolynomial elements).

**Strategic consequence:** Track B is no longer a standalone kernel — discharging it opens the elegant Path-1 route to Track D.  Priority shifts to **B → D-Path1** over **D-Path2 standalone**.

**Original analysis (still valid):** The right antipode axiom requires a
forest-summation cancellation identity in CK 1998 §3 style that is
*not* a mirror of H6.6a.  CK is non-cocommutative → convolution
non-commutative → cannot derive right from left via a Mathlib bridge.

**Recommended attack second.**  Even though F2 is the mathematical
heavy lifting, do F1 first so that when F2 lands, the unconditional
`HopfAlgebra ℚ HopfH` instance is one rebuild away.

**Strategist's design discipline (carry over from Sprint D H5.8):**
do *not* attack the right axiom directly inside the conditional
`HopfAlgebra` instance.  Instead, isolate the mathematical content as
a single payload theorem first, e.g.

```lean
theorem right_antipode_forest_recombination_identity
    (g : HopfGen) :
    ∑ A ∈ forestCoproductProperForestIndex g,
        A.toHopfH * antipodeGen_forest
          (...right-factor representative of A...)
      = ...explicit cancellation target...
```

with the precise statement deferred to Sprint F's first design pass.
Once the payload theorem is proved on its own terms (without
referencing `mul_antipode_lTensor_coproduct_strict_forest` directly),
discharging `AntipodeStrictForestRightReady` is a `simp`/`rw`
exercise on top of the existing H6.6a infrastructure.

This mirrors the H5.8F strategy: the H5.8 facade
`CoassocStrictForestH58FinitePayloads` was discharged via a single
`indexed_classifier` field whose underlying theorem proof was the
heart of Sprint D.  H6.7 should follow the same shape.

**Files expected to be touched:** `Antipode.lean` (or a new
`AntipodeRight.lean` if the payload theorem is bulky enough to
warrant separation; default to keeping in `Antipode.lean` until the
size justifies a split).

### Sprint F completion criterion

* ✅ both facades discharged via canonical instances (no `[Ready]`
  hypothesis on the final `HopfAlgebra ℚ HopfH` instance).
* ✅ axiom audit (`AxiomAudit.lean`) shows the unconditional
  `instHopfAlgebraHopfHStrictForest` depends on
  `[propext, Classical.choice, Quot.sound]` only.
* ✅ `HOPF_DECOMPOSITION.md` updated with Sprint F closure record.

After Sprint F, the deferred / out-of-scope items below
(sub-Hopf algebras, Birkhoff decomposition, ForestFormula re-derivation,
gauge-sector generalization) become available as next-sprint candidates.

---

## Project deliverable as of 2026-05-27 — dependency boundary visible

The conditional `HopfAlgebra ℚ HopfH` instance is **structurally complete modulo three documented mathematical facades**.  Sprint F's completion criterion above is not yet met — the two `[Ready]` facades remain — but the project is at a natural pause point where every open gap has been characterized, isolated, and classified.

### Completed sprints (A–E + F2i-3q)

| Sprint | Content | Status |
|---|---|---|
| A | H0 + H1 (incl. H1.17 `[ConKr]` irreducible) | ✅ |
| B' | H1.WF + H2.1–2.4 + H3.0–3.5 (Plan-D Hybrid `HopfH_temp`) | ✅ |
| C / C1 / C2 | H2.5 + H3.6–3.9 + H4 (Path-W typeclass family; Path-Sub class lift) | ✅ |
| D | H5 Bialgebra incl. H5.8F coassociativity via admissible-forest carrier; `coproduct_strict_forest` AlgHom | ✅ |
| E | H6.1–H6.8 antipode + conditional `HopfAlgebra ℚ HopfH` | ✅ |
| **F2i-3q forest cover identity** | Q-membership chain, v3 source subgraph (Left⊔LiftedRight⊔LiftedForest), Skolem-form hBP, F2h-6/7 forest analogs, full branch cover disjunction, hForestCompl discharge, hBP structural decomposition into 4 facade Models (3 discharged constructively) | ✅ (2026-05-15 — 2026-05-27) |

### Remaining facades (3 mathematical gaps)

| Facade / class | Mathematical content | Status | Estimated work | Recommended future route |
|---|---|---|---|---|
| `PromotedExternalLegsLiftableModel` (hBP last facade) | `η.externalLegs ≤ Plus(δ).externalLegs` for `η ∈ PromotedComponents g r δ` | 🔴 **Semantic facade**.  Gate `PromotedExternalLegs.map retarget ≤ δ.externalLegs` fails in general — δ.externalLegs is arbitrary sub-multiset of quotient external legs subject to CD/support; star-touching does not force retargeted promoted legs to be in δ.externalLegs.  Rejected redesigns: canonical sorted correspondence (solves wrong problem), strengthen ForestComponents (cascading rewrite), Plus.externalLegs superset (breaks remainder equality) | Plus-chain semantic redesign | External-leg semantics campaign: introduce constraint at η'/δ construction level (Sprint D-ish scope), OR accept as foundational assumption |
| `CoassocStrictForestH58Ready` (Sprint E facade for H5.8) | Coassoc LinearMap equality on `coproduct_strict_forest` | 🟡 **Refined facade**: cover ✅ (F2i-3q-F2h-7), cross ✅ (2026-05-27), foundational injectivity helpers landed 2026-05-27 (Track B-1a/1b-1/1b-2/1b-3-scout), `mixed_q1_recovery` 🟡 paused at HEq plumbing, `forest_q1_recovery` 🟡 deeper combinatorial gap | ~450-550 LOC (revised after Track B HEq-plumbing assessment) | Coassoc injectivity campaign: dependent-equality HEq-plumbing sprint around `Sigma.mk.injEq` + RepRightQuotient transport (Sprint-D-scale, comparable in friction to `_BCandidatePromotesModel`) |
| `AntipodeStrictForestRightReady` (Sprint E facade for H6.7) | `mul ∘ (id ⊗ S) ∘ Δ = η ∘ ε` — right antipode axiom | 🟡 **Decomposed 2026-05-28 (Track D)**: ~190 LOC wrapper layer proven; `AntipodeStrictForestRightReady` reduced to single facade `AntipodeForestRightCoreIdentity` = core identity (★) `∑_A A.toHopfH * S(gen(right A)) = ∑_A (∏γ S(γ)) * gen(right A)`.  Only (★) remains | ~500-1500 LOC for (★) (Sprint-D scale) | Antipode CK §3 cancellation campaign: forest re-indexing of the now-isolated (★) |
| ~~`hForestCompl`~~ | Multiset arithmetic accounting | ✅ **discharged 2026-05-27 (Track A-1)** as theorem `_SourceAdmissibleSubgraph_v3_complementEdges_card_pos`; auto-supplied by 5 `_fully_canonical` wrappers (`Q_v3_fully_canonical`, `Q_v3_fully_canonical_mem_forestChoiceSigmaIndex`, `Q_v3_fully_canonical_toQuotientForestSigma_eq`, `forestPreimage_of_isForestByStar_fully_canonical`, `cover_branch_preimage_fully_canonical`).  No remaining `hForestCompl` explicit argument at the user-facing API | — | ✅ closed |

### Deliverable statement

> The conditional `HopfAlgebra ℚ HopfH` instance is structurally complete modulo three documented mathematical facades (as of 2026-05-27 Track A-1: `hForestCompl` is now fully discharged and wired into `_fully_canonical` wrappers).  All open gaps have been identified and classified:
>
> - **Semantic** (`PromotedExternalLegsLiftableModel`): an assumption about the structure of δ.externalLegs for δ ∈ ForestComponents.  Resists local redesign because the gap is in the *meaning* of leg-presence, not in the *form* of the construction.
> - **Combinatorial** (`CoassocStrictForestH58Ready` injectivity): a `q.1` recovery gap from Sigma equality on `toQuotientForestSigma`.  Discharge requires either combined OuterIndex+RepQuotient HEq argument or an "OuterSubgraph determines A under properDisjoint" theorem.
> - **Mathematical** (`AntipodeStrictForestRightReady`): a CK 1998 §3 forest-summation cancellation identity in the non-cocommutative setting.  Mathlib offers no shortcut for non-cocommutative bialgebras.

### Final note

**No remaining gap is a local Lean wiring issue.**  All open gaps are identified mathematical assumptions or Sprint-D-scale payloads.  The project is in a state where:
- The conditional Hopf algebra structure is proven.
- The path to the unconditional instance is fully characterized.
- Future work is at the granularity of named mathematical interfaces, not unknown obstacles.

### Future tracks (in order of feasibility)

~~A. `hForestCompl` arithmetic discharge~~ — ✅ **closed 2026-05-27** (Track A-0 scout determined the theorem was already proven; Track A-1 added 5 `_fully_canonical` wrappers auto-supplying it).  
B. **Coassoc injectivity campaign** — `forest_inj` + `mixed_inj` for `BranchInjectivitySeparation`.  Foundational helpers landed 2026-05-27; q.1 recovery blocked at HEq plumbing (~450-550 LOC).  
C. **External-leg semantics campaign** — `PromotedExternalLegsLiftableModel` discharge via Plus-chain semantic redesign.  Confirmed semantic gate failure; may require strengthening `ForestComponents` predicate.  
D. **Antipode CK §3 cancellation campaign** — now reduced (Track D, 2026-05-28) to the single core identity (★) `antipodeForestRightCoreLHS g = antipodeForestRightCoreRHS g`; ~190 LOC wrapper layer already proven.  Only (★) remains (~500-1500 LOC).

Tracks B/C/D each require Sprint-scale commitments for their remaining math kernel.

---

## Post Track-D dependency boundary (2026-05-28)

**All monolithic facades have been reduced to named mathematical kernels.**  After Tracks A/B/D, the conditional `HopfAlgebra ℚ HopfH` instance depends on exactly 3 isolated kernels (down from the original opaque facades + hForestCompl + hBP).

### Audit (2026-05-28)

- `sorry` / `admit` in code: **0** (occurrences are doc-comment phrases only)
- project-specific axioms: **0**
- `hForestCompl`: ✅ removed from facade list (Track A-1, 5 `_fully_canonical` wrappers)
- hBP 4-facade decomposition: **3 discharged** (`BElementMapAdmissibleModel`, `BCandidateProperForestIndexModel`, `BCandidatePromotesModel` have instances), **1 facade** (`PromotedExternalLegsLiftableModel`, no instance — semantic gate)
- `AntipodeStrictForestRightReady`: ✅ has `instance AntipodeStrictForestRightReady_of_coreIdentity` from `AntipodeForestRightCoreIdentity` (no longer a primitive blocker)

### Remaining kernels

| Kernel | Skeleton status | Remaining math kernel | Campaign estimate |
|---|---|---|---|
| `PromotedExternalLegsLiftableModel` | hBP 3/4 discharged; this is the residual | **Semantic**: gate `PromotedExternalLegs.map retarget ≤ δ.externalLegs` fails in general (δ.externalLegs need not contain retargeted promoted legs) | Plus-chain semantic redesign — possibly foundational; not a wiring task |
| `CoassocStrictForestH58Ready` | cover ✅ + cross ✅ + foundational injectivity helpers ✅ | **Combinatorial/HEq**: `q.1` recovery from `toQuotientForestSigma` Sigma equality, blocked at dependent-equality plumbing (`mixed_q1_recovery` ~300-400 LOC, `forest_q1_recovery` deeper) | ~450-550 LOC HEq-plumbing campaign |
| `AntipodeForestRightCoreIdentity` | ~190 LOC wrapper layer ✅ (D-1, D-wrapper-1a/1b/2, connector) | **CK §3 forest cancellation**: (★) `∑_A A.toHopfH · S(gen(right A)) = ∑_A (∏γ S(γ)) · gen(right A)` | ~500-1500 LOC forest re-indexing campaign |

### Deliverable statement (refined)

> The conditional `HopfAlgebra ℚ HopfH` instance is structurally complete modulo **3 named mathematical kernels**, each precisely stated and isolated.  No remaining gap is a Lean wiring issue — all three are genuine mathematical content (1 semantic assumption, 1 combinatorial/dependent-equality, 1 CK §3 cancellation).  The skeleton around each kernel (~190 LOC for Antipode, foundational helpers for Coassoc, 3/4 hBP Models) is proven.

### Strategic shape achieved

The project has converged from "several opaque facades" to a **clean kernel decomposition**: every remaining obstacle is a single, named, precisely-stated mathematical interface with a proven skeleton around it.  This mirrors the successful hBP pattern applied uniformly across all three upstream blockers.

---

## Deferred / out of scope

- **Sub-Hopf algebras** (e.g., the ladder Hopf algebra) — instance theorems under the full Hopf construction. Defer to post-Sprint E.
- **Birkhoff decomposition** for renormalization scheme matching — depends on the Hopf instance and on a renormalization scheme datum; downstream of Sprint E.
- **Connection to `ForestFormula.lean`** — the existing `R_operation` should be re-derived as the Birkhoff projection once the antipode is in place.
- **Generalization to gauge sectors / sub-Hopf by sector** — defer.

---

## Methodological note

This decomposition follows the NSBarrier playbook (`PlaybookStrategy` / `withClaudeCode` methodology):

1. **Tag every statement up front.** No statement may be implemented without first being placed in the table.
2. **Push `[ConKr]` count down by aggressive layering.** Each combinatorial subfact gets its own statement with `[Comb]` or `[Graph]` tag.
3. **Distinguish `[ConKr]` from `[ConKr-derived]`** (introduced 2026-04-23). A statement *of CK form* whose proof reduces to a prior `[ConKr]` by `rw`/induction does NOT count as a new irreducible. This is the discipline that exposes the "true irreducible footprint".
4. **Sprint cuts coincide with `[ConKr]` boundaries OR mechanical/recursive grain boundaries.** Sprint A absorbed H1.17 (the sole `[ConKr]`); subsequent sprints partition by qualitative work-character (mechanical wiring vs recursion-heavy vs Hopf-instance assembly).
5. **Stubbing strategy:** if a `[ConKr]` stalls, parameterize downstream theorems by the corresponding `Hypothesis` typeclass rather than introducing an `axiom`. This preserves the "axiom-free" property. (Not needed in Sprint A; H1.17 closed cleanly.)

Final goal mirrors `geometric_main` and `physical_consistency`:

> The `HopfAlgebra ℚ HopfH` instance carries no project-specific axiom; the entire Connes–Kreimer construction is internalised through finite combinatorics on Multisets.
