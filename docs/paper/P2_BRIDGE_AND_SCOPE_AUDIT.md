# P2 — abstract-CK ↔ stable-φ⁴ bridge audit, paper scope, and novelty positioning

*Decision document for P2. Resolves the three P2 items: (1) the abstract-CK ↔ stable-φ⁴
connection, (2) the counit/bialgebra/antipode scope → paper title, (3) related-work /
novelty positioning. The guiding instruction (roadmap §6) was to **audit the
carrier/forgetful relationship BEFORE building any bridge — this is not a `cast`-and-connect
job**. That audit is done below; its verdict shapes items (2) and (3).*

---

## 1. The bridge audit (P2 item 1)

### 1.1 The two sides, precisely

| | Abstract resolved CK (R-6c terminus, body-556) | Stable φ⁴₄ (QFT-R1, body-651) |
|---|---|---|
| Carrier | `ResolvedHopfGen := { c : ResolvedFeynmanGraphClass // (toFlatClass c).IsConnectedDivergent }` | `StableResolvedPhi4HopfGen := { c : ResolvedFeynmanGraphClass // c.IsConnectedDivergentFor phi4… ∧ c.HasStableBoundaryIds }` |
| Extra constraint | none beyond connected-divergent | **+ `HasStableBoundaryIds`** (the idempotent boundary-ID certificate) |
| Power-counting hypotheses | the abstract CK divergence **classes** `IsPermInvariantDivergence`, `IsDivergencePreservedByContract`, `IsDivergencePreservedByAdmissibleForestContract`, `IsDivergenceReflectedByAdmissibleForestContract`, `IsAmbientInvariantDivergence`, `IsIsoInvariantDivergence` (carried as *instances*), plus `Measure`/`E`/`rep*` supplies | **none** — the φ⁴ power-counting is a concrete *providable* value `phi4DivergenceMeasureFamily`; `coproduct_resolved_stable_phi4_coassociative` takes **zero class-instance arguments** |
| Terminus | coassoc on `ResolvedHopfGen` **modulo the CK divergence classes** | coassoc on `StableResolvedPhi4HopfGen` **unconditionally** |

### 1.2 The decisive structural fact

The φ⁴ development did **not** instantiate the abstract 556 machinery. It **reformulated every CK
divergence law from an abstract typeclass into a concrete, providable family/supply structure**,
and it did so *specialized to the canonical forest contraction*, not to an arbitrary nested subgraph.
Evidence in the source:

- `phi4PermInvariantDivergenceMeasureFamily : PermInvariantDivergenceMeasureFamily phi4DivergenceMeasureFamily`
  (a **structure**, via `degree_mapPerm`) — and body-565 states explicitly: *"The old
  `IsPermInvariantDivergence` is not used."*
- `DivergenceFamilyForestReflection.lean` — the forest-contract **reflection** law
  (`phi4CanonicalForestContractGraph_isDivergent_iff_ambient`,
  `…_ambient_isDivergent_of_quotient`) proved for the φ⁴ family, *"…the φ⁴ specialization…
  never an arbitrary nested subgraph. The old generic class …"*
- `DivergenceFamilyForwardLanding.lean` — the contract-preservation (forward landing) in family form.

So the φ⁴ side carries the **mathematical content** of the CK divergence laws, but in a
concrete family form specialized to the canonical contraction — deliberately *avoiding* the
generic abstract classes (that avoidance is the "no forbidden divergence class in any decl type"
discipline held across the whole φ⁴ campaign). The φ⁴ coassociativity is a **genuinely parallel,
self-contained proof**, not a corollary of 556.

### 1.3 Tier-by-tier feasibility (roadmap §6's three tiers)

- **Minimal tier** — "φ⁴ data satisfies the abstract interface" (`instance : IsPermInvariantDivergence (phi4…)`,
  … , so 556 instantiates at φ⁴).
  - *Perm-invariance*: essentially already there — the family `degree_mapPerm` is the class's content; a bridge
    instance is provable.
  - *Contract / forest-contract reflection*: **uncertain**. The abstract classes are **generic** (arbitrary
    nested subgraph); the φ⁴ family theorems are **canonical-contraction-specialized**. The generic class may
    demand strictly more than the φ⁴ family proves — closing that gap is real work, not a rename.
  - *And even if all six discharge*: 556 then yields coassoc on **`ResolvedHopfGen`** (the abstract carrier),
    **not** on `StableResolvedPhi4HopfGen`. It would be a *separate* abstract result, not the φ⁴-stable one we
    already have unconditionally. **Low marginal value.**
- **Middle tier** — a generator-level comparison `Δ^stable_φ⁴(X_G) = Δ^abstract(X_G)`.
  - The two coproducts sum over **different carriers**: the abstract one over the W″ (leg-saturated) supply,
    the φ⁴-stable one over the W‴ (edge-complete) supply. **These are different filtered coproducts** — the
    W‴ ⊊ W″ strictness (Figure 1) and the body-663+ discrepancy are the formal proof that a change of
    forest-support carrier changes the coproduct/renormalized value. A comparison theorem would therefore
    have to *reproduce that difference*, not assert an equality. **This tier is a trap: the honest statement
    is that they differ, which is Result E, already proved.**
- **Maximal tier** — carrier equivalence / a forgetful morphism transporting the abstract Hopf structure onto
  the stable carrier.
  - The carriers are **not** equivalent: `StableResolvedPhi4HopfGen` adds `HasStableBoundaryIds`, and the
    coproducts differ (above). A forgetful map `StableResolvedPhi4HopfGen → ResolvedHopfGen` exists (drop the
    stability certificate, coarsen the φ⁴-family CD to the generic CD), but it does **not** intertwine the two
    coproducts (different carriers). **Confirmed `cast`-trap — exactly the body-625 hazard the roadmap
    warned about.** Transporting the abstract counit/antipode this way would be unsound.

### 1.4 Verdict on the bridge

**Do not build the middle or maximal bridge** — the carriers and the coproducts genuinely differ, and the
"difference" is itself one of the paper's results (Result E). **The minimal bridge is possible but
low-value** (a separate abstract corollary with a generic-vs-canonical gap). The φ⁴ development is
**stronger as it stands**: it realizes CK renormalization *concretely and unconditionally*, built directly
from φ⁴ Feynman-graph combinatorics, rather than by inhabiting an abstract Lean interface.

**Paper framing (recommended).** Present the abstract resolved-CK layer as **prior context in the same
repository**, and the φ⁴ result as a **self-contained concrete realization** — "we build the Connes–Kreimer
renormalization structure directly and unconditionally for a concrete φ⁴₄ Feynman-graph Hopf algebra",
NOT "we instantiate an abstract Lean typeclass interface". This is honest, avoids the trap, and is the
stronger claim.

---

## 2. Counit / bialgebra / antipode scope → the title (P2 item 2)

What the φ⁴ side has, natively and unconditionally (no inheritance from the abstract side needed — it was
all built directly): **coproduct + coassociativity (R1); counit `ε` with both counit laws; associative
unital character convolution; Rota–Baxter subtraction; well-founded Bogoliubov recursion; genuine
counterterm/renormalized characters; the Birkhoff factorization `φ₋ ⋆ φ = φ₊`; and the carrier-support
renormalization discrepancy (R2)**. Missing: the **antipode** (and hence a bundled `Bialgebra`/`HopfAlgebra`
instance and the convolution-inverse `φ₋ = φ ∘ S_H`).

Consequently the honest scope is **more than a "coproduct coassociativity" paper and less than a full
"Hopf algebra" paper**:

| Title candidate | Requires | Verdict |
|---|---|---|
| *"…Coassociativity for the Stable Resolved φ⁴ Forest Coproduct"* | coproduct + coassoc only | **understates** the work (ignores all of R2) |
| *"A Connes–Kreimer Hopf Algebra for φ⁴ Theory in Lean 4"* | counit + bialgebra + grading/connectedness + **antipode** | **overstates** — antipode not done |
| ✅ *"A machine-verified Connes–Kreimer Birkhoff factorization for φ⁴₄, and the forest-support dependence of the renormalized amplitude"* | coassoc + convolution + counit + Rota–Baxter + Birkhoff + Result E — **exactly what is proved** | **recommended** |

The recommended title claims the **renormalization Birkhoff decomposition** (the central object of
Hopf-algebraic renormalization) plus the **new carrier-support-dependence result** — the two headline
theorems (paper Thm 6 + Thm 7 in `PaperMainTheorems.lean`), scaffolded by the coassociativity + character
algebra (Thm 1–5). It neither claims the antipode nor hides the R2 content. **The antipode is explicitly
future work (QFT-R3) — a separate campaign, not a "missing tile".**

*Strongest = the exact closure the central claim needs, no more.* Chasing counit/bialgebra/antipode "because
they might be reachable" would risk the abstract-bridge trap (§1.3) for structure the paper does not need.

---

## 3. Related work / novelty positioning (P2 item 3)

### 3.1 What is genuinely new here

1. **A concrete, complete, machine-verified CK Birkhoff factorization for a real φ⁴₄ Feynman-graph Hopf
   algebra** — not an abstract Hopf-algebra axiomatization, but built from actual divergent-subforest
   combinatorics, coassociative unconditionally, with the Bogoliubov recursion's **termination formally
   owned by Lean** (the W‴ `IsProperForest` positive complement).
2. **Result E — the forest-support renormalization discrepancy** (paper Thm 7): the *carrier* of admissible
   subdivergences is a renormalization input, and changing it (W‴ ⊊ W″) propagates **exactly** to the
   renormalized amplitude — the difference is a genuine counterterm-times-cograph sum over the dropped
   sector, with a Lean-checked witness pair (Figure 1 = necessary counterexample dropped by the fifth axis;
   the bubble graph = positive example passing it, giving a non-primitive coproduct). We are not aware of a
   classical statement isolating *forest-support choice* as a renormalization-scheme axis in exactly this
   form. **This is the referee-facing novelty.**

### 3.2 Positioning against the literature

- **Connes–Kreimer** (*CMP* 2000/2001), **Kreimer** (rooted trees, 1998): the abstract Hopf-algebraic
  renormalization framework. *We give a concrete φ⁴₄ instance built from Feynman-graph combinatorics and
  machine-verify the Birkhoff decomposition, plus the carrier-support result which is not in the abstract
  theory.*
- **Ebrahimi-Fard–Guo–Kreimer** (Rota–Baxter / algebraic Birkhoff, ~2004): the Rota–Baxter formulation of
  BPHZ. *We formalize the weight −1 Rota–Baxter subtraction vessel and the factorization it produces; our
  `1−R` is proved also weight −1, and the Bogoliubov recursion's well-foundedness is a theorem, not an
  assumption.*
- **BPHZ (Bogoliubov–Parasiuk / Hepp / Zimmermann)** — the forest formula. *Our Bogoliubov recursion is the
  forest formula realized as a terminating recursion over the subdivergence poset; the termination is
  carried by the boundary-resolved carrier's positive-complement axis.*
- **Formal-methods prior art** (Hopf algebras of trees / this repo's abstract CK layer): *the formalization
  lineage; our contribution is the concrete φ⁴₄ renormalization character theory and Result E.*
- **Superrenormalizable / lower-dimensional φ⁴** (φ⁴₃, φ⁴₂): potential *extensions* — the contraction-defect
  classification (roadmap P3) would place φ⁴₄'s marginal case in a family (φ³₆ positive, φ⁴₃
  reflection-failure, φ⁶₄ forward-failure). *Noted as the second-paper / future direction, not claimed here.*

### 3.3 Candidate venues (math-physics, per the pivot)

*Letters in Mathematical Physics* or *Annales Henri Poincaré* for the focused Thm 6 + Thm 7 paper;
*Journal of Mathematical Physics* for the full A–E development; *Communications in Mathematical Physics* only
if Result E's novelty is foregrounded and the exposition is self-contained.

---

## 4. P2 decisions (summary)

1. **Bridge**: do NOT build the middle/maximal abstract-CK bridge (cast trap — carriers and coproducts
   genuinely differ; the difference is Result E). The minimal bridge is possible but low-value. **Frame the
   φ⁴ result as a self-contained concrete realization; the abstract CK layer is prior context.**
2. **Scope/title**: **"machine-verified CK Birkhoff factorization for φ⁴₄ + forest-support dependence"** —
   more than coproduct, short of full Hopf algebra; **antipode = QFT-R3 future work**.
3. **Novelty**: lead with (i) the concrete verified Birkhoff factorization and (ii) Result E
   (forest-support renormalization dependence); position against Connes–Kreimer / EFGK / BPHZ; note the φ⁴₃/φ⁶₄
   classification as future work.

*Next actionable step after this audit: draft the paper (abstract + section skeleton) around paper Thm 6 +
Thm 7 as headline and Thm 1–5 as scaffolding, using `QFT_RESULTS_INVENTORY.md` and
`PaperMainTheorems.lean` as the source of record.*
