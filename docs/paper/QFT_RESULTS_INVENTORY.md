# φ⁴₄ Connes–Kreimer renormalization, machine-verified — Results Inventory

*Working consolidation of the formal results, framed for a **mathematical-physics**
readership (pivoting away from a pure-formalization venue). This is the raw material for
the paper: an accurate, complete catalog of what is proved, the exact Lean 4 statements,
and the physics meaning of each. Every headline theorem is machine-verified and
axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]` — no `sorry`,
no `admit`, no `native_decide`, no project axiom).*

*Repository: `miosync-masa/ck-hopf-formalization`, v2.0.0, DOI `10.5281/zenodo.21765915`.
Lean `v4.29.0`, Mathlib `v4.29.0`. Combined `GaugeGeometry/QFT` + `GaugeGeometry/Core`:
**185,066 lines of Lean** (935 files).*

---

## 0. The one-sentence claim

> We give a **complete, unconditional, machine-checked realization of the Connes–Kreimer
> Birkhoff decomposition of renormalization** — `φ = φ₋⁻¹ ⋆ φ₊` in its factorized form
> `φ₋ ⋆ φ = φ₊` — on a **concrete φ⁴₄ Feynman-graph Hopf algebra**, together with a new
> formal theorem: a change in the admissible-forest support of the coproduct **propagates
> exactly** to the renormalized amplitude, with the difference given by a genuine sum of
> counterterm-times-quotient weights over the dropped forest sector.

The mathematical spine is the Connes–Kreimer Hopf algebra of Feynman graphs
(Connes–Kreimer, *Comm. Math. Phys.* 1998–2000) and the Rota–Baxter / algebraic-Birkhoff
formulation of renormalization (Ebrahimi-Fard–Guo–Kreimer). The contribution here is (i) a
**concrete φ⁴₄ instance** built from actual Feynman-graph combinatorics rather than an
axiom schema, (ii) its **full formal verification** in Lean 4, and (iii) a **new
carrier-support-dependence result** with no classical antecedent we are aware of.

---

## 1. The objects

| Object | Definition | Physics meaning |
|---|---|---|
| Carrier `StableResolvedPhi4HopfGen` | connected, superficially-divergent, id-preserving φ⁴ graph **classes** with a stable boundary-ID certificate | 1PI superficially-divergent φ⁴₄ subgraphs (the objects that get renormalized) |
| Hopf algebra `H := MvPolynomial StableResolvedPhi4HopfGen ℚ` | free commutative ℚ-algebra on the generators | the Hopf algebra of φ⁴₄ Feynman graphs (disjoint union = product) |
| Coproduct `Δᵣˢ := coproduct_resolved_stable_phi4 : H →ₐ[ℚ] H ⊗ H` | on a generator `Δᵣˢ(X_G) = X_G ⊗ 1 + 1 ⊗ X_G + Σ_{F} L_F ⊗ R_F` | extraction of divergent subforests `F`: `L_F` = the forest, `R_F` = the cograph `G/F` |
| Forest carriers `W″ ⊋ W‴` | leg-saturated (`W″`) and additionally edge-complete (`W‴`) admissible forest indices | two admissible-subdivergence prescriptions; `W‴` imposes a stricter (fifth) axis |

The generator carrier is **boundary-resolved and stable**: half-edge / leg identities
persist, and the boundary completion of a subforest is *idempotent* under iteration, so
every combinatorial round-trip is a genuine equality with exact multiplicity — no orbit
quotient, no dependent transport. This is the technical device that makes the coproduct
associative on the nose (see §7 of `../PHI4_QFT_REALIZATION_MAP.md` for the no-go it
repairs).

---

## 2. Result A — the coproduct is coassociative (QFT-R1)

**Theorem** (`coproduct_resolved_stable_phi4_coassociativity_law`,
`Phi4StableCoproductCoassociativityLaw.lean`, public form of
`coproduct_resolved_stable_phi4_coassociative`):

$$\operatorname{assoc}\circ(\Delta_r^s\otimes\mathrm{id})\circ\Delta_r^s
  \;=\;(\mathrm{id}\otimes\Delta_r^s)\circ\Delta_r^s
  \qquad\text{as algebra homs } H\to H\otimes(H\otimes H).$$

**Unconditional**: no divergence-law hypotheses, no typeclass-instance arguments — the φ⁴
power-counting enters as the concrete *providable* `phi4DivergenceMeasureFamily`.

*Physics.* `Δᵣˢ` is a genuine (coassociative) coproduct: extracting subdivergences in two
nested stages is unambiguous. This is the prerequisite for a well-defined renormalization
group / Hopf structure.

---

## 3. Result B — the renormalization character convolution algebra

For any target commutative ℚ-algebra `B` and character `φ : H →ₐ[ℚ] B`:

- **Convolution** (`phi4CharacterConvolution`, `Phi4RegularizedCharacterConvolution.lean`):
  `(f ⋆ g) := m_B ∘ (f ⊗ g) ∘ Δᵣˢ`, built *counit-free* directly as an algebra hom.
- **Associativity** (`phi4CharacterConvolution_assoc`,
  `Phi4CharacterConvolutionAssociativity.lean`): `(f ⋆ g) ⋆ h = f ⋆ (g ⋆ h)`, obtained by
  pushing Result A through a triple-tensor evaluator (purely structural).
- **Counit** (`phi4StableCounit_left_law` / `_right_law`, `Phi4StableCounit.lean`):
  `(ε ⊗ id)∘Δᵣˢ = includeRight`, `(id ⊗ ε)∘Δᵣˢ = includeLeft`.
- **Unit** (`phi4CharacterConvolution_left_unit` / `_right_unit`,
  `Phi4StableConvolutionUnit.lean`): the two-sided convolution identity `η = e∘ε`.

*Physics.* The characters `H → B` form an **associative unital algebra under convolution**
— the arena in which the renormalized and counterterm characters live.

---

## 4. Result C — Rota–Baxter subtraction + the well-founded Bogoliubov recursion

- **Subtraction scheme** (`Phi4RotaBaxterSubtractionScheme`, `Phi4RotaBaxterSubtraction.lean`):
  a weight `−1` **Rota–Baxter operator** `R` on `B` (`R² = R`, `R 1 = 0`,
  `R(x)R(y) = R(R(x)y + xR(y) − xy)`) — the renormalization scheme's "pole projector". We
  prove `1 − R` is *also* weight `−1` Rota–Baxter, giving the pole/finite decomposition.
- **Bogoliubov recursion** (bodies 661a/661b): the prepared value, counterterm, and
  renormalized generator
  $$B_\phi(x)=\phi(X_x)+\!\!\sum_{F\in W'''}\!\!\phi_-(L_F)\,\phi(R_F),\quad
    \phi_-(x)=-R\!\left(B_\phi(x)\right),\quad
    \phi_+(x)=(1-R)\!\left(B_\phi(x)\right),$$
  defined by `WellFounded.fix` on a **generator rank** (internal-edge count,
  `stablePhi4GeneratorRank`).

**Termination is proved, not assumed** (`stableForestComponent_rank_lt`,
`Phi4StableBogoliubovRank.lean`): every W‴ forest *component* generator has strictly
smaller rank than the ambient. **Ownership separation** — the edge-completeness (fifth)
axis is the recursion-*term closure*; what carries the *well-foundedness* is the
`IsProperForest` **positive complement** `0 < |E(G)∖E(F)|` (the forest omits at least one
internal edge). This is the Lean-verified statement of *why Bogoliubov's `R̄`-operation
recursion terminates* for this carrier.

*Physics.* This is Bogoliubov's recursive subtraction (`R̄`-operation / BPHZ forest
formula) as a terminating recursion over the subdivergence poset, with the pole part
selected by a Rota–Baxter scheme.

---

## 5. Result D — the Connes–Kreimer Birkhoff factorization `φ₋ ⋆ φ = φ₊` (MAIN)

`φ₋, φ₊` are promoted to genuine unital ℚ-algebra **characters** via the
free-commutative-algebra universal property (`MvPolynomial.aeval`,
`Phi4StableBogoliubovCharacters.lean`).

**Theorem** (`phi4Bogoliubov_birkhoff_factorization`,
`Phi4StableBogoliubovFactorization.lean`):

$$\phi_-\star\phi \;=\; \phi_+ \qquad\text{as algebra homs } H\to B.$$

The generator identity — Result A/B's `convolution_of_graph`, the counterterm/quotient
weight bridge, Result C's explicit preparation, and `B_φ + φ₋ = φ₊` — **lifts to the whole
polynomial algebra by `MvPolynomial.algHom_ext` precisely because both sides are genuine
algebra homomorphisms**.

*Physics.* This is the **algebraic Birkhoff decomposition of renormalization** (Connes–
Kreimer): the renormalized character `φ₊` is the convolution of the counterterm character
`φ₋` with the (regularized) character `φ`. It is the central structural theorem of
Hopf-algebraic renormalization, here proved unconditionally for a concrete φ⁴₄ Hopf
algebra and machine-checked.

---

## 6. Result E — the carrier-support renormalization discrepancy (NEW)

Take the concrete 12-edge φ⁴ graph `phi4CarrierGapAmbient` (call it **Figure 1**), which
witnesses the strict inclusion `W‴ ⊊ W″` — its marginal outer forest is leg-saturated
(`∈ W″`) but dropped by the edge-completeness axis (`∉ W‴`). Instantiate the genuine CK
weight `w(F) = φ₋(L_F)·φ(R_F)`.

**Theorem** (`phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector`,
`Phi4CarrierGapBogoliubovDroppedSector.lean`):

$$\underbrace{\Big[\phi_-(X)+\phi(X)+\!\!\sum_{F\in W''}\!\!w(F)\Big]}_{\text{broader-support value}}
  \;-\;\phi_+(X)
  \;=\;\sum_{F\in W''\setminus W'''} \phi_-(L_F)\,\phi(R_F),$$

with the honest numerical criterion (`phi4CarrierGap_bogoliubov_difference_of_isolated_marginal`):
if the marginal weight `w(F_{Fig1}) ≠ 0` and the rest of the dropped sector cancels (both
**explicit hypotheses**, never assumed away), the two renormalized values differ.

*Physics.* A change in the **admissible-forest support** of the coproduct (which
subdivergences one declares admissible) **propagates exactly** to the renormalized
amplitude; the difference is a sum of genuine counterterm-times-cograph contributions over
the dropped forests, and it is a real numerical difference precisely when that sector does
not cancel. This is a scheme-/prescription-dependence statement at the level of the CK
formula — not a bookkeeping artifact — and it is fully formal.

*(This is the result with the least classical antecedent; it is the natural "new physics
observation" a math-physics referee will look for, and it is exactly what the Figure-1
counterexample was engineered to make precise.)*

---

## 6bis. Result F — the witness layer (non-vacuity, symmetric primes)

The universal theorems above are certified **non-vacuous** by a second concrete witness: an
**8-edge φ⁴ vacuum graph** containing a **one-loop four-point bubble subdivergence**
(`phi4BubbleAmbient` / `phi4BubbleInner`; `V = 4`, `E = 8`, `L = 5`, bubble `ω = 0` marginal).
*The vacuum choice is deliberate*: with no external legs, this is the minimal configuration whose
cograph edges never have both endpoints inside the bubble, so **edge-completeness (the W‴ fifth
axis) holds automatically** — the exact inverse of Figure 1's engineered failure.

Two theorems, in **symmetric pairs** with the universal statements:

* **Thm 5′ — the coproduct is non-primitive** (`coproduct_resolved_stable_phi4_bubble_not_primitive`):
  the bubble forest enters W‴, the forest sum is nonzero (evaluated to `|W‴| > 0` by the all-1
  character through the tensor evaluator — cancellation-free), hence
  `Δᵣˢ(X_G) ≠ X_G ⊗ 1 + 1 ⊗ X_G`. A primitive coproduct satisfies coassociativity *trivially*;
  Thm 5′ is what certifies Result A as non-trivial content.
* **Thm 2′ — the nested-completion obstruction is inhabited**
  (`exists_nested_completion_obstruction`): the nested copy of the bubble on its own boundary
  completion inherits the straddling edge `e2 (0–2)`, and on this concrete configuration the naive
  nested completion **provably differs** (as a resolved class) from the root-relative one — the
  no-go (the paper's obstruction theorem) *occurs*, it is not a statement about an empty
  hypothesis. Notably **Figure 1 provably cannot witness this** (`phi4CarrierGap_inheritedOuter = 0`).

**The two figures divide the labor** (the paper needs exactly two):

| Figure | Graph | Channel | Role |
|---|---|---|---|
| Figure 1 | `phi4CarrierGapAmbient` (12 edges) | **hidden** (`h03`,`h14`) | negative: `W‴ ⊊ W″`, the dropped-sector discrepancy (Result E, §5 of the paper) |
| Figure 2 | the bubble (8 edges) | **inherited** (`e2`) | positive, double duty: the naive-completion failure *occurs* (§2.2) AND the coproduct actually computes a forest term (§3) |

---

## 7. Honest scope — what is and is not claimed

**Proved (unconditional, axiom-clean).** Results A–F above — A–E bundled publicly as
`phi4StableCK_renormalization_settlement` (`Phi4StableRenormalizationSettlement.lean`), the
witness layer F exported as `paper_thm2'` / `paper_thm5'` (`PaperMainTheorems.lean`).

**Open — the antipode frontier (deliberately not in this work).**
- the antipode `S_H` of `H` (needs connected grading + reduced-coproduct rank descent +
  recursion over the whole polynomial algebra);
- the convolution-inverse representation `φ₋ = φ ∘ S_H` (so far `φ₋` is defined by the
  Bogoliubov recursion, and `φ₋ ⋆ φ = φ₊` is proved directly, *without* an antipode);
- bundled `Bialgebra` / `HopfAlgebra` typeclass instances;
- a concrete momentum-space / dimensional-regularization evaluator inhabiting the
  Rota–Baxter socket (here `R`, `φ` are inputs; no Feynman integral is constructed);
- the *unconditional* nonvanishing of the Figure-1 weight (always a hypothesis).

Stating this boundary sharply is part of the contribution: the Birkhoff factorization is
obtained **without** the antipode, via the terminating Bogoliubov recursion and the
Rota–Baxter structure.

---

## 8. Verification methodology (the rigor guarantee)

- **Kernel-checked.** Every theorem is verified by the Lean 4 kernel; `#print axioms`
  reports `[propext, Classical.choice, Quot.sound]` for each headline (no `sorry`, no
  `admit`, no `native_decide`/`Lean.ofReduceBool`, no project axiom).
- **No hidden power-counting.** The φ⁴ superficial-degree valuation is a concrete
  *providable* instance; the QFT-R1/R2 chain carries **no divergence-law hypotheses** and
  **no typeclass-instance arguments** in its statements.
- **Type-discipline invariants.** No forbidden divergence-invariance class appears in any
  declaration *type* (checked by scanning every `#check @` printed type); no public
  `HEq` / `cast` / graph-data `▸`. The whole QFT-R1+R2 chain introduces **one** new
  `structure` (`Phi4RotaBaxterSubtractionScheme`) and **zero** new `class` / global
  `instance`.
- **Reproducible.** `lake exe cache get && lake build` compiles the development; any
  reviewer can re-run `#print axioms` on the named theorems.
- **One-build ledger + stable façade.** `Phi4StableChainLedgerAudit.lean` is a single audit
  module that `#check @`s every headline by its exact name (a rename fails the build) and
  `#print axioms` it, with the theorem → source file → introducing-commit table; and
  `PaperMainTheorems.lean` (`namespace GaugeGeometry.QFT.Paper`) re-exports the paper's main
  theorems under stable names `paper_thm1 … paper_thm7` + the primed witness layer
  `paper_thm2'` / `paper_thm5'`. A referee needs exactly two files.

---

## 9. Positioning for a mathematical-physics venue

**Framing.** Lead with the *physics/mathematics* result (Connes–Kreimer Birkhoff
decomposition realized concretely for φ⁴₄ + the carrier-support dependence theorem), and
present **full machine verification as the rigor guarantee**, not as the subject. A pure
"formalization" framing invites the "why formalize known mathematics" desk-reject; a
math-physics framing asks instead: *here is a concrete, complete, and (for Result E) new
statement about Hopf-algebraic renormalization, and it is certified beyond doubt.*

**Related work to cite.**
- Connes, Kreimer — *Renormalization in QFT and the Riemann–Hilbert problem I–II*
  (*Comm. Math. Phys.* 210 (2000), 216 (2001)); Kreimer — Hopf algebra of rooted trees
  (*Adv. Theor. Math. Phys.* 1998).
- Ebrahimi-Fard, Guo, Kreimer — Rota–Baxter algebras and the Birkhoff decomposition /
  BPHZ (*J. Phys. A* 2004; *Comm. Math. Phys.* 2004).
- Bogoliubov–Parasiuk, Hepp, Zimmermann — the BPHZ forest formula (background for
  Results C/E).
- (Prior formal work on Hopf algebras of trees / this repository's CK layer, for the
  formalization lineage.)

**Candidate venues (math-physics, receptive to rigorous/structural results).**
- *Letters in Mathematical Physics* — structural results with a clear statement; good fit
  for Results D+E as a focused paper.
- *Annales Henri Poincaré* — renormalization / Hopf-algebraic QFT is in scope.
- *Journal of Mathematical Physics* — broad, accommodates the full A–E development.
- *Communications in Mathematical Physics* — the highest bar; realistic only if Result E's
  novelty is foregrounded and the exposition is self-contained.
- (*Reviews in Mathematical Physics* / *J. Phys. A: Math. Theor.* as alternates.)

**Recommended paper shape (for the pivot).** A focused paper whose **headline is Result D
(Birkhoff factorization, concrete + verified) and Result E (carrier-support dependence,
new)**, with Results A–C as the necessary structural scaffolding, Result F as the witness
layer, and §8 as a short "machine-verification" section. Suggested working title (fixed by the
P2 scope audit, `P2_BRIDGE_AND_SCOPE_AUDIT.md` — more than a coproduct paper, short of a full
Hopf-algebra paper; the antipode is QFT-R3 future work):

> *A concrete, machine-verified Connes–Kreimer Birkhoff factorization for φ⁴₄, and the
> exact forest-support dependence of the renormalized amplitude.*

**The façade IS the table of contents.** `PaperMainTheorems.lean`'s sequence is the paper's
narrative spine:

> Thm 1 (early quotienting fails) → Thm 2 (naive completion fails) → **Thm 2′ (it actually
> happens)** → Thm 3 (the stable repair) → Thm 4 (the bijection) → Thm 5 (coassociativity) →
> **Thm 5′ (the coproduct is non-trivial)** → Thm 6 (Birkhoff `φ₋ ⋆ φ = φ₊`) → Thm 7 (changing
> the carrier changes the value)

with exactly **two figures** (Result F's table): Figure 1 = the 12-edge hidden-channel
counterexample (→ Thm 7, §5), Figure 2 = the 8-edge bubble (→ Thm 2′ in §2.2 AND Thm 5′ in §3).

**Framing decision (P2 bridge audit).** The abstract resolved-CK layer (R-6c, modulo the CK
divergence typeclasses) is *prior context in the same repository*; the φ⁴ development is a
**self-contained concrete realization** — the middle/maximal "bridge" to the abstract interface
is deliberately NOT built (the carriers and coproducts genuinely differ; that difference is
Result E). See `P2_BRIDGE_AND_SCOPE_AUDIT.md`.

---

## 10. Theorem index (paper-ready, verified names)

| # | Result | Lean theorem | File |
|---|---|---|---|
| A | coproduct coassociativity | `coproduct_resolved_stable_phi4_coassociativity_law` | `Phi4StableCoproductCoassociativityLaw.lean` |
| B1 | convolution associativity | `phi4CharacterConvolution_assoc` | `Phi4CharacterConvolutionAssociativity.lean` |
| B2 | counit laws | `phi4StableCounit_left_law` / `_right_law` | `Phi4StableCounit.lean` |
| B3 | convolution unit laws | `phi4CharacterConvolution_left_unit` / `_right_unit` | `Phi4StableConvolutionUnit.lean` |
| C1 | Rota–Baxter vessel (`1−R` also RB) | `Phi4RotaBaxterSubtractionScheme.finitePart_rotaBaxter_weight_neg_one` | `Phi4RotaBaxterSubtraction.lean` |
| C2 | recursion termination (rank descent) | `stableForestComponent_rank_lt` | `Phi4StableBogoliubovRank.lean` |
| C3 | Bogoliubov recursion unfolding | `phi4BogoliubovCountertermGen_eq` / `phi4BogoliubovPreparationGen_eq` | `Phi4StableBogoliubovRecursion.lean` |
| D | **Birkhoff factorization** `φ₋ ⋆ φ = φ₊` | `phi4Bogoliubov_birkhoff_factorization` | `Phi4StableBogoliubovFactorization.lean` |
| E1 | renormalized = forest formula | `phi4CarrierGap_renormalizedCharacter_eq_forestFormula` | `Phi4CarrierGapBogoliubovDiscrepancy.lean` |
| E2 | **dropped-sector identity** | `phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector` | `Phi4CarrierGapBogoliubovDroppedSector.lean` |
| E3 | numerical criterion | `phi4CarrierGap_bogoliubov_difference_of_isolated_marginal` | `Phi4CarrierGapBogoliubovDroppedSector.lean` |
| F1 | **coproduct non-primitive** (Thm 5′; bubble ∈ W‴, forest sum ≠ 0) | `coproduct_resolved_stable_phi4_bubble_not_primitive` | `Phi4BubbleWitnessNonPrimitive.lean` |
| F2 | **∃-no-go inhabited** (Thm 2′; nested completion provably differs) | `exists_nested_completion_obstruction` | `Phi4BubbleNestedObstruction.lean` |
| — | public settlement (A/D/E bundled) | `phi4StableCK_renormalization_settlement` | `Phi4StableRenormalizationSettlement.lean` |
| — | paper façade (`paper_thm1 … thm7`, `thm2'`, `thm5'`) | `GaugeGeometry.QFT.Paper.*` | `PaperMainTheorems.lean` |
| — | one-build theorem ledger (names + axioms + commits) | — | `Phi4StableChainLedgerAudit.lean` |

---

*Status: P0 (ledger) / P1 (façade, non-vacuity, no-go↔repair pairing) / P2 (bridge audit,
scope/title, novelty) are DONE. Next step: choose the venue (recommend Letters in Mathematical
Physics or Annales Henri Poincaré) and draft the paper along the façade's spine — Results D+E
headline, A–C scaffolding, F as the witness layer, two figures.*
