# φ⁴₄ QFT Realization — Formalization Map

*A compact, reader/paper-facing map of two campaigns: **QFT-R1** — a concrete
φ⁴₄ realization of a stable **boundary-resolved** Connes–Kreimer-style
coproduct in Lean 4, culminating in its **coassociativity** on the whole
polynomial algebra (§0–§6); and **QFT-R2** — the full **Connes–Kreimer
renormalization character theory** built on that coproduct: an
associative-unital character convolution, a well-founded Bogoliubov recursion,
genuine counterterm/renormalized characters, their **Birkhoff factorization
`φ₋ ⋆ φ = φ₊`**, and the Figure-1 dropped-sector CK-weight discrepancy (§7);
plus the **witness layer** (the bubble graph inhabiting both the nested-completion
no-go and the coproduct's non-primitivity) and the paper-facing façade/ledger (§8).
Companion to `CK_HOPF_FORMALIZATION_MAP.md` (the abstract Connes–Kreimer side)
and separated from it: the CK docs describe the abstract Hopf-algebra
formalization; this file describes the concrete φ⁴ coproduct and the
renormalization character theory built on the stable resolved carrier.*

All Lean names below are verified against the source.  Constructive body: no
`sorry` / `admit` / project axiom.  Every headline theorem is axiom-clean —
`#print axioms` shows exactly `[propext, Classical.choice, Quot.sound]`.

---

## 0. The public terminus

The campaign's final, downstream/paper-facing theorem
(`Phi4StableCoproductCoassociativityLaw.lean`, body-652):

```lean
theorem coproduct_resolved_stable_phi4_coassociativity_law :
    ((Algebra.TensorProduct.assoc ℚ ℚ ℚ
        StableResolvedPhi4HopfH StableResolvedPhi4HopfH StableResolvedPhi4HopfH).toAlgHom.comp
      (Algebra.TensorProduct.map coproduct_resolved_stable_phi4
        (AlgHom.id ℚ StableResolvedPhi4HopfH))).comp
      coproduct_resolved_stable_phi4
      = (Algebra.TensorProduct.map (AlgHom.id ℚ StableResolvedPhi4HopfH)
          coproduct_resolved_stable_phi4).comp
        coproduct_resolved_stable_phi4
```

i.e. the standard coassociativity square for `Δᵣˢ := coproduct_resolved_stable_phi4`:

$$\operatorname{assoc}\circ(\Delta_r^s\otimes \mathrm{id})\circ\Delta_r^s
  \;=\;(\mathrm{id}\otimes\Delta_r^s)\circ\Delta_r^s.$$

The internal terminus it re-states (body-651,
`Phi4StableCoproductCoassociativity.lean`):

```lean
theorem coproduct_resolved_stable_phi4_coassociative :
    stableCoassocLeft = stableCoassocRight        -- as algebra homs H →ₐ[ℚ] H ⊗ (H ⊗ H)
```

with the pointwise form `coproduct_resolved_stable_phi4_coassoc (p) :
stableCoassocLeft p = stableCoassocRight p`.

---

## 1. What is realized

* **Carrier.**  `StableResolvedPhi4HopfGen` — φ⁴-family connected-divergent,
  id-preserving *resolved graph classes* that also own a **stable
  boundary-ID certificate** (`StableResolvedBoundaryIds`).  The Hopf polynomial
  algebra is `StableResolvedPhi4HopfH := MvPolynomial StableResolvedPhi4HopfGen ℚ`.
* **Coproduct.**  `coproduct_resolved_stable_phi4 : H →ₐ[ℚ] H ⊗[ℚ] H`
  (`Phi4StableResolvedHopfCoproduct.lean`, body-629), the CK-style
  divergent-subforest coproduct, made explicit on a graph generator:
  `Δᵣˢ (X g) = (X g ⊗ 1 + 1 ⊗ X g) + stableForestSum G hSt`.
* **Theorem.**  `Δᵣˢ` is **coassociative** on the whole algebra (§0).

This is a *concrete realization*: the coproduct and its coassociativity are
built from actual φ⁴₄ Feynman-graph combinatorics (divergent subforests,
star-contractions, boundary-completed inner ambients), not from an abstract
Hopf-algebra axiom schema.

### Relationship to the abstract CK side

`CK_HOPF_*` documents the abstract Connes–Kreimer Hopf algebra and its
boundary-resolved carrier repair in general.  This campaign supplies the
**concrete φ⁴₄ instance of the coproduct** and proves *its* coassociativity
directly.  The two are companions on the same resolved-carrier idea, kept in
separate files because they are separate deliverables (abstract structure vs.
concrete φ⁴ coproduct + its coassociativity theorem).

---

## 2. The design pivot — why a *stable* carrier

The naive resolved carrier's forest-block round-trip is only an *orbit*
(mapPerm-class) equality, not a raw equality; forcing it raw would demand a
false dependent transport.  The recorded **no-go** (body-625) is a genuine
math-physics obstruction: a first-order-correct rigidification that is **not
idempotent under iteration** breaks coassociativity — the naive nested
completion re-encodes inherited boundary legs (even ids) while the root-direct
completion uses odd ids, and a `mapPerm`-invariant leg-id profile separates
them.

**Repair (bodies 626→640): rigidify once, and make the rigidification stable
under iteration.**  `stableLocalBoundaryCompletedGraph` carries inherited legs
*verbatim* (zero re-encode), so the inner ambient of a sub-forest is
judgmentally the same whether reached in one step or two.  On this stable
carrier every round-trip below is a genuine **raw** equality — no orbit
quotient, no dedup, exact component multiplicity — and no `cast`/`HEq`/graph-data
transport ever appears in a public declaration type.

---

## 3. Proof architecture — the arc (bodies 641 → 652)

The coproduct on a graph generator splits into a common "alpha" part plus a
residual sum; coassociativity reduces to a **bijection of the two residual
sums** that preserves the summand weight.

| Stage | What is built | Headline Lean name | File |
|---|---|---|---|
| Forward map | split-choice → raw inverse-codomain package | `stableForestBlockForward` | `Phi4StableSummandAgreement.lean` |
| Weight equality | branch weight = quotient-triple weight | `stableForestBlockForward_summand_agree` | `Phi4StableSummandAgreement.lean` |
| Sole obligation | bijectivity fixed as the one open `Prop` | `StablePhi4ForestBlockForwardBijective` | `Phi4StableFiniteSumOwnership.lean` (641) |
| Inverse (FOREST payload) | source-independent stable inner forest | `stableInvRecoveredInnerForestValue` | `Phi4StableRecoveredInnerForest.lean` (642) |
| Inverse function | residual-free recovered split choice | `stableRecoveredSplitChoice` | `Phi4StableRecoveredSplitChoice.lean` (643) |
| RIGHT inverse | `forward ∘ inverse = id` | `stableForestBlockForward_recoveredSplitChoice` | `Phi4StableForestBlockForwardInverse.lean` (646) |
| LEFT inverse | `inverse ∘ forward = id` | `stableRecoveredSplitChoice_forestBlockForward` | `Phi4StableForestBlockLeftInverse.lean` (647c) |
| Genuine Equiv | obligation discharged; Equiv issued | `stablePhi4ForestBlockEquiv` | `Phi4StableGenuineForestBlockEquiv.lean` (648) |
| Finite-sum reindex | the two residual sums coincide | `stableForestBlock_finiteSum_reindex` | `Phi4StableFiniteSumReindex.lean` (649) |
| Alpha bridge (I) | iterated coproducts, choice expansion, partition | `stablePureChoicePartition` | `Phi4StableCoassocAlphaBridge.lean` (650a) |
| Alpha bridge (II) | alpha normal forms; graph coassoc | `coproduct_resolved_stable_phi4_coassoc_of_graph` | `Phi4StableCoassocAlphaCompletion.lean` (650b) |
| Crown | whole-algebra coassociativity | `coproduct_resolved_stable_phi4_coassociative` | `Phi4StableCoproductCoassociativity.lean` (651) |
| Public law | standard coassociativity square | `coproduct_resolved_stable_phi4_coassociativity_law` | `Phi4StableCoproductCoassociativityLaw.lean` (652) |

The LEFT inverse was assembled in parts — parent recovery (647a,
`Phi4StableForestBlockInverseForwardParent.lean`), the ambient-free inner-element
image equality (647b-1, `Phi4StableForestBlockInnerElements.lean`), the aligned
inner forest + exact `Sum.inr` payload (647b-2,
`Phi4StableForestAlignedInnerForest.lean`), and the outer/forward reconciliation
(644/645a/645b, `Phi4StableForwardInverseOuter.lean` /
`Phi4StableForwardInverseForestRecontraction.lean` /
`Phi4StableForwardInverseForestReconciliation.lean`).

### The three keystones

1. **Bijection, not quotient** (648).  `stableForestBlockForward` is bijective
   on the *raw* carriers, so no ID-distinct occurrence is collapsed and no
   coefficient/multiplicity is changed.
2. **Weight preservation** (640).  Corresponding terms carry equal weights, so
   the bijection lifts to an equality of *weighted* sums (649, via
   `Finset.sum_bij'`).
3. **Common-part cancellation** (650b).  Both iterated coproducts expand to the
   *same* `stableCoassocCommonPart` plus their respective residual sum; the 649
   reindex identifies the residuals, and `abel` closes.

---

## 4. Discipline invariants (held across the whole arc)

* **Axiom-clean.**  Every headline theorem: `[propext, Classical.choice, Quot.sound]`.
  No `sorry` / `admit` / `native_decide` / project axiom.
* **No forbidden divergence classes** in any declaration *type*
  (`IsPermInvariantDivergence`, `IsIsoInvariantDivergence`,
  `IsAmbientInvariantDivergence`, `IsDivergencePreservedByContract`, and the two
  forest-contract variants).
* **No public `HEq` / `cast` / graph-data `▸`.**  The few dependent transports
  (owner alignment for the FOREST payload) are confined to `private` helper
  bodies; every public statement is homogeneous.
* **No cross-ambient subgraph equality.**  Sub-forest comparisons are made
  ambient-free at the boundary-completion (plain `ResolvedFeynmanGraph`) level.
* **No orbit quotient / no dedup.**  Exact component multiplicity is preserved.
* The correcting permutations `τ` are used *only* through their action on the
  finite visible support; the permutations themselves are never equated.

---

## 5. Honest scope boundary (QFT-R1)

**Proved.**  `coproduct_resolved_stable_phi4` is a coassociative coproduct
(algebra hom) on the whole algebra `StableResolvedPhi4HopfH`, realized from
concrete φ⁴₄ divergent-subforest combinatorics, axiom-clean.

**Established in QFT-R2 (§7 below).**  The **counit** `ε` (both counit laws), an
associative-unital **character convolution**, a well-founded **Bogoliubov
recursion**, genuine counterterm/renormalized **characters** `φ₋, φ₊`, and their
**Birkhoff factorization `φ₋ ⋆ φ = φ₊`** — all built on this coproduct, all
axiom-clean.

**Still out of scope (QFT-R3 frontier).**  The **antipode** `S_H`, the
convolution-inverse representation `φ₋ = φ ∘ S_H`, a bundled `Bialgebra` /
`HopfAlgebra` instance, a concrete momentum-space / dimensional-regularization
evaluator, and the *unconditional* nonvanishing of the Figure-1 weight.

---

## 6. Where to read more

* Full internal sprint log (body-by-body, newest first):
  `~/.claude/.../memory/qft-realization-progress.md`.
* Abstract Connes–Kreimer side: `CK_HOPF_FORMALIZATION_MAP.md` (reader-facing),
  `CK_HOPF_DEPENDENCY_GRAPH.md` (technical dependency map).
* Source: `GaugeGeometry/QFT/HopfAlgebra/Phi4Stable*.lean`.

---

## 7. QFT-R2 — the Connes–Kreimer renormalization character theory (bodies 653 → 665)

Building on the coassociative coproduct `Δᵣˢ` of §0–§6, the **QFT-R2** campaign realizes
the full Connes–Kreimer renormalization machinery for the concrete φ⁴₄ carrier and
proves the **Birkhoff factorization `φ₋ ⋆ φ = φ₊`** on the whole polynomial algebra —
unconditional, axiom-clean.

### 7.1 The carrier-gap counterexample (Figure 1; bodies 653–655)

A concrete **12-edge φ⁴ graph** (`phi4CarrierGapAmbient`) witnesses the strict inclusion
`W‴ ⊊ W″` of the two forest carriers (edge-complete W‴ inside leg-saturated W″): its
marginal outer forest sits in W″ but is *dropped* by W‴'s fifth (edge-completeness) axis.
The counterexample is fully formal — topology (support-connectivity + 1PI, native, no
`native_decide`), the exact hidden defect `{h03, h14}`, the superficial-degree reversal
(`ω(δ)=0 → root ω=−2`), and the carrier-membership difference — and it is lifted to a
formal indicator-vector coefficient change (`1 → 0`, body-654) and a scheme-parametric
evaluated difference `= ∑_{W″ ∖ W‴} amp(F)` (body-655), with `amp` a socket.

### 7.2 The character algebra (bodies 656–659)

| Piece | Headline Lean name | File |
|---|---|---|
| Figure-1 as a stable Hopf generator | `phi4CarrierGapStableGen` | `Phi4RegularizedFeynmanRule.lean` (656) |
| Regularized Feynman-rule character | `phi4RegularizedFeynmanRule` (`= aeval`) | `Phi4RegularizedFeynmanRule.lean` (656) |
| Counit-free character convolution | `phi4CharacterConvolution` (`= mul ∘ (f⊗g) ∘ Δᵣˢ`) | `Phi4RegularizedCharacterConvolution.lean` (657) |
| Convolution **associativity** | `phi4CharacterConvolution_assoc` | `Phi4CharacterConvolutionAssociativity.lean` (658) |
| Stable **counit** `ε` + laws | `phi4StableCounit_left_law` / `_right_law` | `Phi4StableCounit.lean` (659a) |
| Convolution **unit** `η` + identity laws | `phi4CharacterConvolution_left_unit` / `_right_unit` | `Phi4StableConvolutionUnit.lean` (659b) |

Convolution is built **counit-free** (a direct `AlgHom`, no `Coalgebra` instance), and its
**associativity** is obtained by pushing the §0 coassociativity through a triple-tensor
evaluator — purely structural, no generator/forest re-expansion. Together with the
two-sided unit `η` and the counit `ε` (`(ε ⊗ id) ∘ Δᵣˢ = includeRight`,
`(id ⊗ ε) ∘ Δᵣˢ = includeLeft`), the character space is an **associative unital**
convolution algebra.

### 7.3 The Rota–Baxter subtraction vessel + Bogoliubov recursion (bodies 660–661)

* **Subtraction vessel** (`Phi4RotaBaxterSubtractionScheme`, body-660). A weight `−1`
  Rota–Baxter operator `R` (`polePart`, ℚ-linear, `R² = R`, `R 1 = 0`) owns the pole part;
  `1 − R` is proved also weight `−1` Rota–Baxter, giving the pole/finite split.
* **Well-founded recursion** (bodies 661a/661b). The prepared value
  `B_φ(x) = φ(X x) + ∑_{F ∈ W‴} φ₋(L_F)·φ(R_F)`, counterterm `φ₋(x) = −R(B_φ(x))`, and
  renormalized `φ₊(x) = (1 − R)(B_φ(x))` are defined by `WellFounded.fix` on a **generator
  rank** (`stablePhi4GeneratorRank`, internal-edge count, class-well-defined). The
  load-bearing termination fact `stableForestComponent_rank_lt` proves every W‴ forest
  **component** generator has strictly smaller rank than the ambient — carried by
  `IsProperForest`'s **positive complement** (`0 < complementEdges.card`), *not* the fifth
  axis. **Ownership separation:** the fifth axis (edge-completeness) is the recursion-term
  *closure*; the positive complement is the *well-foundedness*.

### 7.4 The Birkhoff factorization crown (bodies 662–663)

* `φ₋, φ₊` are promoted to genuine unital ℚ-algebra **characters** via `MvPolynomial.aeval`
  (body-662), with the load-bearing `map_prod` left-aggregate bridge.
* **`φ₋ ⋆ φ = φ₊`** on the *whole* algebra (body-663,
  `phi4Bogoliubov_birkhoff_factorization`): the generator identity — 657's
  `convolution_of_graph` + 662's bridge + 661's explicit preparation + 662's
  `prep + counterterm = renormalized` — lifts by `MvPolynomial.algHom_ext` precisely because
  *both sides are genuine `AlgHom`s*. This is the formal Connes–Kreimer Birkhoff
  factorization core.

### 7.5 The Figure-1 renormalization discrepancy + public settlement (bodies 664–665)

The §7.1 dropped-sector socket is instantiated with the **genuine CK weight**
`w(F) = φ₋(L_F)·φ(R_F)`. The PAPER HEADLINE (body-664b) is the exact identity

$$\text{comparisonValue} - \phi_+(X_{\mathrm{gap}})
  = \sum_{F \in W'' \setminus W'''} \phi_-(L_F)\,\phi(R_F),$$

with an honest numerical criterion (nonzero dropped-sector, or an isolated marginal with
`w(Outer) ≠ 0` and the rest vanishing — both **explicit hypotheses**). The public
settlement (body-665, `phi4StableCK_renormalization_settlement`) bundles the Birkhoff law
and this discrepancy identity under one `S`, `φ`.

**The reviewer's answer.** The forest-support change (`W‴ ⊊ W″`) **propagates** to the CK
renormalization formula; the exact difference is the sum of genuine
counterterm-times-quotient weights over the dropped sector; numerical inequality follows
*precisely* when that sector does not cancel — not a bookkeeping defect, but the
renormalization-calculation consequence, formally proved.

### 7.6 Honest scope boundary (QFT-R2)

**Proved (unconditional, axiom-clean).** Stable coproduct coassociativity;
associative-unital character convolution + counit + unit; well-founded Bogoliubov
recursion (termination owned by Lean); genuine `φ₋, φ₊` characters; `φ₋ ⋆ φ = φ₊`; the exact
Figure-1 dropped-sector CK-weight identity + honest numerical criterion.

**Out of scope (QFT-R3 frontier).** The antipode `S_H`; the convolution-inverse
representation `φ₋ = φ ∘ S_H`; bundled `Bialgebra` / `HopfAlgebra` instances; a
momentum-space / dimensional-regularization evaluator inhabiting the Rota–Baxter socket;
the *unconditional* nonvanishing of the Figure-1 weight (always a hypothesis here). `S` and
`φ` are inputs; no concrete Feynman-rule integral is built.

Discipline invariants of §4 hold across QFT-R2 as well: every headline theorem is
`[propext, Classical.choice, Quot.sound]`; no forbidden divergence class in any declaration
type (checked by scanning every `#check @` printed type); no public `HEq` / `cast` /
graph-data `▸`; one new `structure` in the whole campaign (`Phi4RotaBaxterSubtractionScheme`,
body-660), zero new `class` / global `instance`.

Source: `GaugeGeometry/QFT/HopfAlgebra/Phi4{RegularizedFeynmanRule,
RegularizedCharacterConvolution, CharacterConvolutionAssociativity, StableCounit,
StableConvolutionUnit, RotaBaxterSubtraction, StableBogoliubovRank, StableBogoliubovRecursion,
StableBogoliubovCharacters, StableBogoliubovFactorization, CarrierGapBogoliubovDiscrepancy,
CarrierGapBogoliubovDroppedSector, StableRenormalizationSettlement}.lean` and the Figure-1
counterexample `Phi4WDoubleTriplePrime*.lean` / `Phi4ForestSupportDiscrepancy.lean` /
`Phi4ForestEvaluationDiscrepancy.lean`.

---

## 8. The witness layer + the paper-facing infrastructure (bodies 665a–665d, façade, ledger)

### 8.1 The bubble witness — non-vacuity of the coproduct AND of the no-go

The theorems of §0–§7 are universal; the witness layer makes their content **inhabited**. The
single witness is an **8-edge φ⁴ vacuum graph** `phi4BubbleAmbient` (vertices `{0,1,2,3}`, all
valence 4, no external legs, `L = E − V + 1 = 5`) containing a **one-loop four-point bubble
subdivergence** `phi4BubbleInner` on `{0,1}` (edges `{e0,e1}`, `ω = 0`, marginal). *The vacuum
choice is deliberate*: with no external legs, this is the minimal configuration whose cograph
edges never have both endpoints inside the bubble — so **edge-completeness (the W‴ fifth axis)
holds automatically**, the exact inverse of Figure 1's engineered failure.

| Body | Content | Headline |
|---|---|---|
| 665a | graph + raw geometry; the PASSING edge-completeness (`filter (both ∈ {0,1}) = {e0,e1}`) | `phi4BubbleInner_internalEdgeComplete` |
| 665b | native topology (explicit reachability, no `native_decide`) + CD certificates (ambient `ω = 4`, bubble `ω = 0`) | `phi4BubbleInner_forget_isConnectedDivergent` |
| 665c | **the payoff**: bubble forest `∈ W‴`; W‴ nonempty; `stableForestSum ≠ 0` via the all-1 character (`Eval = |W‴| > 0`, cancellation-free); **the coproduct is NON-PRIMITIVE**: `Δᵣˢ(X_G) ≠ X_G ⊗ 1 + 1 ⊗ X_G` | `coproduct_resolved_stable_phi4_bubble_not_primitive` |
| 665d | **the ∃-no-go**: the nested copy `phi4BubbleNested` on the bubble's boundary completion inherits the straddling edge `e2`, inhabiting body-625's obstruction | `exists_nested_completion_obstruction` |

**The pairing of the two witnesses.** Figure 1 (`phi4CarrierGapAmbient`, 12 edges) and the bubble
(8 edges) divide the labor exactly:

* **Figure 1 — the HIDDEN channel, the negative example.** Its outer forest is dropped by the
  fifth axis (`h03`/`h14`); its `inheritedOuter` is PROVED empty
  (`phi4CarrierGap_inheritedOuter = 0` — it *cannot* witness the nested no-go). It carries
  `W‴ ⊊ W″` and the dropped-sector renormalization discrepancy (§7.5).
* **The bubble — the INHERITED channel, the positive example.** It passes the fifth axis into W‴
  (non-primitive coproduct, 665c) *and* its nested copy inherits an outer boundary edge
  (∃-no-go, 665d). One graph does double duty.

### 8.2 The paper façade + the reproducible theorem ledger

* **`PaperMainTheorems.lean`** — one import point compressing the development to the paper's
  main theorems under stable names (`namespace GaugeGeometry.QFT.Paper`):

  | Paper name | Statement | Internal name |
  |---|---|---|
  | `paper_thm1_early_quotient_obstruction` | flat quotienting loses identity data | `flat{Edge,Leg}Retarget_not_injective` (axiom-FREE) |
  | `paper_thm2_naive_completion_obstruction` | naive completion not relabeling-stable | `nested_direct_singletonProfile_ne` |
  | `paper_thm2'_obstruction_inhabited` | the obstruction OCCURS on a real φ⁴ configuration | `exists_nested_completion_obstruction` (665d) |
  | `paper_thm3_stable_normalization` | root-relative completion idempotent | `stableBoundaryIterate_idempotent` |
  | `paperForestBlockEquiv` + `paper_thm4_multiplicity_preserving_correspondence` | genuine bijection + weight-preserving reindex | `stablePhi4ForestBlockEquiv` + `stableForestBlock_finiteSum_reindex` |
  | `paper_thm5_phi4_coassociativity` | coassociativity, unconditional | `coproduct_resolved_stable_phi4_coassociativity_law` |
  | `paper_thm5'_coproduct_non_primitive` | the coproduct is non-primitive on a real φ⁴ graph | `coproduct_resolved_stable_phi4_bubble_not_primitive` (665c) |
  | `paper_thm6_birkhoff_factorization` | `φ₋ ⋆ φ = φ₊` | `phi4Bogoliubov_birkhoff_factorization` |
  | `paper_thm7_carrier_support_discrepancy` | the dropped-sector CK-weight identity | `phi4CarrierGap_comparison_minus_renormalized_eq_droppedSector` |

  The **primed theorems are the witness layer, in symmetric pairs**: Thm 2 states the
  obstruction, Thm 2′ shows it occurs; Thm 5 states coassociativity, Thm 5′ shows the coproduct
  is non-primitive (a primitive coproduct would satisfy coassociativity trivially — 5′ is what
  certifies 5 as non-trivial content). Both primes ride the same bubble witness.

* **`Phi4StableChainLedgerAudit.lean`** — the single reproducible **theorem ledger**: building
  this one module `#check @`s (by exact name — a rename fails the build) and `#print axioms`
  the eight QFT-R1+R2 headlines, with the theorem → source file → introducing-commit table.
  One `lake build` re-verifies the whole claim.

Paper-support documents: `docs/paper/QFT_RESULTS_INVENTORY.md` (the results catalog framed for a
mathematical-physics readership) and `docs/paper/P2_BRIDGE_AND_SCOPE_AUDIT.md` (the abstract-CK
bridge audit — verdict: the φ⁴ development is a self-contained concrete realization, NOT an
instantiation of the abstract interface; the paper scope is "Birkhoff factorization +
forest-support dependence", with the antipode as the QFT-R3 frontier).

Release: **v2.0.0**, DOI `10.5281/zenodo.21765915`.
