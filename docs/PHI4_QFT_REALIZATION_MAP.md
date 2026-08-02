# φ⁴₄ QFT Realization — Formalization Map

*A compact, reader/paper-facing map of the **QFT-R1** campaign: a concrete
φ⁴₄ realization of a stable **boundary-resolved** Connes–Kreimer-style
coproduct in Lean 4, culminating in its **coassociativity** on the whole
polynomial algebra.  Companion to `CK_HOPF_FORMALIZATION_MAP.md` (the abstract
Connes–Kreimer side) and separated from it: the CK docs describe the abstract
Hopf-algebra formalization; this file describes the concrete φ⁴ coproduct built
on the stable resolved carrier and the theorem that it is coassociative.*

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

## 5. Honest scope boundary

**Proved.**  `coproduct_resolved_stable_phi4` is a coassociative coproduct
(algebra hom) on the whole algebra `StableResolvedPhi4HopfH`, realized from
concrete φ⁴₄ divergent-subforest combinatorics, axiom-clean.

**Not claimed here (out of scope / future work).**

* **counit / antipode / full `Bialgebra` / `HopfAlgebra` instance.**  Only the
  coproduct and its coassociativity are established; the remaining Hopf structure
  is a separate front and is *not* asserted.
* A formal instantiation of the abstract CK divergence typeclasses by this
  concrete coproduct — the broader QFT-R1 realization goal — beyond the
  coassociativity delivered here.

---

## 6. Where to read more

* Full internal sprint log (body-by-body, newest first):
  `~/.claude/.../memory/qft-realization-progress.md`.
* Abstract Connes–Kreimer side: `CK_HOPF_FORMALIZATION_MAP.md` (reader-facing),
  `CK_HOPF_DEPENDENCY_GRAPH.md` (technical dependency map).
* Source: `GaugeGeometry/QFT/HopfAlgebra/Phi4Stable*.lean`.
