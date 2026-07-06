import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredChoiceRoundTrip
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredQuotientRoundTrip

/-!
# R-6c-body-192 — round-trip HEq scout: the two heterogeneous leaves reduced to component/index facts

Hundred-and-ninety-second genuine-body step, a scout of the two remaining `HEq` round-trip leaves before attacking
them.  The audit fixed their exact type mismatches, their consumption, and the already-proved index transports, and
isolated the one fresh componentwise fact for the lighter leaf.

## The two `HEq` leaves (audit)

```text
backward_choice_heq  (body-164)  HEq (recoverChoice (fwdMap q)) q.2
   TypeA = (γ ∈ (unionOuter (fwdMap q)).1.elements.attach) → Bool ⊕ (D.supply γ.1.…).ForestIdx
   TypeB = (γ ∈ q.1.1.elements.attach)                     → Bool ⊕ (D.supply γ.1.…).ForestIdx
   same dependent-function shape over two DIFFERENT index Finsets (unionOuter(fwdMap q) vs q.1.1)

forward_quotient_heq (body-165)  HEq (quotientForest ⟨unionOuter z, recoverChoice z⟩) z.2
   TypeA = (D.supply ((selectedOuterOf ⟨unionOuter z,…⟩).1.contractWithStars …)).ForestIdx
   TypeB = (D.supply (z.1.1.contractWithStars …)).ForestIdx
   ForestIdx over two contract-with-stars graphs (differing base outer)
```

Both are consumed **raw** as the second argument of `Sigma.ext` (body-147 `RegionRoundTripReduction`), paired with the
already-proved outer `Eq` as the first argument:

* `backward_choice_heq` ↔ `backward_outer q : unionOuter (fwdMap q) = q.1` (from `recoveredOuter_partition`, PROVED);
* `forward_quotient_heq` ↔ `forward_outer z : selectedOuterOf ⟨unionOuter z,…⟩ = z.1` (from `selectedOuter_partition`,
  PROVED).

So the index transports are in hand; the `HEq`s are the only unfilled second components.

## backward is lighter — reduced to a componentwise `Eq`

At a common component `γ`, both `recoverChoice (fwdMap q) ⟨γ,_⟩` and `q.2 ⟨γ,_⟩` return the *same* type
`Bool ⊕ (D.supply γ.1.…).ForestIdx` (it depends only on `γ.1`).  So the `HEq` reduces — under the domain equality
`backward_outer` (via `Function.hfunext` / `heq_of_eq`, the flat-`Coassoc` pattern; there is no Resolved HEq helper)
— to the **homogeneous componentwise `Eq`**

```text
choice_component_eq : recoverChoice (fwdMap q) ⟨γ,_⟩ = q.2 ⟨γ,_⟩
```

whose content, by tag: `inl true` on `leftResidual` (body-152 `left_tag` + body-172 bridge), `inl false` on
`rightRecovered` (`right_tag` + body-170), `inr Bᵧ` on `forestRecovered` (`forest_tag` + body-171 + body-188
`recoverChoice_forest_eq`) — the two `inl` cases are covered by the region tags / sector bridges / body-173
trichotomy; the **only fresh** point is the `inr` value match `Bᵧ = q`'s original forest index (the choice-value
de-contraction round-trip).  `ResolvedRoundTripHEqDecompositionSupply` fields `choice_component_eq` as that reduced
leaf.

## forward is heavier — kept as a fielded `HEq`

`forward_quotient_heq` needs a full `ForestIdx`-over-contract-graph identity reconstructing `B = rightSurvivor ⊔
remnant` on the recovered choice — no homogeneous predecessor exists (`quotientForest` is defined only through
body-129's `union_eq` of survivor/remnant, not reduced to `z.2`).  It is kept here as the heavier fielded leaf.

## Assessment

`backward_choice_heq` first: field `choice_component_eq` (done here), then the next body assembles the `HEq` from it
+ `backward_outer` via `Function.hfunext` and closes the `inl` tags, leaving the single `inr` value fact.
`forward_quotient_heq` is deferred as the genuinely heavier quotient reconstruction.

Per the HALT: no `HEq` is proved here; the `Function.hfunext` assembly is not entered; the componentwise `Eq` is
fielded and the `inr` fresh fact recorded; the forward leaf stays a fielded `HEq`.

Landed:

* `ResolvedRoundTripHEqDecompositionSupply D S Region` — the backward componentwise `Eq` + the forward `HEq`;
* the audit of both leaves' type mismatches, transports, and the lighter/heavier assessment.

Scout / toolkit body (like body-186 / body-188).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-192 — the round-trip HEq decomposition supply.**  The backward-choice `HEq` reduced to a
homogeneous componentwise `Eq` (`choice_component_eq`), and the heavier forward-quotient `HEq` kept fielded. -/
structure ResolvedRoundTripHEqDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Backward, reduced: at a common component `γ`, the reconstructed choice of the forward image agrees with the
  original choice (homogeneous — both sides are `Bool ⊕ (D.supply γ.1.…).ForestIdx`). -/
  choice_component_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements),
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = q.2 γ (Finset.mem_attach _ _)
  /-- Forward, heavier: the reconstructed quotient of the recovered outer is the original quotient (heterogeneous —
  `ForestIdx` over two contract-with-stars graphs). -/
  forward_quotient_heq : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2

end GaugeGeometry.QFT.Combinatorial
