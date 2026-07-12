import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterNonempty
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestBlockBijection

/-!
# R-6c-body-245 — selected-outer filtered membership: the new root (domain correction, PROVED)

Two-hundred-and-forty-fifth genuine-body step — the **domain correction** for the selected-outer carrier membership.
Body-242 found the total leaf `ResolvedForwardMapCoherenceSupply.selectedOuter_mem : ∀ {G} s, selectedOuterRawOf s ∈
D.carrier G` (`ForwardMapCoherence.lean:72`) is **false at the all-right split `p_R`** (`selectedOuterRawOf p_R = ∅`).
This body plants a **new root** stated on the consumer's actual filtered domain — `p ∈ forestChoiceCarrier A` — so the
false total hypothesis is never assumed.  It is NOT an adapter from the old total supply (which would keep the false
assumption); it is an independent supply.

## The new root

```lean
structure ResolvedSelectedOuterFilteredMemSupply (D) where
  selectedOuter_mem : ∀ {G} A p, p ∈ forestChoiceCarrier A → selectedOuterRawOf ⟨A, p⟩ ∈ D.carrier G
```

matching exactly the filtered shape of the proved `selectedOuterRaw_isNonempty_of_mem_forestChoiceCarrier` (body-244).

## The filtered carrier-tagged map and its projection

`selectedOuterOfForestChoice` is the carrier-tagged selected outer on the **filtered sigma** `Σ A, {p // p ∈
forestChoiceCarrier A}` (the honest domain), with

```lean
(selectedOuterOfForestChoice F q).1 = selectedOuterRawOf ⟨q.1, q.2.1⟩     -- rfl
```

mirroring `ForwardMapCoherenceSupply.selectedOuter_eq` (`ForwardMapCoherence.lean:83`): the carrier tag is only on the
filtered domain, while the raw forest `selectedOuterRawOf` remains the total helper.

## The reconnection to the sum consumer

`forestBlockDomFinset G = (D.carrier G).attach.sigma (fun A => forestChoiceCarrier A)`
(`ForestBlockBijection.lean:84`), so **every summand `q ∈ forestBlockDomFinset G` carries `q.2 ∈ forestChoiceCarrier
q.1`** (`Finset.mem_sigma`).  `mem_of_mem_forestBlockDomFinset` feeds the filtered root at exactly those summands —
the image-side sum consumer `ResolvedForestBlockBijectionSupply` (`ForestBlockBijection.lean:94`) already has this
`hq` in scope, so the new root reconnects there cleanly with no false total assumption.

## Migration boundary (deferred to 246+)

The following still speak of the total `selectedOuterOf` / `∀ s`; they either use only the **value** `(selectedOuterOf
q).1` (discharged by `rfl`, no membership — the quotient ambient-type sites) or must later gain an `hq :
q ∈ forestBlockDomFinset` hypothesis:

```text
value-only (no migration): ForwardSigmaInstantiation, ForwardQuotientAssembly, QuotientElementsRecovery,
  RemnantElementsRecovery, SummandFactorBundle, QuotientBody  — consume (selectedOuterOf q).1 by rfl.
needs hq (later): fwdMap (WitnessSplitConcrete.lean:82, the choke point), ForwardMapCoherenceSupply.selectedOuter_mem
  (ForwardMapCoherence.lean:72, the defect root leaf), mixed/forest_backward (WitnessSplitConcrete.lean:101),
  ResolvedWitnessSplitCoverSupply (WitnessSplitFromCover.lean:81), ResolvedBijectionProviderSupply
  (BijectionProvider.lean:73), leftSubgraph (LeftSubgraphConstructor.lean:161).
```

`p_R` is never applied in any live sum (the summand index `forestBlockDomFinset` excludes it; `EmptyPivot` carries the
all-right boundary cover-external), so the migration is a re-typing to the filtered domain, not new mathematics.

Per the HALT: the new root is defined (its `selectedOuter_mem` field is the honest filtered obligation, discharged
later by the certificate + the `isProper` conjuncts), the filtered map + `.1 = rfl` + the sum-consumer reconnection are
proved; no old total supply is used, and the migration boundary is enumerated, not migrated.  No facade, no flat term,
no `forgetHopf`.
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

/-- **R-6c-body-245 — the selected-outer filtered membership root.**  The honest, filtered-domain replacement for the
total (all-right-false) `ResolvedForwardMapCoherenceSupply.selectedOuter_mem`: carrier membership of
`selectedOuterRawOf ⟨A, p⟩` only for `p ∈ forestChoiceCarrier A`. -/
structure ResolvedSelectedOuterFilteredMemSupply (D : ResolvedCoproductProperForestData) where
  /-- The selected outer lies in the carrier on the filtered domain (`p ≠ p_R`, `p ≠ p_L`). -/
  selectedOuter_mem : ∀ {G : ResolvedFeynmanGraph}
    (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx),
    p ∈ forestChoiceCarrier A →
      (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf ⟨A, p⟩ ∈ D.carrier G

/-- **R-6c-body-245 — the carrier-tagged selected outer on the filtered sigma.**  Domain
`Σ A, {p // p ∈ forestChoiceCarrier A}` — the honest domain, carrying the filter membership as a subtype proof. -/
noncomputable def ResolvedSelectedOuterFilteredMemSupply.selectedOuterOfForestChoice
    (F : ResolvedSelectedOuterFilteredMemSupply D) {G : ResolvedFeynmanGraph}
    (q : Σ A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G},
      {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx //
        p ∈ forestChoiceCarrier A}) :
    {A' : ResolvedAdmissibleSubgraph G // A' ∈ D.carrier G} :=
  ⟨(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf ⟨q.1, q.2.1⟩,
    F.selectedOuter_mem q.1 q.2.1 q.2.2⟩

/-- **R-6c-body-245 — the filtered map's forest is the raw selected outer** (`rfl`).  The carrier tag is only on the
filtered domain; the raw forest stays the total helper. -/
theorem ResolvedSelectedOuterFilteredMemSupply.selectedOuterOfForestChoice_fst
    (F : ResolvedSelectedOuterFilteredMemSupply D) {G : ResolvedFeynmanGraph}
    (q : Σ A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G},
      {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx //
        p ∈ forestChoiceCarrier A}) :
    (F.selectedOuterOfForestChoice q).1
      = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf ⟨q.1, q.2.1⟩ :=
  rfl

/-- **R-6c-body-245 — the new root reconnects to the sum consumer.**  Every summand `q ∈ forestBlockDomFinset G`
carries `q.2 ∈ forestChoiceCarrier q.1`, so the filtered root supplies the carrier membership there — with no total
(all-right-false) hypothesis. -/
theorem ResolvedSelectedOuterFilteredMemSupply.mem_of_mem_forestBlockDomFinset
    (F : ResolvedSelectedOuterFilteredMemSupply D) {G : ResolvedFeynmanGraph}
    (q : ForestBlockDomType D G) (hq : q ∈ forestBlockDomFinset G) :
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q ∈ D.carrier G := by
  simp only [forestBlockDomFinset, Finset.mem_sigma] at hq
  exact F.selectedOuter_mem q.1 q.2 hq.2

end GaugeGeometry.QFT.Combinatorial
