import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterFilteredMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocWitnessSplitConcrete
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardMapCoherence

/-!
# R-6c-body-248 — `fwdMap` filtered-domain migration scout: verdict (3) PROVIDER-RETYPE (shallow)

Two-hundred-and-forty-eighth genuine-body step, the migration map for making the carrier-tagged forward map use the
**filtered** subtype domain, so the live sum no longer references the retired total root
`ResolvedForwardMapCoherenceSupply.selectedOuter_mem : ∀ s` (false at `p_R`).  Verdict: **(3) PROVIDER-RETYPE, shallow
variant** — the sum consumer and provider maps-to laws are already filtered, but the witnessSplit round-trip *laws* are
total and keep the total root alive; they must be restated over the finsets.  Crucially every restated proof ports
**verbatim** by proof irrelevance.  Imports 245/witnessSplit/coherence to keep the map honest.

## Where the total membership is consumed (the single point)

`fwdMap S s = ⟨(S.Forward.imageSupply G).selectedOuterOf s, S.quotientForest s⟩` (`WitnessSplitConcrete.lean:82`) reads
an *already-tagged* `selectedOuterOf s`.  The total root is consumed one level up, when `imageSupply` is built:
`ResolvedForwardMapCoherenceSupply.imageSupply = resolvedConcreteSelectedOuterImageSupply D G C.selectedOuter_mem`
(`ForwardMapCoherence.lean:76`), `C.selectedOuter_mem : ∀ s` (`:72`).  `quotientForest` is membership-free
(`QuotientForest.lean:53`, depends only on `(selectedOuterOf s).1`, the raw forest by `rfl`).  So the sole total
consumption is the `.2` tag of `selectedOuterOf`.

## The sum consumer is already filtered

`ResolvedForestBlockBijectionSupply` (`ForestBlockBijection.lean:94-120`): **every** element-bearing field is guarded
by `hq : q ∈ forestBlockDomFinset G` / `hr : r ∈ forestBlockCodFinset G` — `toFun` (an *independent* field, not `fwdMap`
restricted), `toFun_mem`, `invFun_mem`, `left_inv`, `right_inv`, `summand_agree`.  The bijection is a `Finset.sum_bij'`
reindex (`:133`), not an `Equiv`.  `toFun_mem` already proves `∈ forestBlockCodFinset` from `hq`.  So a subtype
`fwdMapFiltered` slots into `toFun` cleanly; the codomain membership is already supplied and filtered.

## What keeps the total root alive: the witnessSplit round-trip laws

`witnessSplit z : ResolvedCoassocSplitChoice` (`WitnessSplitConcrete.lean:113`) has NO attached `∈ forestBlockDomFinset`
proof, and the round-trips are TOTAL:

```text
forward_witness  : ∀ z, fwdMap S (witnessSplit z) = z          (WitnessSplitConcrete.lean:117)
backward_witness : ∀ q, witnessSplit (fwdMap S q) = q          (:130)
```

plus their sources `ResolvedWitnessSplitConcreteData.mixed/forest_forward/backward` (`:94-105`) and the cover restatements
`ResolvedWitnessSplitCoverSupply.forward/backward_witness` (`WitnessSplitFromCover.lean:83-89`) — all `∀ z`/`∀ q`, no
`hq`, referencing `fwdMap S` / total `selectedOuterOf` directly.  Reusing them keeps the total root in the live path.

## The verbatim-reuse mechanism (proof irrelevance)

Because `(selectedOuterOfForestChoice ⟨q.1, ⟨q.2, hq'⟩⟩).1 = (selectedOuterOf q).1 = selectedOuterRawOf q` all by
`rfl` (body-245 `selectedOuterOfForestChoice_fst`; `ForwardMapCoherence.selectedOuter_eq`), and the two `.1 : {A // A ∈
carrier}` compare by `Subtype.ext` (proof irrelevance on the tag), one gets

```text
fwdMapFiltered ⟨q, hq⟩ = fwdMap S q     by Subtype.ext rfl.
```

Every `Sigma.ext` / HEq round-trip proof (bodies 193/200/203/204/206, `ForwardQuotientAssembly`) reads only `.1`
(rfl-equal) and never the proof-irrelevant `.2` tag — so **all port verbatim** under a subtype wrapper or an added `hq`.

## Blast radius (record/def level)

```text
RE-TYPE to filtered (∀ … ∈ finset) round-trip laws  [the Verdict-3 core]:
  ResolvedWitnessSplitCoverSupply.forward_witness / backward_witness      WitnessSplitFromCover.lean:83-89
  ResolvedWitnessSplitConcreteData.mixed/forest_forward/backward          WitnessSplitConcrete.lean:94-105
  witnessSplit / forward_witness / backward_witness (methods)             WitnessSplitConcrete.lean:113-132
  provider inverse laws mixed/forest_left_inv/right_inv discharge sites   WitnessSplitFromCover.lean:110-123
VALUE-SUBSTITUTION only (shape unchanged; total selectedOuterOf → filtered selectedOuterOfForestChoice):
  fwdMap (or add fwdMapFiltered)                                          WitnessSplitConcrete.lean:80-82
  ForwardMapCoherenceSupply.imageSupply / .selectedOuter_mem (retire)     ForwardMapCoherence.lean:72,76-79
  ResolvedCoassocSelectedOuterImageSupply.selectedOuterOf                 ImageSupply.lean:48
  SideSupply / provider toFun-mem/inv sites                               BijectionSideAssembly.lean:81-116, BijectionProvider.lean:75-111
NO CHANGE (already filtered, or value-only-by-rfl):
  ResolvedForestBlockBijectionSupply + toForestCarrierProperSupply        ForestBlockBijection.lean:94-141
  ForwardQuotientAssembly, ForwardSigmaInstantiation, QuotientElementsRecovery,
    RemnantElementsRecovery, SummandFactorBundle, QuotientBody            (value-only (selectedOuterOf q).1 by rfl)
```

## The single minimal migration boundary

Replace the total `(S.Forward.imageSupply G).selectedOuterOf q` with body-245's filtered
`F.selectedOuterOfForestChoice ⟨q.1, ⟨q.2, hq'⟩⟩` (`SelectedOuterFilteredMem.lean:94`), `hq'` from
`mem_of_mem_forestBlockDomFinset` (`:117`), at the `fwdMap` definition.  Everything downstream already carries `hq`;
the only remaining obligation is re-quantifying the witnessSplit cover round-trip laws over the finsets.  **No dummy /
total carrier element is needed outside the domain** — `p_R` is never applied in any live sum, and `EmptyPivot` carries
the all-right boundary cover-external.

## Assessment and plan

* **Verdict (3), shallow**: the round-trip *laws* must be restated over the finsets to remove the total-root reference,
  but every restated proof ports verbatim by proof irrelevance (`fwdMapFiltered q = fwdMap q` by `Subtype.ext rfl`).
* **body-249 first step**: introduce `fwdMapFiltered : FilteredForestBlockDom D G → ForestBlockCodType D G` via
  `selectedOuterOfForestChoice`, and prove the single bridge `fwdMapFiltered ⟨q, hq⟩ = fwdMap S q` by `Subtype.ext rfl`.
  That bridge lets the subsequent finset-quantified round-trip laws reuse the existing total proofs; defer the
  cover-law requantification to body-250.

Per the HALT: no migration is performed; the verdict, the blast radius, the minimal cut, and the body-249 step are
named, and the no-dummy-element invariant is confirmed.  This is a documentation / scout anchor (like body-224/242).
No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
