import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandAgreeValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCarryingBlock

/-!
# R-6c-body-257 — factor-equality bypass scout: verdict (A), `selected` is packaging; the term equality is p_R-safe

Two-hundred-and-fifty-seventh genuine-body step, the audit that decides how `summand_agree_value` (body-254) is
canonically discharged and where the last migration boundary sits.  Verdict: **(A) BYPASS** — the generic
factor-equality theorem takes individual pieces (no `ResolvedSummandFactorBundle`, no `selected`, no total
`selectedOuterOf` in its type), all suppliable from `fwdMapFilteredValue`; the `selected` bundle is packaging, and the
term equalities are p_R-safe raw statements.  A thin B-caveat: one helper (`hL`) currently *bundles* the total
`selected` supply in its argument type (not its proof) and should be re-keyed to raw.

## The generic theorem takes pieces, not a bundle

`resolved_splitChoice_summand_agree_of_factor_eqs` (`ForestCarryingBlock.lean:68`) has signature
`(A' p A B) (hL hR hQ) : D.resolvedSplitChoiceTerm ⟨A', p⟩ = leftTerm A ⊗ (leftTerm B ⊗ rightTerm B)` — a one-line
alias of `resolved_mixed_summand_agree` (`MixedBoundaryBlock.lean:133`).  `A'`/`A` are `{A // A ∈ D.carrier G}`, `B` a
raw contract-graph `ForestIdx`; **no `ResolvedSummandFactorBundle` / `selected` / `selectedOuterOf` appears in its
type.**  `hL`/`hR`/`hQ` mention only `localLeftFactor` / `localRightFactor` / `leftTerm` / `rightTerm` on the raw
pieces — no tag, no `Forward`.

## All pieces come from `fwdMapFilteredValue` (no `Forward`)

```text
A' := q.1.1                         -- domain outer, {A // ∈ carrier} for free (ForestBlockDomType first Σ-slot)
p  := q.1.2                         -- the component choice
A  := (fwdMapFilteredValue F V q).1 -- codomain outer ⟨selectedOuterRawOf q.1, F.mem_of_mem_forestBlockDomFinset …⟩ (tag from F)
B  := (fwdMapFilteredValue F V q).2 -- = V.quotientForestRaw q.1 (contract-graph ForestIdx, value root)
```

`hR` (`QuotientForestTermFactors.lean:101`, `resolved_quotientForest_right_factor_eq_of_parts`) takes **no `S`**; `hQ`
is the value bundle's Forward-free `quot_eq`.  So the canonical discharge is a direct call — no `S`, no `.ofLegacy`.

## `selected` is packaging; the p_R falsity is confined to the inert tag

`ResolvedSummandFactorBundle.selected : ResolvedCoassocSelectedOuterImageSupply D G`
(`SummandFactorBundle.lean:130`) carries the **total** `selectedOuter_mem : ∀ s` (`SelectedOuterBridge.lean:62`) — the
p_R-failing obligation.  But in the summand algebra it is used **only** for `.1` (`= selectedOuterRawOf q`) and the raw
`leftSelection` / `promotedOf` data; the `.2` membership tag rides along as the `A` argument and is **never read** by
`hL` / `hR` / `hQ` or the conclusion (`leftTerm` / `rightTerm` project only `.1`).  So the term equality is **NOT false
at `p_R`** — only the carrier-tag construction is, and the value path never meets `p_R` (`FilteredForestBlockDom` ⊆
`forestChoiceCarrier = piCarrier \ {p_R, p_L}`, tag from `F`).

## Verdict and the last boundary

* **(A) BYPASS** — `summand_agree_value` is provable directly:
  ```lean
  summand_agree_value := fun q =>
    resolved_splitChoice_summand_agree_of_factor_eqs q.1.1 q.1.2
      (fwdMapFilteredValue F V q).1 (fwdMapFilteredValue F V q).2 hL hR hQ
  ```
  with `hR` from `resolved_quotientForest_right_factor_eq_of_parts` (`S`-free), `hQ` from the value bundle's `quot_eq`.
* **Thin B-caveat (re-key, not re-prove)** — the left-factor identity `hL` is currently produced by
  `resolved_selectedOuter_left_factor_eq_of_parts` (`LocalLeftFactorProduct.lean:104`), whose **argument type** bundles
  the total `S : ResolvedCoassocSelectedOuterImageSupply` (with the p_R-failing `selectedOuter_mem`), though its
  **proof** uses only `leftOf` / `promotedOf` / `hLdisj` (raw).  A raw-keyed variant producing
  `∏ localLeftFactor = resolvedForestLeftTerm (selectedOuterRawOf q)` from the raw selection data is the one re-keying
  needed — the **last migration boundary** (`ResolvedCoassocSelectedOuterImageSupply.selectedOuter_mem` reached via
  `ResolvedSummandFactorBundle.selected` and that helper's `S` argument).
* **NOT (C)** — the generic theorem's type has no carrier-tagged total selected map; no re-theorem is required.

The live class-block sum already bypasses the total `selected` bundle (`ForestCarryingBlock.lean:196`,
`ForestBlockMapCombiner.lean:183/206`, `MixedBoundaryBlock.lean:256` all pass `A' := q.1`, `A := (toFun q).1`,
`B := (toFun q).2` + fielded factor eqs); the `ResolvedSummandFactorBundle` / `toSummandBundle` path (with total
`selected`) is only the legacy record the `.ofLegacy` migration-checks compare against.

Per the HALT: no proof is entered; the verdict (A + thin B), the exact canonical discharge call, and the last boundary
(the `hL` helper's `S`-argument / `selectedOuter_mem`) are named.  This is a documentation / scout anchor (like
body-248).  No declarations beyond this docstring.  No facade, no flat term, no `forgetHopf`.
-/
