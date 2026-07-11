import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocEmptyPivot
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestCoreIndex

/-!
# R-6c-body-242 — selected-outer nonemptiness scout: verdict (c) THREADING OBSTRUCTION (`selectedOuter_mem` is total; the p_R exclusion lives only at the sum)

Two-hundred-and-forty-second genuine-body step, the audit that decides the whole `selectedOuter_mem` (body-128) route.
Body-239 found `X = selectedOuterRawOf s = (leftOf s).union (promotedOf s)` is **empty on the all-right split** `p_R`
(every component tagged `inl false`), so `X.IsNonempty` — and hence `selectedOuter_mem : ∀ s, X ∈ D.carrier G` — is
genuinely false at `s = p_R` for the canonical carrier (`∅ ∉ D.carrier G`).  The audit asks whether `p_R` is excluded
upstream.  **Verdict: (c) THREADING OBSTRUCTION** — the exclusion exists but is decoupled from the total obligation.

## The three findings

* **`selectedOuter_mem` is TOTAL (`∀ s`), not filtered.**  `SelectedOuterBridge.lean:62` /
  `SelectedOuterMem.lean:50` state `selectedOuter_mem : ∀ s, selectedOuterRawOf s ∈ D.carrier G` over every
  `s : ResolvedCoassocSplitChoice D G`; it feeds the **total** map `selectedOuterOf : ResolvedCoassocSplitChoice D G →
  {A // A ∈ D.carrier G}` (`SelectedOuterBridge.lean:80`), built before/independently of any sum.  `p_R` is inside
  this quantifier.
* **The consumer SUM excludes p_R.**  `forestChoiceCarrier A` (`ForestCoreIndex.lean:70`) is
  `(…pi…).filter (fun p => p ≠ (fun _ _ => Sum.inl false) ∧ p ≠ (fun _ _ => Sum.inl true))` — the first conjunct is
  `p ≠ p_R` (all-right), the second `p ≠ p_L` (all-left).  The image-side sum is indexed over
  `forestBlockDomFinset = (D.carrier G).attach.sigma forestChoiceCarrier` (`ForestBlockBijection.lean:84`), so every
  *summand* carries `q.2 ≠ p_R` via `Finset.mem_filter`.  `p_R` is **not** a real summand.
* **`EmptyPivot` relocates p_R cover-external, it does not discharge it.**  `EmptyPivot.lean:13-19` takes
  `∅ ∉ D.carrier G` as a canonical-model input (not re-derived) and concludes the total `selectedOuterOf` can never
  return `∅`; `resolved_output_boundaries_external` (`:84`) carries the all-right boundary as a **cover-external** term.
  There is no `∅`-fiber inside the cover (`:41-44`).  Not circular (it never re-derives `≠ ∅` from `selectedOuter_mem`).

## The exact obstruction

`selectedOuter_mem` is stated totally and consumed at construction of the **total** `selectedOuterOf`, *before* — and
decoupled from — the `forestChoiceCarrier`-filtered sum that is the only place `q ≠ p_R` becomes available.  At
`s = p_R`: `leftOf p_R` and `promotedOf p_R` are both empty (all tags `inl false`), so `selectedOuterRawOf p_R = ∅`,
and `∅ ∉ D.carrier G` — the total obligation is genuinely **false at p_R**, and the filter that would remove it cannot
be threaded into a `∀ s` statement.  (`mixed_ne_pR`, body-151 `RecoveredChoiceMembership.lean:125`, gives `≠ p_R` only
for reconstructed *mixed* codomain elements, not for a generic `s` reaching this obligation.)

## The `X.IsNonempty` route once restricted (body-243)

Under a domain restricted to `forestChoiceCarrier` (so `s ≠ p_R` is in scope), `X.IsNonempty` discharges cleanly, and
— pleasant surprise — **without any `promote_collapse` (body-188/189) floor**:

```text
s ≠ p_R (from Finset.mem_filter on forestChoiceCarrier, ForestCoreIndex.lean:73)
  → ∃ γ ∈ s.1.1.elements with tag ≠ inl false, i.e. inl true OR inr B
  → inl true : γ ∈ (leftOf s).elements    (leftOf_elements = filter, LeftSelect.lean:70) → leftOf nonempty
     inr B   : γ contributes to s.promotedElements = (promotedOf s).elements (promotedOf_elements, PromotedOf.lean:102)
              → promotedOf nonempty          (reduces to s.promotedElements.Nonempty — NO per-component promote_collapse)
  → selectedOuterRawOf s = (leftOf s) ∪ (promotedOf s) nonempty         (union_isNonempty_left/right, body-240)
```

Caveat: nonemptiness only removes the *one definite* `∅` counterexample; the residual `∈ D.carrier G` still needs the
canonical sub-forest-closed carrier (`SelectedOuterMem.lean:11-19`), the separately-supplied floor (the certificate
`isProper` other conjuncts + `recovered_eq`, body-232/233).

## Assessment and plan

* **Verdict (c): the p_R exclusion exists at the sum but is not threadable into the total `∀ s` obligation.**  It is
  NOT verdict (b) (p_R is not a real summand — EmptyPivot carries it cover-external), and NOT (a) (the obligation is
  not restricted).
* **body-243 target**: re-state the selected-outer membership on the **forest block** — `∀ A, ∀ p ∈ forestChoiceCarrier
  A, selectedOuterRawOf ⟨A, p⟩ ∈ D.carrier G` (equivalently give `selectedOuterOf` the domain `forestBlockDomFinset`) —
  so each summand's `p ≠ p_R` is in scope; then `X.IsNonempty` discharges via the route above (`leftOf` / `promotedOf`
  nonempty + `union_isNonempty`, no `promote_collapse`).  This is a **re-typing** of the obligation to match the
  consumer, paralleling the `recoveredOuter` forward-image restriction (body-241); the p_R boundary stays with
  `EmptyPivot`.

Per the HALT: no proof is entered; the verdict, the exact cycle (total `∀ s` vs filtered sum), and the body-243
re-typing target are named.  This is a documentation / scout anchor (like body-239).  No declarations beyond this
docstring.  No facade, no flat term, no `forgetHopf`.
-/
