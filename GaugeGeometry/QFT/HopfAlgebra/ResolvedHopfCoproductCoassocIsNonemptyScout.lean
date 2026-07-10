import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPositiveInternalEdges
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionMembershipAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterSubset

/-!
# R-6c-body-239 — `IsNonempty` scout: Y (region union) is viable via covering; X (selectedOuterRawOf) is BLOCKED (all-right empty)

Two-hundred-and-thirty-ninth genuine-body step, a scout of the fourth `IsProperForest` conjunct `IsNonempty A =
A.elements.Nonempty` (`ResolvedSubGraph.lean:627`) for the two constructed forests — the first *piece-specific*
conjunct (unlike the universal #1/#2).  Verdict: a sharp **asymmetry** — `Y` (the recovered-outer region union) is
provable via the body-173 covering, but `X` (`selectedOuterRawOf`) is **genuinely not unconditionally nonempty**: in
the all-right-primitive split both `leftOf` and `promotedOf` are empty.  Records both routes/obstructions.  Imports
238/173/subset to keep the map honest.

## The two routes (and why the discharge one is the frontier)

* **Route A (consumer)** — if the carrier-membership leaf is *given* (`selectedOuter_mem` 128 / `recovered_outer_mem`
  159) plus a `ResolvedCarrierProperProvider D`, then `IsNonempty` is a one-liner:
  `(P.carrier_isProperForest G A hmem).1` (`isNonempty_of_isProperForest`, `ResolvedSubGraph.lean:645`).  **But this is
  circular for the certificate discharge** — the membership is exactly what body-232/233's certificate `isProper`
  (whose first conjunct is `IsNonempty`) must *produce*.
* **Route B (discharge)** — prove `IsNonempty` from scratch, as a genuine certificate field.  This is the frontier.

## Y — VIABLE (via the body-173 covering, keyed on the domain outer)

* `z : ForestBlockCodType D G = (A : {A // A ∈ D.carrier G}) × …ForestIdx` (`ForestBlockBijection.lean:79`), so
  **`z.1.1 ∈ D.carrier G` is free** (it is `z.1.2`, the sigma subtype proof).  Hence `z.1.1.elements.Nonempty` via
  `(P.carrier_isProperForest G z.1.1 z.1.2).1` — **not circular** (`z.1.1` is the *input* outer, a real carrier member
  distinct from the union `Y` being built).
* `recovered_region_membership` (`RecoveredRegionMembershipAssembly.lean:107`) is a per-`γ` **membership IFF**, not an
  elements equality:
  `(γ ∈ leftResidual (fwdMap S q) ∨ γ ∈ rightRecovered (fwdMap S q) ∨ γ ∈ forestRecovered (fwdMap S q)) ↔ γ ∈ q.1.1.elements`.
  Its ⟸ direction transfers nonemptiness: a witness `γ ∈ q.1.1.elements` lands in one of the three regions, hence in
  `Y.elements` (via `union_elements` ×2 + `Finset.mem_union`).
* **Gaps to thread**: the covering RHS is `q.1.1.elements` (the *domain* outer via `fwdMap S q`), NOT the generic
  `z.1.1.elements` — the codomain outer is a separate component (`ForestBlockBijection.lean:77`).  So the route closes
  cleanly only over the forward image `z = fwdMap S q`, and needs (a) `ResolvedCarrierProperProvider D`, (b) the
  bundled `ResolvedRecoveredRegionMembershipAssemblySupply` (the three sector bridges,
  `RecoveredRegionMembershipAssembly.lean:93`), (c) the identification `z = fwdMap S q`.

## X — BLOCKED (`selectedOuterRawOf` can be EMPTY)

* `selectedOuterRawOf s = (leftOf s).union (promotedOf s) (cross s)` with `leftOf` / `promotedOf` **abstract supply
  fields** (`Promote.lean:50`); concrete `leftOf` is a filter (`LeftSelect.lean:70`), `promotedOf` a filter/image
  (`PromotedOf.lean:102`).  **No `leftOf_nonempty` / `promotedOf_nonempty` / `selectedOuterRawOf_nonempty` exists.**
* **In the all-right-primitive split** (every component picks `inl false`), `leftOf s` is empty AND `promotedOf s` is
  empty, so `selectedOuterRawOf s` is **empty** — `X.IsNonempty` is genuinely *false* for that raw split.
* **No covering**: `selectedOuterRawOf_vertices_subset` (`SelectedOuterSubset.lean:40`) is a `vertices ⊆ s.1.1.vertices`
  — the wrong direction for a lower bound; there is no `s.1.1 ⊆ selectedOuterRawOf` and no elements covering.
* `EmptyPivot.lean:19` records that `selectedOuterOf` never hits `∅` — but only *as a consequence of*
  `selectedOuter_mem` (`∅ ∉ D.carrier G`), i.e. Route A (circular for the discharge).

So discharging `X.IsNonempty` for the canonical carrier is not a piece-nonemptiness lemma but a **structural
obligation**: the all-right split must be excluded (or handled by the `EmptyPivot` machinery), because
`selectedOuterRawOf` is not a proper forest there — the certificate route for `selectedOuter_mem` (128) is therefore
*incomplete* on the all-right sector without that handling.

## Assessment and plan

* **body-240 target = `Y.IsNonempty`** (the viable one): a lemma reducing `Y.IsNonempty` to `q.1.1.elements.Nonempty`
  via `recovered_region_membership` (⟸) + `union_elements` + `Finset.mem_union`, with `carrier_isProperForest` on the
  domain outer `q.1.1` supplying the witness — threading the `ResolvedRecoveredRegionMembershipAssemblySupply` and the
  `z = fwdMap S q` identification.  Alternatively, a **generic** `union_isNonempty_left/right`
  (`A.IsNonempty → (A.union B _).IsNonempty` via `Finset.Nonempty.inl`) as the reusable infra first.
* **X.IsNonempty is deferred / is a structural obstruction** — record it: `selectedOuterRawOf` is empty on the
  all-right split; its nonemptiness needs the split excluded or `EmptyPivot` integration, not a piece lemma.  Do NOT
  target `X.IsNonempty` as a plain conjunct.

Per the HALT: no `IsNonempty` body is entered, no certificate field is proved; the exact `Y` route (covering +
carrier-proper on the domain outer + `fwdMap` identification) and the exact `X` obstruction (all-right empty, no
covering) are named.  This is a documentation / scout anchor (like body-235/237).  No declarations beyond this
docstring.  No facade, no flat term, no `forgetHopf`.
-/
