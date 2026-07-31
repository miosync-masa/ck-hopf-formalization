import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeCorrectedQuotientForest

/-!
# QFT-R1-body-617 — corrected forest-block reconciliation: geometric FOREST round-trip is now RAW; the whole `Equiv` is a documented frontier

Body-616 built `phi4WTriplePrime_inv_correctedForestComponent O` whose raw round-trip
`phi4WTriplePrime_inv_correctedForestComponent_roundtrip : correctedForestComponent O = δ.1` is a genuine
raw `Eq` (via `ResolvedFeynmanSubgraph.ext` on three raw field equalities, ZERO `HEq` / `cast`), with
multiplicity EXACTLY preserved.  This body reconciles that inverse-side corrected component with the
forward-side recovered occurrence owner (body-614) THROUGH THE COMMON RAW TARGET COMPONENT, per the
componentwise-correction principle (CK body-454/489): each FOREST occurrence is corrected by its OWN
`reconTau`; NO global `τ`, NO orbit quotient, NO fabricated `HEq`.

## What closes cleanly here (genuine, axiom-clean, non-fabricating)

* **Step 1 (geometric FOREST recovery, RAW).**  `phi4WTriplePrime_forestBlock_correctedForestRecovery_raw`:
  for any recovered forest occurrence `O` over `z` / `δ`, the body-616 corrected component EQUALS the target
  quotient component `δ.1` as an ordinary `Eq` (both inhabit the SAME fixed quotient ambient
  `Q := z.1.1.contractWithStars (starOf G z.1.1)`).  This is the exact UPGRADE of body-615's RED-LINE
  obstruction: what body-615 could only close up to the correcting permutation `τ`
  (`..._forestRecovery_upToPerm`, `..._classLevel`) is now a RAW component equality — the geometric part of
  body-614's FOREST obligation, discharged with NO `HEq` / `cast`.  The forward remnant and the inverse
  corrected component are RECONCILED because each, via componentwise correction, LANDS ON `δ.1`.
* **Step 3a (recovered-choice non-purity).**  `phi4WTriplePrime_recoveredChoice_ne_pureLeft` /
  `..._ne_pureRight`: the recovered global choice (body-614) avoids BOTH pure primitives, so — once the
  outer W‴ membership below is available — it lands in `phi4EdgeCompleteForestChoiceCarrier` (the
  `choice_filtered` field of `Phi4EdgeCompleteFilteredCoassocSplitChoice`).  These read the three-region
  tags (LEFT `Sum.inl true` / RIGHT `Sum.inl false` / FOREST `Sum.inr …`) directly and are proved WITHOUT
  the outer-membership obstruction below.
* **Step 5–6 (multiplicity).**  `phi4WTriplePrime_inv_correctedForest_eq_forestDomain_image` is re-exposed:
  the corrected quotient forest is EXACTLY the target forest domain's components — every `Finset.image`
  carries its injectivity proof, so NO dedup / NO orbit quotient / NO multiplicity loss occurs on the way to
  the FOREST sector of the whole map.

## Frontier — the whole `Equiv` is NOT emitted (two genuine, NON-fabricable obstructions)

The TARGET `phi4WTriplePrime_forestBlockEquivCorrected :
  Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃ Phi4WTriplePrimeInverseCodomain G` requires the inverse map
`z ↦ recoveredSplitChoice z`, hence a `Phi4EdgeCompleteFilteredCoassocSplitChoice G` inhabitant, hence the
outer-forest W‴ index membership `phi4WTriplePrime_recoveredOuter z ∈ phi4WTriplePrimeIndex G` — plus the two
composition round-trips.  Each of the following is a genuine unmet obligation; closing the `Equiv` here would
require fabricating a dependent `Σ` / `Finset.pi` transport across a `.1`-equality that is NOT yet proved —
exactly the forbidden move — so the `Equiv` is deliberately withheld (a TRUTHFUL STOP, mirroring body-615).

1. **`recoveredOuter_mem` positive-complement conjunct.**  W‴ membership needs `IsProperForest`, whose fifth
   conjunct is `0 < (recoveredOuter z).complementEdges.card` (positive complement in `G`).  The only available
   route (`phi4WTriplePrime_complementEdges_card_pos_of_internalEdges_le`, body-602) needs a bound
   `recoveredOuter.internalEdges ≤ H` for some `H` with positive complement.  For an ARBITRARY codomain `z`
   the recovered parent's INDUCED region carries the decontracted reconnection edges, so
   `recoveredOuter.internalEdges` is NOT bounded by `z.1.1.internalEdges`, and no ambient bound with positive
   complement is available in the imported chain.  (The other four IsProperForest conjuncts, the four
   `G`-ambient conjuncts, and forest saturation / edge-completeness ARE available region-by-region — the
   positive-complement conjunct is the sole gap.)  This is a genuine new construction, not present in bodies
   604–616.
2. **Cross-composition round-trips are ABSENT.**  `forestBlockForwardCorrected (recoveredSplitChoice z) = z`
   needs `selectedOuter (recoveredSplitChoice z) = z.1.1` (coordinate 1) and, transported across it, the
   dependent `correctedQuotientForest (recoveredSplitChoice z) = z.2.1` (coordinate 2);
   `recoveredSplitChoice (forestBlockForwardCorrected s) = s` needs
   `recoveredOuter (forestBlockForwardCorrected s) = s.outer` plus the full choice reconstruction.  NONE of
   these reconciliation theorems exists anywhere in the φ⁴ (`Phi4WTriplePrime*`) arc — bodies 604–616 built
   only the ONE-SIDED pieces (recovered outer, recovered choice, corrected inverse forest, the raw component
   round-trip above).  Building them (and the corrected forward map whose quotient coordinate uses the
   corrected remnants) is itself several bodies of work; forcing the `Equiv` without them would demand a
   fabricated transport.

## Revised roadmap (the whole `Equiv` is split into a body sequence — Lean forced this scope split)
The piecewise inverse and the global inverse are DIFFERENT theorems.  The `Equiv` is issued only after the
frontiers above are discharged one at a time:
* **body-618** — `phi4WTriplePrime_recoveredOuter_complementEdges_card_pos z : 0 < (recoveredOuter z).complementEdges.card`.
  NO `recoveredOuter.IE ≤ z.outer.IE` assumption; instead expose the edge multiset surviving OUTWARD after
  decontraction from the codomain's properness, or prove the exact complement residual identity.
* **body-619** — the recovered inverse inhabitant: `recoveredOuter z ∈ phi4WTriplePrimeIndex G` (assembling
  618 with the region-wise CD / disjoint / saturation / edge-complete facts) and the source-independent
  `recoveredSplitChoice z : Phi4EdgeCompleteFilteredCoassocSplitChoice G`, residual-field-free.
* **body-620** — forward-after-inverse: `forestBlockForwardCorrected (recoveredSplitChoice z) = z` (outer
  recovery → quotient-forest raw recovery → final `Σ` equality; star-free via 608, FOREST via 616).
* **body-621** — inverse-after-forward: `recoveredSplitChoice (forestBlockForwardCorrected s) = s`
  (branch-wise LEFT/RIGHT/FOREST recovery; body-614's exact `Sum.inr ⟨B, mem⟩` obligation discharged HERE).
* **body-622** — pure assembly: `phi4WTriplePrime_forestBlockEquivCorrected` from 619–621, NO new geometry.
Then body-623+ : summand agreement → `Finset.sum_bij` → `alpha` → Δᵣ-coassoc.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; NO global `τ`, NO orbit quotient / dedup, NO strict cross-presentation star equality, NO
`δ.boundaryEdgeCount = 0`; every `Finset.image` consumed carries its injectivity proof (zero multiplicity
loss); NO fabricated `HEq` / `cast` (ZERO `HEq` / `cast` sites in this file); the whole forest-block `Equiv`
and its round-trips are deliberately NOT emitted (documented frontier above); no `alpha` / `sum_bij` /
summand agreement / coassoc; no new `class` / `structure` / permanent `instance`; no
`sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst617 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the geometric FOREST recovery, now a RAW `Eq` (upgrade of body-615) -/

/-- **body-617 (Step 1, HEADLINE) — the FOREST-sector geometric round-trip is a RAW `Eq`.**  For any recovered
forest occurrence `O` over `z` / `δ`, the body-616 corrected forest component EQUALS the target quotient
component `δ.1` as an ordinary `Eq` — both inhabit the SAME fixed quotient ambient
`Q := z.1.1.contractWithStars (starOf G z.1.1)`, so no dependent transport is needed and NO `HEq` / `cast` is
introduced.  This is the exact upgrade of body-615's up-to-`τ` obstruction
(`phi4WTriplePrime_forestBlock_forestRecovery_upToPerm` / `..._classLevel`): the forward remnant and the
inverse corrected component are reconciled through the common raw target — each, via its OWN componentwise
`reconTau`, lands on `δ.1`.  This discharges the GEOMETRIC part of body-614's FOREST obligation. -/
theorem phi4WTriplePrime_forestBlock_correctedForestRecovery_raw
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    phi4WTriplePrime_inv_correctedForestComponent O = δ.1 :=
  phi4WTriplePrime_inv_correctedForestComponent_roundtrip O

/-- **body-617 (Step 1, multiplicity) — the corrected quotient forest IS the target forest domain's
components.**  Re-exposed from body-616: each corrected component equals its target `δ.1`, the collection is a
raw `Finset` `Eq` to the star-touching part of `z.2.1`, and the underlying map is injective (body-616
`_correctedForestComponentDom_injective`), so NO multiplicity is lost. -/
theorem phi4WTriplePrime_forestBlock_correctedForest_eq_forestDomain_image
    (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_inv_correctedForest z
      = (phi4WTriplePrime_inv_forestDomain z).image (fun δ => δ.1) :=
  phi4WTriplePrime_inv_correctedForest_eq_forestDomain_image z

/-! ## Step 3a — the recovered global choice avoids both pure primitives -/

/-- **body-617 (Step 3a) — the recovered choice is NOT the all-left pure primitive.**  `z.2.1` is a proper
forest, hence has a component `δ₀`; its recovered quotient-region component is tagged `Sum.inl false` (RIGHT,
star-free) or `Sum.inr …` (FOREST, star-touching) — never `Sum.inl true`.  So `recoveredChoice z ≠ PL`. -/
theorem phi4WTriplePrime_recoveredChoice_ne_pureLeft (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_recoveredChoice z
      ≠ phi4EdgeCompleteChoicePL (phi4WTriplePrime_recoveredOuter z) := by
  obtain ⟨d, hd⟩ := (phi4WTriplePrime_inv_B_isProperForest z).1
  set δ₀ : {x // x ∈ z.2.1.elements} := ⟨d, hd⟩ with hδ₀
  intro hEq
  set g : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements} :=
    ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
      phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ with hg
  have hPL : phi4WTriplePrime_recoveredChoice z g (Finset.mem_attach _ g) = Sum.inl true :=
    congrFun (congrFun hEq g) (Finset.mem_attach _ g)
  by_cases hst : phi4WTriplePrime_inv_isForestImage z δ₀
  · have hR := phi4WTriplePrime_recoveredChoice_forest_isRight z hst (Finset.mem_attach _ g)
    rw [hPL] at hR
    simp only [Sum.isRight_inl] at hR
    exact absurd hR (by decide)
  · have hF := phi4WTriplePrime_recoveredChoice_right z hst (Finset.mem_attach _ g)
    rw [hPL] at hF
    exact absurd (Sum.inl.inj hF.symm) (by decide)

/-- **body-617 (Step 3a) — the recovered choice is NOT the all-right pure primitive.**  Either some
`A`-component is LEFT (tagged `Sum.inl true`), or — if none is — the nonempty `z.1.1` has a component whose
canonical star lands in some `δ₀`, making `δ₀` star-touching (FOREST, tagged `Sum.inr …`).  Either way a
component is tagged `≠ Sum.inl false`, so `recoveredChoice z ≠ PR`. -/
theorem phi4WTriplePrime_recoveredChoice_ne_pureRight (z : Phi4WTriplePrimeInverseCodomain G) :
    phi4WTriplePrime_recoveredChoice z
      ≠ phi4EdgeCompleteChoicePR (phi4WTriplePrime_recoveredOuter z) := by
  intro hEq
  by_cases hLex : ∃ γ : ResolvedFeynmanSubgraph G,
      γ ∈ z.1.1.elements ∧ phi4WTriplePrime_inv_isLeftComponent z γ
  · obtain ⟨γ, hγA, hLc⟩ := hLex
    set g : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements} :=
      ⟨γ, phi4WTriplePrime_inv_left_mem_recoveredOuter z hγA hLc⟩ with hg
    have hPR : phi4WTriplePrime_recoveredChoice z g (Finset.mem_attach _ g) = Sum.inl false :=
      congrFun (congrFun hEq g) (Finset.mem_attach _ g)
    have hL := phi4WTriplePrime_recoveredChoice_left z hγA hLc (Finset.mem_attach _ g)
    rw [hPR] at hL
    exact absurd (Sum.inl.inj hL.symm) (by decide)
  · push_neg at hLex
    obtain ⟨c, hc⟩ := (phi4WTriplePrime_inv_A_isProperForest z).1
    have hnotL : ¬ phi4WTriplePrime_inv_isLeftComponent z c := hLex c hc
    rw [phi4WTriplePrime_inv_not_isLeftComponent_iff] at hnotL
    obtain ⟨δ₀, hstar⟩ := hnotL
    have hst : phi4WTriplePrime_inv_isForestImage z δ₀ :=
      ⟨phi4WTriplePrimeCanonicalSupply.starOf G z.1.1 c, hstar,
        ResolvedAdmissibleSubgraph.mem_starVertices.mpr ⟨c, hc, rfl⟩⟩
    set g : {x // x ∈ (phi4WTriplePrime_recoveredOuter z).elements} :=
      ⟨phi4WTriplePrime_inv_regionComponentOf z δ₀,
        phi4WTriplePrime_inv_regionComponent_mem_recoveredOuter z δ₀⟩ with hg
    have hPR : phi4WTriplePrime_recoveredChoice z g (Finset.mem_attach _ g) = Sum.inl false :=
      congrFun (congrFun hEq g) (Finset.mem_attach _ g)
    have hR := phi4WTriplePrime_recoveredChoice_forest_isRight z hst (Finset.mem_attach _ g)
    rw [hPR] at hR
    simp only [Sum.isRight_inl] at hR
    exact absurd hR (by decide)

end GaugeGeometry.QFT.Combinatorial
