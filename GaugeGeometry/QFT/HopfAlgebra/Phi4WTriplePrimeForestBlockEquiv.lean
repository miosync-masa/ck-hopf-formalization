import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeRecoveredSplitChoice

/-!
# QFT-R1-body-615 — forest-block round-trip: the FOREST sector recovers only up to the mapPerm orbit (RED-LINE STOP)

Body-614 assembled the residual-free recovered-occurrence owner, the three-region recovered outer forest, and
the recovered global choice (region tags), then explicitly DEFERRED the exact FOREST value equation
`recoveredChoice … = Sum.inr ⟨innerForest, mem⟩` (for a FIXED `δ₀`) to this body as a *named* obligation — to
be discharged **only if** a genuine dependent term round-trip holds.

This body carries out the equality-level audit demanded by the spec and reaches the following verdict.

## Equality-level audit (spec Step 1)

* recovered outer (LEFT/RIGHT survivors): ordinary `Eq` — a star-free `δ` is fully `G`-native, so body-608's
  `recoveredRight` round-trip is a RAW `toResolvedFeynmanGraph` equality (no relabeling).  ✅ term-level.
* **FOREST sector (star-touching `δ`): NOT an ordinary `Eq`.**  The recovered inner forest is recontracted with
  the parent's *freshly generated* canonical star `starL`, whose vertex ids differ from `δ`'s original quotient
  star ids `starA`.  Body-613 reconciles them only through a nontrivial correcting permutation `τ`
  (`phi4WTriplePrime_inv_reconTau`): the strongest HONEST statement is the RAW `mapPerm`-orbit equality
  `remnant.mapPerm τ = δ.boundaryCompletedResolvedGraph`, i.e. the class-level equality
  `remnant.toResolvedClass = δ.boundaryCompletedResolvedGraph.toResolvedClass`
  (`phi4WTriplePrime_inv_recontraction_recovery`).  A raw term equality `remnant = δ.bcrg` would force
  `δ.boundaryEdgeCount = 0`, which W‴ membership does NOT guarantee (see body-609's frontier docstring and
  body-604's forward `remnant = localContraction.mapPerm τ`, which is *itself* only defined up to a permutation).

## Verdict — the RED LINE is reached (the type mismatch IS the deliverable)

The forest-block codomain

```
Phi4WTriplePrimeInverseCodomain G
  = Σ A ∈ phi4WTriplePrimeIndex G, {B ∈ phi4WTriplePrimeIndex (A.contractWithStars starOf)}
```

is a Σ over **raw** W‴ carrier members: each forest component `δ` of `z.2.1 = B` is a raw
`ResolvedFeynmanSubgraph (A.contractWithStars starOf)` with **specific** vertex ids.  The forward-after-recovered
round-trip `forestBlockForward (inverse z) = z` therefore demands, in its second Σ-coordinate, the RAW term
equation `quotientForest (inverse z) = z.2.1`, whose FOREST components are exactly the recontracted remnants.
Those remnants agree with `z.2.1`'s forest components **only up to the correcting permutation `τ`** — the
mapPerm orbit — never as raw terms.

* **What we get:** `∃ τ, remnant.mapPerm τ = δ.boundaryCompletedResolvedGraph`
  (equivalently `remnant.toResolvedClass = δ.…toResolvedClass`).
* **What a true term equality — hence the whole `Equiv` — needs:** `remnant = δ.boundaryCompletedResolvedGraph`
  as a raw `ResolvedFeynmanGraph`, i.e. `τ = id` on the recontraction stars.  This is FALSE in general (fresh
  canonical star ≠ `δ`'s quotient star), and forcing it would require `δ.boundaryEdgeCount = 0`.

Per the body-615 red line, closing `phi4WTriplePrime_forestBlockEquiv` here would require fabricating an
`HEq` / `cast` that transports across this nontrivial `τ` — a *false* dependent transport turning an orbit
equality into a raw one.  **That is forbidden, so the whole-forest-block `Equiv` is deliberately NOT emitted.**
The exact `Sum.inr ⟨B, mem⟩` value equation (body-614's named obligation) is NOT discharged: it is precisely the
component whose raw term equality fails.  This is a TRUTHFUL STOP, recorded as two honest theorems below.

## What this body DOES prove (the maximal honest recovery)

* **Step (class)** — `phi4WTriplePrime_forestBlock_forestRecovery_classLevel`: for any recovered forest
  occurrence over `z`/`δ`, recontracting the recovered inner forest returns `δ`'s boundary-completion at the
  `toResolvedClass` (mapPerm-orbit) level.  This is the strongest form the FOREST round-trip supports.
* **Step (up-to-perm)** — `phi4WTriplePrime_forestBlock_forestRecovery_upToPerm`: the same recovery exhibited as
  an explicit `∃ τ, remnant.mapPerm τ = δ.bcrg` — making the residual vertex-relabeling `τ` (the exact
  obstruction to a raw `Eq`) concrete.

## HALT compliance
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes in any
declaration type; no fabricated `HEq` / `cast`; no whole forest-block `Equiv`; no false raw star equality; no
`δ.boundaryEdgeCount = 0`; no `alpha` / `sum_bij` / summand agreement / coassoc; no `s` / `componentEquiv`; no
new `class` / `structure` / permanent `instance`; no `sorry` / `admit` / `native_decide`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

set_option maxHeartbeats 3200000

/-- The concrete φ⁴ divergence measure family, registered file-locally (providable instance, NO forbidden
class). -/
noncomputable local instance phi4Inst615 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-- **body-615 (class level) — the FOREST-sector round-trip closes ONLY at the resolved-class (mapPerm-orbit)
level.**  For any recovered forest occurrence `O` over a star-touching `δ`, recontracting the recovered inner
forest `F` inside the recovered parent's boundary-completed ambient (with the parent's *fresh* canonical star)
returns `δ`'s boundary-completion at the `toResolvedClass` level — the strongest HONEST form (body-613).  A raw
`ResolvedFeynmanGraph` equality is NOT available: the fresh recontraction star and `δ`'s quotient star differ,
so the recovery is only determined up to a vertex relabeling. -/
theorem phi4WTriplePrime_forestBlock_forestRecovery_classLevel
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    ((phi4WTriplePrime_inv_recoveredInnerForest O.input
        (phi4WTriplePrime_inv_innerForest_CD_proof O.input)).contractWithStars
      (phi4WTriplePrimeCanonicalSupply.starOf
        (phi4WTriplePrime_inv_recoveredParent O.input).boundaryCompletedResolvedGraph
        (phi4WTriplePrime_inv_recoveredInnerForest O.input
          (phi4WTriplePrime_inv_innerForest_CD_proof O.input)))).toResolvedClass
      = δ.1.boundaryCompletedResolvedGraph.toResolvedClass :=
  O.recontractionRecovery

/-- **body-615 (up-to-perm) — the FOREST-sector recovery, with the residual relabeling made explicit.**  There
is a permutation `τ` of `VertexId` (the correcting permutation `phi4WTriplePrime_inv_reconTau`) carrying the
recontracted remnant EXACTLY onto `δ`'s boundary-completion.  This `τ` is the precise obstruction to a raw term
`Eq` (and hence to the whole forest-block `Equiv`): a genuine `remnant = δ.bcrg` would need `τ = id` on the
recontraction stars, which fails because the fresh canonical star ≠ `δ`'s quotient star (a raw target would
force `δ.boundaryEdgeCount = 0`, not guaranteed by W‴ membership). -/
theorem phi4WTriplePrime_forestBlock_forestRecovery_upToPerm
    {z : Phi4WTriplePrimeInverseCodomain G} {δ : {x // x ∈ z.2.1.elements}}
    (O : Phi4WTriplePrime_RecoveredForestOccurrence z δ) :
    ∃ τ : Equiv.Perm VertexId,
      ((phi4WTriplePrime_inv_recoveredInnerForest O.input
          (phi4WTriplePrime_inv_innerForest_CD_proof O.input)).contractWithStars
        (phi4WTriplePrimeCanonicalSupply.starOf
          (phi4WTriplePrime_inv_recoveredParent O.input).boundaryCompletedResolvedGraph
          (phi4WTriplePrime_inv_recoveredInnerForest O.input
            (phi4WTriplePrime_inv_innerForest_CD_proof O.input)))).mapPerm τ
        = δ.1.boundaryCompletedResolvedGraph :=
  ⟨phi4WTriplePrime_inv_reconTau O.input, phi4WTriplePrime_inv_recontraction_raw O.input⟩

/-! ## RED LINE — the whole forest-block `Equiv` is deliberately NOT emitted.

`phi4WTriplePrime_forestBlockEquiv : Phi4EdgeCompleteFilteredCoassocSplitChoice G ≃
  Phi4WTriplePrimeInverseCodomain G` would require the forward-after-recovered round-trip to satisfy the RAW
Σ-coordinate equation `quotientForest (inverse z) = z.2.1`, whose FOREST components are the recontracted
remnants above.  By `phi4WTriplePrime_forestBlock_forestRecovery_upToPerm` those match `z.2.1`'s forest
components only after the nontrivial permutation `τ`, i.e. only in the mapPerm orbit / `toResolvedClass`.
Emitting the `Equiv` (and its `right_inv` / the `Sum.inr ⟨B, mem⟩` value equation) would demand an `HEq` / `cast`
transporting across `τ` — a FALSE dependent transport.  It is therefore intentionally omitted; the two theorems
above are the truthful maximal recovery.

## Resolution route — CORRECT THE FORWARD MAP, do NOT quotient the codomain.
The raw Σ codomain is KEPT: orbit-quotienting the index would collapse ID-distinct occurrences / star-coordinate
fibers and thereby change coproduct coefficients / multiplicities / future symmetry factors — i.e. it would
change the computed value, so it is rejected.  Instead the geometric `τ`-shift is fixed on the FORWARD side:
* body-616 — bundle the componentwise `reconTau` of every FOREST occurrence into a SINGLE global correcting
  permutation (fixing survivor/root vertices, sending reconstructed local stars onto the target quotient
  stars); upgrade `_upToPerm` to a raw corrected equality of the whole quotient forest.
* body-617 — define `forestBlockForwardCorrected` (uncorrected forward's quotient output ∘ global `τ`), prove
  the raw forward/backward laws against the recovered inverse, EMIT the genuine whole `Equiv`, and discharge
  body-614's FOREST exact `Sum.inr ⟨B, mem⟩` value obligation in this corrected forward-image context.
* body-618 — prove each summand of the corrected forward equals the original forward's (mapPerm invariance of
  the algebraic term), so NO raw index multiplicity is lost; then the corrected `Equiv` feeds `Finset.sum_bij`
  → `alpha` → Δᵣ-coassoc.
Slogan: **fix the coordinate shift in the forward map; never collapse the summand count.** -/

end GaugeGeometry.QFT.Combinatorial
