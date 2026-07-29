import GaugeGeometry.QFT.HopfAlgebra.ResolvedBoundaryCompletedSubgraph

/-!
# QFT-R1-body-596 — nested boundary-ID coherence audit

Body-589's even/odd `legId` encoding is perfect at FIRST order:

```text
existing leg ℓ  ↦ existingLegId ℓ = 2·(ℓ.legId)      (EVEN)
boundary edge e ↦ boundaryLegId e = 2·(e.edgeId) + 1  (ODD)
```

But the coassoc geometry contracts TWICE.  At second order, a parent's boundary (odd) leg `2e+1` is
itself re-encoded as an existing leg, producing

```text
nested route:  existingLegId (boundaryExternalLeg e) = 2·(2·e.edgeId + 1) = 4·e.edgeId + 2   (EVEN)
direct route:  boundaryLegId e                        = 2·e.edgeId + 1                        (ODD)
```

One even, one odd — they can never be equal.  And this is NOT a vertex-relabeling artifact:
`resolvedLegIdProfile` (the multiset of external-leg `legId`s) is a `mapPerm`-INVARIANT, and resolved class
equality is exactly `∃ σ, · = ·.mapPerm σ` (which preserves every `legId`).  So a correcting permutation —
the body-580 tool that absorbed the STAR mismatch — CANNOT absorb this ID mismatch.

This body **measures the crack**: it banks the nested/direct no-go, the profile invariant, and the
old-`promote` incompatibility, and names the repair frontier for body-597+.  It builds no repaired
completion; it proves nothing about resolved class equality of the two routes.

This is the genuine second half of body-567's "the resolved version is needed separately": the first half
(589) restored the boundary at first order; here the SECOND-order re-encoding is shown to break naive
nesting, so 597+ must supply a **root-relative / stable** nested boundary completion.

## Contents

* Step 1 `existingLegId_boundaryExternalLeg` (`= ⟨4·e.edgeId + 2⟩`) + `…_ne_boundaryLegId` — the nested vs
  direct no-go, as concrete arithmetic (reuses body-589's `existingLegId_ne_boundaryLegId`).
* Step 2 `resolvedLegIdProfile` + `resolvedLegIdProfile_mapPerm` — the leg-ID profile is `mapPerm`-invariant,
  so the nested/direct profile difference cannot be relabeled away.
* Step 3 `boundaryLegId_not_existingLegId` + `nested_direct_singletonProfile_ne` — the odd induced leg is
  never a re-encoding of an ambient leg, and the two routes' singleton profiles differ (documenting the
  old-`promote` incompatibility: `promote` wants `δ.externalLegs ≤ γ.externalLegs`, but a boundary-completed
  `δ` on `γ.boundaryCompletedResolvedGraph` carries odd induced legs absent from the ambient `G.externalLegs`).

## Repair frontier (body-597+)

A **root-relative / stable nested boundary completion** must: preserve inherited normalized IDs WITHOUT
re-encoding; give an ODD ID only to the newly-cut internal edges; agree EXACTLY (ID + profile) with the
direct completion after promotion; keep edge-origin traceability; keep `LegIdsUnique`; be `mapPerm`-coherent;
and transport family-CD.

Per the HALT: body-589/594/595 are not edited; no selectedOuter / `promote` construction; the ID mismatch is
NOT forged away by a vertex permutation; no resolved class equality of the two routes is asserted; no
quotient / alpha / coassoc; zero `class` / `instance`; zero forbidden divergence classes.
-/

namespace GaugeGeometry.QFT.Combinatorial

open ResolvedFeynmanSubgraph

/-! ## Step 1 — the nested vs direct ID no-go (concrete arithmetic) -/

/-- **body-596 (Step 1) — the nested-route leg ID is `4·e.edgeId + 2`.**  Re-encoding a parent boundary
(odd, `2e+1`) leg as an existing leg doubles it: `existingLegId (boundaryExternalLeg e) = ⟨2·(2·e.edgeId+1)⟩
= ⟨4·e.edgeId+2⟩` — EVEN. -/
theorem existingLegId_boundaryExternalLeg {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    existingLegId (γ.boundaryExternalLeg e) = ⟨4 * e.edgeId.id + 2⟩ := by
  simp only [existingLegId, boundaryExternalLeg_legId, boundaryLegId]
  congr 1
  omega

/-- **body-596 (Step 1) — nested ≠ direct.**  The second-order (nested existing-re-encoded, EVEN `4e+2`)
and first-order (direct boundary, ODD `2e+1`) IDs of the SAME boundary edge never agree.  Reuses body-589's
even/odd `existingLegId_ne_boundaryLegId`. -/
theorem existingLegId_boundaryExternalLeg_ne_boundaryLegId {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    existingLegId (γ.boundaryExternalLeg e) ≠ boundaryLegId e :=
  existingLegId_ne_boundaryLegId (γ.boundaryExternalLeg e) e

/-! ## Step 2 — the leg-ID profile is a `mapPerm` invariant -/

/-- **body-596 (Step 2) — the leg-ID profile.**  The multiset of a resolved graph's external-leg `legId`s —
the invariant that distinguishes the nested and direct completions. -/
def resolvedLegIdProfile (G : ResolvedFeynmanGraph) : Multiset ResolvedLegId :=
  G.externalLegs.map ResolvedExternalLeg.legId

/-- **body-596 (Step 2) — the leg-ID profile is `mapPerm`-invariant.**  `mapPerm σ` preserves every `legId`
(`ResolvedExternalLeg.map` keeps the id), so the profile is unchanged — hence resolved class equality (which
is `∃ σ, · = ·.mapPerm σ`) preserves the profile, and the nested/direct profile difference is NOT
relabelable. -/
@[simp] theorem resolvedLegIdProfile_mapPerm (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    resolvedLegIdProfile (G.mapPerm σ) = resolvedLegIdProfile G := by
  unfold resolvedLegIdProfile
  show (G.externalLegs.map (ResolvedExternalLeg.map σ)).map ResolvedExternalLeg.legId
    = G.externalLegs.map ResolvedExternalLeg.legId
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-! ## Step 3 — old-`promote` incompatibility -/

/-- **body-596 (Step 3) — an induced boundary leg is never a re-encoding of an ambient leg.**  The odd
`boundaryLegId e = 2e+1` is never `existingLegId ℓ = 2·(…)` for any ambient leg `ℓ` — so the boundary-completed
`δ`'s induced legs are NOT ambient legs re-encoded, and cannot fit the old `promote`'s `δ.externalLegs ≤
γ.externalLegs` ambient shape by any id-level identification. -/
theorem boundaryLegId_not_existingLegId (e : ResolvedFeynmanEdge) (ℓ : ResolvedExternalLeg) :
    boundaryLegId e ≠ existingLegId ℓ :=
  (existingLegId_ne_boundaryLegId ℓ e).symm

/-- **body-596 (Step 3) — the nested and direct singleton profiles differ.**  A one-leg profile carrying the
nested ID cannot equal one carrying the direct ID (from Step 1's `≠`), so — with the `mapPerm`-invariance of
Step 2 — no vertex permutation can bridge a nested-completed graph to a direct-completed one at that leg. -/
theorem nested_direct_singletonProfile_ne {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (e : ResolvedFeynmanEdge) :
    ({existingLegId (γ.boundaryExternalLeg e)} : Multiset ResolvedLegId) ≠ {boundaryLegId e} := by
  intro h
  exact existingLegId_boundaryExternalLeg_ne_boundaryLegId γ e (Multiset.singleton_inj.mp h)

end GaugeGeometry.QFT.Combinatorial
