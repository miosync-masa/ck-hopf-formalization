import GaugeGeometry.QFT.Combinatorial.ResolvedSubGraph

/-!
# QFT-R1-body-559 — external-boundary preservation under contraction (+ scope audit)

The first combinatorial step toward the concrete `φ⁴₄` realization.  Before any numerical
`DivergenceMeasure` is defined, we fix — as **divergence-free combinatorial theorems** — that single
star-contraction and admissible-forest star-contraction preserve the ambient *external boundary* up to
the (sector/id-preserving) retarget: the external-leg count, the external **sector profile**, and — on
the boundary-resolved carrier — the full `(legId, sector)` **boundary profile** are all invariant.

**The transport itself is already `rfl`.**  `FeynmanSubgraph.contract_externalLegs`,
`AdmissibleSubgraph.contractWithStars_externalLegs`, and
`ResolvedAdmissibleSubgraph.contractWithStars_externalLegs` state the external legs of the contracted
graph as `ambient.externalLegs.map (retarget …)` by `rfl`; and the retarget preserves `sector`
(and, resolved, `legId`) by `rfl` (`ExternalLeg.retarget_sector`, `ResolvedExternalLeg.retarget_sector`
/ `_legId`).  So the results below are **semantic quotient corollaries** of that existing `rfl` layer —
`Multiset.map_map` + `Multiset.card_map` + the sector/id `rfl` lemmas — not new geometry.

## Scope verdict — forward preservation / reflection vs. the single-contraction class

External-boundary preservation makes `IsDivergencePreservedByAdmissibleForestContract` and its reverse
companion *candidates* to realize from a concrete boundary-additive power-counting valuation (the
ambient and the quotient share the same external boundary profile, so a boundary-indexed superficial
degree transports).  ★But the single-contraction class

```text
IsDivergencePreservedByContract.contract_isDivergent :
    γ 1PI → γ divergent → (G/γ) divergent
```

does NOT follow from boundary preservation, and is *not* realized here.★  It requires the quotient to be
divergent from `γ` alone, **without assuming the ambient `G` is divergent** — which a genuinely
external-boundary-dependent measure need not give.  Example (schematic, `φ⁴₄`, `ω = 4 − E`): a 6-point
ambient with a divergent 4-point subgraph `γ` (`ω(γ) = 0`); contracting `γ` leaves a 6-point quotient
with `ω = 4 − 6 = −2 < 0`, i.e. **convergent**.  So `contract_isDivergent` as stated is a stronger, and
possibly (for boundary-dependent measures) over-strong, premise than forest preservation / reflection.

Accordingly this body: builds **no** `DivergenceMeasure` and **no** typeclass instance; edits no class;
fabricates no false implication; and records that "forest preservation / reflection" and the
"single-contraction class" live at **different scopes** — the downstream audit (next body) checks
whether each single-contraction consumer already carries ambient divergence.

Per the HALT: no `DivergenceMeasure`, no `ω = 4 − E`, ZERO typeclass instances, ZERO new
`class`/`structure`; no flat strict boundary equality is demanded; `LegIdsUnique` / injectivity /
freshness / properness / 1PI / CD are unused; no forest induction; the CK final theorem is not edited.
-/

namespace GaugeGeometry.QFT.Combinatorial

set_option linter.unusedSectionVars false

-- An abstract power-counting measure is *assumed* (instance binder), exactly as `AdmissibleSubgraph`
-- / `ResolvedAdmissibleSubgraph` require it; NO concrete `DivergenceMeasure` is defined or
-- instantiated here (per the HALT).
variable [∀ G : FeynmanGraph, DivergenceMeasure G]

/-! ## Flat external profiles and their contraction invariance -/

/-- The multiset of external-leg sectors of a flat graph — the `φ⁴₄` external-boundary observable. -/
def FeynmanGraph.externalSectorProfile (G : FeynmanGraph) : Multiset GaugeSector :=
  G.externalLegs.map ExternalLeg.sector

variable {G : FeynmanGraph}

/-- **R-6c-QFT-R1-body-559 — single star-contraction preserves the external-leg count.** -/
@[simp] theorem FeynmanSubgraph.contract_externalLegCount_eq_ambient (γ : FeynmanSubgraph G) :
    γ.contract.externalLegs.card = G.externalLegs.card := by
  rw [FeynmanSubgraph.contract_externalLegs, Multiset.card_map]

/-- **R-6c-QFT-R1-body-559 — admissible-forest star-contraction preserves the external-leg count.** -/
@[simp] theorem AdmissibleSubgraph.contractWithStars_externalLegCount_eq_ambient
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).externalLegs.card = G.externalLegs.card := by
  rw [AdmissibleSubgraph.contractWithStars_externalLegs, Multiset.card_map]

/-- **R-6c-QFT-R1-body-559 — single star-contraction preserves the external sector profile.** -/
@[simp] theorem FeynmanSubgraph.contract_externalSectorProfile_eq_ambient (γ : FeynmanSubgraph G) :
    γ.contract.externalSectorProfile = G.externalSectorProfile := by
  simp only [FeynmanGraph.externalSectorProfile, FeynmanSubgraph.contract_externalLegs,
    Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-- **R-6c-QFT-R1-body-559 — admissible-forest star-contraction preserves the external sector profile.** -/
@[simp] theorem AdmissibleSubgraph.contractWithStars_externalSectorProfile_eq_ambient
    (A : AdmissibleSubgraph G) (starOf : FeynmanSubgraph G → VertexId) :
    (A.contractWithStars starOf).externalSectorProfile = G.externalSectorProfile := by
  simp only [FeynmanGraph.externalSectorProfile,
    AdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-! ## Resolved witness profiles and their contraction invariance -/

/-- The full boundary witness of a resolved graph: each external leg's persistent `legId` and its
`sector`.  This is the finest external-boundary invariant the resolved carrier can report. -/
def ResolvedFeynmanGraph.externalBoundaryProfile (G : ResolvedFeynmanGraph) :
    Multiset (ResolvedLegId × GaugeSector) :=
  G.externalLegs.map (fun ℓ => (ℓ.legId, ℓ.sector))

/-- The multiset of external-leg sectors of a resolved graph. -/
def ResolvedFeynmanGraph.externalSectorProfile (G : ResolvedFeynmanGraph) : Multiset GaugeSector :=
  G.externalLegs.map ResolvedExternalLeg.sector

variable {H : ResolvedFeynmanGraph}

/-- **R-6c-QFT-R1-body-559 — resolved star-contraction preserves the full `(legId, sector)` boundary
profile.**  The descent `rigidified external legs → retarget map equality → (legId, sector) profile
equality`, all through the existing `rfl` layer. -/
@[simp] theorem ResolvedAdmissibleSubgraph.contractWithStars_externalBoundaryProfile_eq_ambient
    (A : ResolvedAdmissibleSubgraph H) (starOf : ResolvedFeynmanSubgraph H → VertexId) :
    (A.contractWithStars starOf).externalBoundaryProfile = H.externalBoundaryProfile := by
  simp only [ResolvedFeynmanGraph.externalBoundaryProfile,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-- **R-6c-QFT-R1-body-559 — resolved star-contraction preserves the external sector profile.** -/
@[simp] theorem ResolvedAdmissibleSubgraph.contractWithStars_externalSectorProfile_eq_ambient
    (A : ResolvedAdmissibleSubgraph H) (starOf : ResolvedFeynmanSubgraph H → VertexId) :
    (A.contractWithStars starOf).externalSectorProfile = H.externalSectorProfile := by
  simp only [ResolvedFeynmanGraph.externalSectorProfile,
    ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-- **R-6c-QFT-R1-body-559 — resolved star-contraction preserves the external-leg count.** -/
@[simp] theorem ResolvedAdmissibleSubgraph.contractWithStars_externalLegCard_eq_ambient
    (A : ResolvedAdmissibleSubgraph H) (starOf : ResolvedFeynmanSubgraph H → VertexId) :
    (A.contractWithStars starOf).externalLegs.card = H.externalLegs.card := by
  rw [ResolvedAdmissibleSubgraph.contractWithStars_externalLegs, Multiset.card_map]

end GaugeGeometry.QFT.Combinatorial
