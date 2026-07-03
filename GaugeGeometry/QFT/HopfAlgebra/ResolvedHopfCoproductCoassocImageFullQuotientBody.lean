import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFullQuotient

/-!
# R-6c-body-35 — the quotient forest IS the full-quotient `remnant ⊔ right` (by `rfl`)

Thirty-fifth genuine-body step, discharging body-17's `quotientForest_union` residual at the CONCRETE image
side: the image's quotient forest is definitionally the full-quotient `toImage`, whose elements are
`remnant ⊔ right`.  This is the quotient counterpart to body-25's `selectedOuter_eq`, and — as body-17
anticipated — it falls out entirely by `rfl`.

The chain is definitional: heart-3 sets `quotientForestOf s := (fullQuotientOf s).toImage`, and the concrete
`fullQuotientOf` (heart-5b-4) sets `remnantComponents := (remnant.remnantForest s).elements`,
`rightComponents := (survivor.rightSurvivorForest s).elements`.  `toImage_elements` (`rfl`) then gives the
union.  Downstream `(imageOf s).quotientForest = quotientForestOf s` (the image-supply record), so these `rfl`
facts pin `(imageOf s).quotientForest.elements = remnant ⊔ right` for the concrete image side — no transport,
no fielding (unlike body-13/14's abstract transported form).

Per the HALT, the remnant / right component forests are NOT re-derived; support-9 finite cover is untouched;
the sigma-cover `Aout`/`starOf` alignment is the definitional one from the concrete construction.

Landed:

* `ResolvedCoassocFullQuotientSupply.quotientForestOf_eq_toImage` — `quotientForestOf s = (fullQuotientOf
  s).toImage` (`rfl`);
* `ResolvedCoassocFullQuotientSupply.quotientForestOf_elements` — its elements are the full-quotient
  components' union (`rfl`);
* `ResolvedConcreteFullQuotientSupply.quotientForestOf_elements` — CONCRETE: the elements are
  `remnant.remnantForest ⊔ survivor.rightSurvivorForest` (`rfl`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-body-35 — the quotient forest is the full-quotient `toImage`** (heart-3 definition, `rfl`). -/
theorem ResolvedCoassocFullQuotientSupply.quotientForestOf_eq_toImage
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    {Sig : ResolvedCoassocSigmaDataSupply D G S}
    (Full : ResolvedCoassocFullQuotientSupply D G S Sig)
    (s : ResolvedCoassocSplitChoice D G) :
    Full.quotientForestOf s = (Full.fullQuotientOf s).toImage := rfl

/-- **R-6c-body-35 — the quotient forest's elements are the full-quotient components' union** (`rfl`, via
`toImage_elements`). -/
theorem ResolvedCoassocFullQuotientSupply.quotientForestOf_elements
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    {Sig : ResolvedCoassocSigmaDataSupply D G S}
    (Full : ResolvedCoassocFullQuotientSupply D G S Sig)
    (s : ResolvedCoassocSplitChoice D G) :
    (Full.quotientForestOf s).elements =
      (Full.fullQuotientOf s).remnantComponents ∪ (Full.fullQuotientOf s).rightComponents := rfl

/-- **R-6c-body-35 — the CONCRETE quotient forest is `remnant ⊔ right`** (`rfl`): the image's quotient forest
elements are exactly the concrete remnant / right-survivor forests' elements. -/
theorem ResolvedConcreteFullQuotientSupply.quotientForestOf_elements
    {mem : ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G}
    {Sig : ResolvedCoassocSigmaDataSupply D G (resolvedConcreteSelectedOuterImageSupply D G mem)}
    (Q : ResolvedConcreteFullQuotientSupply D G mem Sig)
    (s : ResolvedCoassocSplitChoice D G) :
    (Q.toFullQuotientSupply.quotientForestOf s).elements =
      (Q.remnant.remnantForest s).elements ∪ (Q.survivor.rightSurvivorForest s).elements := rfl

end GaugeGeometry.QFT.Combinatorial
