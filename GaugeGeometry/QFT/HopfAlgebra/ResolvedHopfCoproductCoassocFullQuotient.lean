import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientBody
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem

/-!
# R-6c-heart-5b-4 — concrete `fullQuotientOf` from `Right ⊔ Remnant`

Heart-3 (`QuotientBody`) reduced the quotient forest to an **arbitrary** supply field `fullQuotientOf :
(s) → ResolvedFullQuotientForestImageData (Sig.sigmaDataOf s)`.  `product_eq` cannot be proved against
an arbitrary quotient forest, so this file replaces it by the concrete construction
`fullQuotientOf s = (remnantForest s) ⊔ (rightSurvivorForest s)` — exactly the `Remnant ⊔ Right`
grain of `ResolvedFullQuotientForestImageData`.

The selected-outer forest is the **concrete** one (`resolvedConcreteSelectedOuterImageSupply` from P5),
so `(Sig.sigmaDataOf s).Aout.contractWithStars (Sig.sigmaDataOf s).starOf` is *definitionally* the
quotient graph `s.selectedOuterContractGraph` over which the survivor/remnant forests live — the two
families plug straight into `remnantComponents` / `rightComponents`.

The structural `ResolvedFullQuotientForestImageData` data that is **not** combinatorial bookkeeping —
the forest discriminator `remnantNonempty`, and the star separators `remnantTouches` /
`rightAvoidsStars` (the G-13 separator obligations) — are, per the HALT, kept as supply fields, along
with the survivor/remnant cross-disjointness.  The CD/pairwise-disjointness come *for free* from the
admissible-forest structure of `remnantForest` / `rightSurvivorForest`.

Landed:

* `ResolvedConcreteFullQuotientSupply D G mem Sig` — a survivor supply, a remnant supply, their
  cross-disjointness, and the three separator/discriminator facts as supply fields;
* `ResolvedConcreteFullQuotientSupply.toFullQuotientSupply` — the concrete
  `ResolvedCoassocFullQuotientSupply` (so `quotientForestOf = (remnant ⊔ right).toImage` via the
  existing heart-3 `.quotientForestOf` / `.toQuotientForestSupply`).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The separator/discriminator proofs and the
de-contraction term geometry (`product_eq` / `right_eq`, 5c) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5b-4 — the concrete full-quotient supply.**  The data assembling `fullQuotientOf` as
`Remnant ⊔ Right`: a right-survivor supply, a remnant supply, their cross-disjointness, and the three
`ResolvedFullQuotientForestImageData` facts that are genuine geometry (the forest discriminator and the
two star separators) as supply fields.  The selected outer is the concrete one (`mem` = P5 carrier
closure), so the survivor/remnant forests live over `Sig.sigmaDataOf`'s contract graph definitionally. -/
structure ResolvedConcreteFullQuotientSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (mem : ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G)
    (Sig : ResolvedCoassocSigmaDataSupply D G (resolvedConcreteSelectedOuterImageSupply D G mem)) where
  /-- The right-survivor supply (the `Right` half — the `Sum.inl false` survivors). -/
  survivor : ResolvedRightSurvivorSupply D G
  /-- The remnant supply (the `Remnant` half — the `Sum.inr B` de-contraction pieces). -/
  remnant : ResolvedRemnantComponentSupply D G
  /-- Survivor and remnant components are cross-disjoint. -/
  cross : ∀ s : ResolvedCoassocSplitChoice D G,
    ∀ δ ∈ (survivor.rightSurvivorForest s).elements,
    ∀ δ' ∈ (remnant.remnantForest s).elements, δ ≠ δ' → δ.Disjoint δ'
  /-- There is at least one remnant piece (the forest discriminator). -/
  remnantNonempty : ∀ s : ResolvedCoassocSplitChoice D G,
    (remnant.remnantForest s).elements.Nonempty
  /-- Each remnant piece touches an outer star. -/
  remnantTouches : ∀ s : ResolvedCoassocSplitChoice D G,
    ∀ δ ∈ (remnant.remnantForest s).elements,
    ¬ Disjoint δ.vertices ((Sig.sigmaDataOf s).Aout.starVertices (Sig.sigmaDataOf s).starOf)
  /-- Each right survivor avoids the outer stars. -/
  rightAvoidsStars : ∀ s : ResolvedCoassocSplitChoice D G,
    ∀ δ ∈ (survivor.rightSurvivorForest s).elements,
    Disjoint δ.vertices ((Sig.sigmaDataOf s).Aout.starVertices (Sig.sigmaDataOf s).starOf)

/-- **R-6c-heart-5b-4 — the concrete `fullQuotientOf`.**  Replaces the arbitrary heart-3 supply by the
`Remnant ⊔ Right` construction: `remnantComponents`/`rightComponents` are the concrete remnant/survivor
forests, `remnantCD`/`rightCD`/`pairwiseDisjoint` come from their admissible structure plus the cross,
and the discriminator/separators are the supplied facts. -/
noncomputable def ResolvedConcreteFullQuotientSupply.toFullQuotientSupply
    {mem : ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G}
    {Sig : ResolvedCoassocSigmaDataSupply D G (resolvedConcreteSelectedOuterImageSupply D G mem)}
    (Q : ResolvedConcreteFullQuotientSupply D G mem Sig) :
    ResolvedCoassocFullQuotientSupply D G (resolvedConcreteSelectedOuterImageSupply D G mem) Sig where
  fullQuotientOf := fun s =>
    { remnantComponents := (Q.remnant.remnantForest s).elements
      rightComponents := (Q.survivor.rightSurvivorForest s).elements
      remnantCD := (Q.remnant.remnantForest s).isConnectedDivergent
      rightCD := (Q.survivor.rightSurvivorForest s).isConnectedDivergent
      pairwiseDisjoint := by
        intro δ₁ h₁ δ₂ h₂ hne
        rcases Finset.mem_union.mp h₁ with hr₁ | hs₁ <;>
          rcases Finset.mem_union.mp h₂ with hr₂ | hs₂
        · exact (Q.remnant.remnantForest s).pairwiseDisjoint hr₁ hr₂ hne
        · exact (Q.cross s δ₂ hs₂ δ₁ hr₁ hne.symm).symm
        · exact Q.cross s δ₁ hs₁ δ₂ hr₂ hne
        · exact (Q.survivor.rightSurvivorForest s).pairwiseDisjoint hs₁ hs₂ hne
      remnantNonempty := Q.remnantNonempty s
      remnantTouches := Q.remnantTouches s
      rightAvoidsStars := Q.rightAvoidsStars s }

end GaugeGeometry.QFT.Combinatorial
