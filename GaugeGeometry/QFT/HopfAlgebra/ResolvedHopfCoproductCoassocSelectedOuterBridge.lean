import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLeftSelect

/-!
# R-6c-support-5 — selectedOuter supply → imageOf supply bridge

The selected-outer pipeline is now closed up to the `selectedOuterOf` field that
`ResolvedCoassocSplitPhiImageSupply` (R-6c-4f part 3b) needs.  The landed pieces compose:

  `leftSelection` (R-6c-support-3) → `leftOf` concrete
  `+ promotedOf` (supply) `+ cross` (supply) → `ResolvedForestPromoteSupply.selectedOuterRawOf`
  `+ selectedOuter_mem` (supply) → `selectedOuterOf : ResolvedCoassocSplitChoice D G → {A // A ∈ D.carrier G}`.

This file bundles those into a single `ResolvedCoassocSelectedOuterImageSupply`, reuses the existing
`ResolvedCoassocSelectedOuterSupply.toSelectedOuterOf` bridge, and exposes
`toImageSupplySkeleton`: given the still-deferred `quotientForestOf` / `imageWeightOf` /
`discriminatorOf` as inputs, it produces a `ResolvedCoassocSplitPhiImageSupply D G`.  So the only
remaining de-contraction obligations on the image side are `quotientForestOf` (the quotient subforest),
the image weight, the discriminator, and the two supply fields `promotedOf` / `selectedOuter_mem`
(the genuine rep/perm promote + its carrier closure).

Landed:

* `ResolvedCoassocSelectedOuterImageSupply D G` — `leftSelection` + `promotedOf` + `cross` +
  `selectedOuter_mem`, the four inputs that determine the selected outer forest as a carrier forest;
* `.promoteSupply` / `.toSelectedOuterSupply` / `.selectedOuterOf` — the bundled selected-outer map;
* `.toImageSupplySkeleton` — assembles `ResolvedCoassocSplitPhiImageSupply` from `selectedOuterOf`
  plus the supplied `quotientForestOf` / `imageWeightOf` / `discriminatorOf`.

No facade, no flat splitPhi theorem, no `forgetHopf`; `promotedOf` (the genuine promote) and
`selectedOuter_mem` stay supply fields.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-support-5 — the selected-outer image supply.**  The four inputs that determine the selected
outer forest of every split choice as a carrier forest: the left-selection predicate (giving the
concrete `leftOf`), the promoted forest family `promotedOf`, their cross-disjointness `cross`, and the
carrier-membership `selectedOuter_mem` of the resulting `leftOf.union promotedOf`.  `promotedOf` and
`selectedOuter_mem` are the genuine de-contraction obligations (the rep/perm promote + carrier
closure), kept as supply fields. -/
structure ResolvedCoassocSelectedOuterImageSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The left-selection supply (giving the concrete left-selected sub-forest `leftOf`). -/
  leftSelection : ResolvedSplitChoiceLeftSelectionSupply D G
  /-- The promoted admissible forest of a split choice (the deferred rep/perm promote). -/
  promotedOf : ResolvedCoassocSplitChoice D G → ResolvedAdmissibleSubgraph G
  /-- The left-selected and promoted components are cross-disjoint (needed for the union). -/
  cross : ∀ s, ∀ γ ∈ (leftSelection.leftOf s).elements, ∀ δ ∈ (promotedOf s).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- The selected outer forest `leftOf.union promotedOf` is a carrier forest (the sub-forest-closure
  obligation). -/
  selectedOuter_mem : ∀ s,
    (leftSelection.toPromoteSupply promotedOf cross).selectedOuterRawOf s ∈ D.carrier G

/-- The promote supply assembled from the left selection + promote inputs. -/
noncomputable def ResolvedCoassocSelectedOuterImageSupply.promoteSupply
    (S : ResolvedCoassocSelectedOuterImageSupply D G) : ResolvedForestPromoteSupply D G :=
  S.leftSelection.toPromoteSupply S.promotedOf S.cross

/-- The bundled `ResolvedCoassocSelectedOuterSupply` (raw selected outer forest + carrier membership),
reusing the support-2 `selectedOuterRawOf`. -/
noncomputable def ResolvedCoassocSelectedOuterImageSupply.toSelectedOuterSupply
    (S : ResolvedCoassocSelectedOuterImageSupply D G) : ResolvedCoassocSelectedOuterSupply D G where
  selectedOuterRaw := fun s => S.promoteSupply.selectedOuterRawOf s
  selectedOuter_mem := S.selectedOuter_mem

/-- The selected-outer map `ResolvedCoassocSplitChoice D G → {A // A ∈ D.carrier G}` for the image
supply — `⟨selectedOuterRaw s, selectedOuter_mem s⟩` via the existing
`ResolvedCoassocSelectedOuterSupply.toSelectedOuterOf` bridge. -/
noncomputable def ResolvedCoassocSelectedOuterImageSupply.selectedOuterOf
    (S : ResolvedCoassocSelectedOuterImageSupply D G) :
    ResolvedCoassocSplitChoice D G → {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G} :=
  S.toSelectedOuterSupply.toSelectedOuterOf

/-- **R-6c-support-5 — the image-supply skeleton.**  Given the selected-outer map (assembled above) and
the still-deferred quotient forest, image weight, and discriminator as inputs, produce a full
`ResolvedCoassocSplitPhiImageSupply D G`.  This closes the selected-outer wiring into the image side:
the only remaining image-side work is supplying `quotientForestOf` / `imageWeightOf` /
`discriminatorOf` (and discharging `promotedOf` / `selectedOuter_mem`). -/
noncomputable def ResolvedCoassocSelectedOuterImageSupply.toImageSupplySkeleton
    (S : ResolvedCoassocSelectedOuterImageSupply D G)
    (quotientForestOf : (s : ResolvedCoassocSplitChoice D G) →
      ResolvedAdmissibleSubgraph
        ((S.selectedOuterOf s).1.contractWithStars (D.starOf G (S.selectedOuterOf s).1)))
    (imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3)
    (discriminatorOf : ResolvedCoassocQuotientImage D G → Prop) :
    ResolvedCoassocSplitPhiImageSupply D G where
  selectedOuterOf := S.selectedOuterOf
  quotientForestOf := quotientForestOf
  imageWeightOf := imageWeightOf
  discriminatorOf := discriminatorOf

end GaugeGeometry.QFT.Combinatorial
