import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightRecoveredSectorScout

/-!
# R-6c-body-219 — right image correspondence scout: reduced to `componentToRight` sound + complete

Two-hundred-and-nineteenth genuine-body step, a scout that turned into a reduction of body-213's
`right_image_correspondence` — the lightest of the four sector correspondences — into the two `componentToRight`
round-trip directions.

## The scout finding — both directions are fresh region-map obligations

`Finset.mem_image` gives `γ ∈ s.attach.image f ↔ ∃ δ ∈ s.attach, f δ = γ`, so the correspondence splits into:

* **sound** — `δ ∈ rightDomain (fwdMap q) → rightPrimSelected q (componentToRight δ)`: the `componentToRight` image
  of a star-avoiding component is a right-primitive parent;
* **complete** — `rightPrimSelected q γ → ∃ δ ∈ rightDomain (fwdMap q), componentToRight δ = γ`: every right-primitive
  parent is a `componentToRight` image.

Both are **fresh**: body-156's region `componentToRight` is an abstract field with only `rightComponentCD` /
`rightComponentDisjoint` (no soundness), and — confirmed — it is *nowhere wired* to the sector `componentToRight`
(which lands in `RightPrimitiveIndex`, carrying the `inl false` witness `hR`).  So neither direction follows from
`componentToRight_spec` / `right_surj` at the region level.

**The deeper win (deferred).**  The genuine floor is the sector inverse: the sector `componentToRight` already lands
in `RightPrimitiveIndex` whose `hR : isRight` *is* the `inl false` tag, so a wiring bridge identifying the region map
with the sector one would collapse both `sound` / `complete` into `right_surj` / `componentToRight_spec` +
`rightPrimSelected_iff_choice`.  Until that bridge exists, `sound` / `complete` are the honest floor.

## The reduction (PROVED, term-mode `mem_image`)

`ResolvedRightImageCorrespondenceDecompositionSupply D S Region` fields body-156's construction and the two fresh
directions `right_sound` / `right_complete`.  Then `.right_image_correspondence` is **proved** by term-mode
`Finset.mem_image.mp` / `.mpr` (the `@[simp]` form does not fire through `simp` due to the `DecidableEq
(ResolvedFeynmanSubgraph G)` instance mismatch — body-211's finding — but term-mode elaboration unifies the instance
from the goal, as body-156 itself does).  `.toRightRecoveredSectorDecompositionSupply` (given the wiring bridge
`rightRecovered_eq`) produces body-213's supply, so the right sector leaf reduces to `right_sound` / `right_complete`.

## Consequence

The right sector correspondence is now the two fresh `componentToRight` round-trip directions.  Everything downstream
(body-213 → body-170 → the backward-outer / choice floors) is proved.  The forest and survivor correspondences
remain (body-218's plan: forest next, survivor last).

Per the HALT: the `componentToRight` round-trip body (soundness / completeness) is not entered; the sector inverse is
not wired; only the `mem_image` assembly is proved.

Landed:

* `ResolvedRightImageCorrespondenceDecompositionSupply D S Region` — body-156's construction + `sound` + `complete`;
* `.right_image_correspondence` — body-213's leaf (PROVED from the two directions);
* `.toRightRecoveredSectorDecompositionSupply` — body-213's supply (given the wiring bridge).

Scout / toolkit body (like body-213).  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-219 — the right image correspondence decomposition supply.**  Body-156's sector region construction
and the two fresh `componentToRight` round-trip directions (soundness / completeness). -/
structure ResolvedRightImageCorrespondenceDecompositionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-156's sector region construction. -/
  Construction : ResolvedRegionConstructionFromSectorSupply D S
  /-- Sound: a `componentToRight` image of a star-avoiding component is a right-primitive parent. -/
  right_sound : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (δ : {x // x ∈ rightDomain (fwdMap S q)}),
    rightPrimSelected q (Construction.componentToRight (fwdMap S q) δ)
  /-- Complete: every right-primitive parent is a `componentToRight` image. -/
  right_complete : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : ResolvedFeynmanSubgraph G),
    rightPrimSelected q γ →
    ∃ δ : {x // x ∈ rightDomain (fwdMap S q)}, Construction.componentToRight (fwdMap S q) δ = γ

namespace ResolvedRightImageCorrespondenceDecompositionSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-219 — body-213's `right_image_correspondence` from `sound` + `complete`.** -/
theorem right_image_correspondence
    (F : ResolvedRightImageCorrespondenceDecompositionSupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) (γ : ResolvedFeynmanSubgraph G) :
    γ ∈ (rightDomain (fwdMap S q)).attach.image (F.Construction.componentToRight (fwdMap S q))
      ↔ rightPrimSelected q γ := by
  constructor
  · intro h
    obtain ⟨δ, _, rfl⟩ := Finset.mem_image.mp h
    exact F.right_sound q δ
  · intro hγ
    obtain ⟨δ, hδ⟩ := F.right_complete q γ hγ
    exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, hδ⟩

/-- **R-6c-body-219 — body-213's right recovered sector decomposition supply** (given the wiring bridge). -/
def toRightRecoveredSectorDecompositionSupply
    (F : ResolvedRightImageCorrespondenceDecompositionSupply D S Region)
    (rightRecovered_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (Region.Union.rightRecovered (fwdMap S q)).elements
        = (F.Construction.rightRecovered (fwdMap S q)).elements) :
    ResolvedRightRecoveredSectorDecompositionSupply D S Region where
  Construction := F.Construction
  rightRecovered_eq := fun {G} q => rightRecovered_eq q
  right_image_correspondence := fun {G} q γ => F.right_image_correspondence q γ

end ResolvedRightImageCorrespondenceDecompositionSupply

end GaugeGeometry.QFT.Combinatorial
