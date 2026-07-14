import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegionConstructionFromSector

/-!
# R-6c-body-277 — the S-free region construction core (PROVED)

Two-hundred-and-seventy-seventh genuine-body step — the phantom-`S`-free reduct of body-156's region construction.  The
scout (body-273) established that `ResolvedRegionConstructionFromSectorSupply D S` never reads `S`: every field is
phrased over `z : ForestBlockCodType D G`, `rightDomain z`, `forestDomain z` alone.  Here the six genuine fields are
re-declared with `S` removed from the declaration type, and the `rightRecovered` / `forestRecovered` methods (and their
`rfl` element shapes) are re-derived identically.  This removes the last declaration-level `S` blocker from the
value-root region layer (bodies 275/276 carried `S` only as a phantom index on `Construction`).

## The S-free core

`ResolvedRegionConstructionFromSectorValueSupply D` fields exactly body-156's six geometry fields
(`componentToRight` / `rightComponentCD` / `rightComponentDisjoint` and the forest mirror), verbatim, with `S` gone.
`rightRecovered` / `forestRecovered` are the same `ofElements` images; `rightRecovered_elements_eq` /
`forestRecovered_elements_eq` are `rfl` (the success criterion: element shape unchanged).

## Migration check (not canonical)

`ResolvedRegionConstructionFromSectorSupply.toValueCore` copies the six fields from the old `S`-indexed supply — a
field-by-field `rfl` reduct, confirming the S-free core is a faithful reduct.  It references the old bundle only for the
migration check; the canonical path (body-278) re-keys the right/forest bridges onto the S-free core directly, never
through `toValueCore`.

Per the HALT: only the S-free core + its two recovered methods (+ `rfl` element shapes) + the migration converter are
defined; the right/forest bridge re-key and the recovered-membership assembly are NOT entered.  No facade, no flat term,
no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-277 — the S-free region construction core.**  Body-156's six geometry fields with `S` removed from the
declaration type; every field reads only `z` / `rightDomain z` / `forestDomain z`. -/
structure ResolvedRegionConstructionFromSectorValueSupply (D : ResolvedCoproductProperForestData) where
  /-- A survivor component pulled back to its source outer component. -/
  componentToRight : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x // x ∈ rightDomain z} → ResolvedFeynmanSubgraph G
  /-- Each recovered right component is connected-divergent. -/
  rightComponentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ rightDomain z}), (componentToRight z δ).forget.IsConnectedDivergent
  /-- The recovered right components are pairwise disjoint. -/
  rightComponentDisjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ ⦃γ⦄, γ ∈ (rightDomain z).attach.image (componentToRight z) →
    ∀ ⦃δ⦄, δ ∈ (rightDomain z).attach.image (componentToRight z) → γ ≠ δ → γ.Disjoint δ
  /-- A remnant component pulled back to its forest-choice parent. -/
  componentToForest : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    {x // x ∈ forestDomain z} → ResolvedFeynmanSubgraph G
  /-- Each recovered forest parent is connected-divergent. -/
  forestComponentCD : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (δ : {x // x ∈ forestDomain z}), (componentToForest z δ).forget.IsConnectedDivergent
  /-- The recovered forest parents are pairwise disjoint. -/
  forestComponentDisjoint : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ∀ ⦃γ⦄, γ ∈ (forestDomain z).attach.image (componentToForest z) →
    ∀ ⦃δ⦄, δ ∈ (forestDomain z).attach.image (componentToForest z) → γ ≠ δ → γ.Disjoint δ

namespace ResolvedRegionConstructionFromSectorValueSupply

/-- **R-6c-body-277 — the recovered right region** (S-free; same `ofElements` as body-156). -/
noncomputable def rightRecovered (T : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements ((rightDomain z).attach.image (T.componentToRight z))
    (by
      intro δ hδ
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ
      exact T.rightComponentCD z γ)
    (T.rightComponentDisjoint z)

/-- **R-6c-body-277 — the recovered forest region** (S-free; same `ofElements` as body-156). -/
noncomputable def forestRecovered (T : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) : ResolvedAdmissibleSubgraph G :=
  ResolvedAdmissibleSubgraph.ofElements ((forestDomain z).attach.image (T.componentToForest z))
    (by
      intro δ hδ
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hδ
      exact T.forestComponentCD z γ)
    (T.forestComponentDisjoint z)

/-- **R-6c-body-277 — the right region's element shape** (`rfl`; success criterion). -/
@[simp] theorem rightRecovered_elements_eq (T : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (T.rightRecovered z).elements = (rightDomain z).attach.image (T.componentToRight z) :=
  rfl

/-- **R-6c-body-277 — the forest region's element shape** (`rfl`; success criterion). -/
@[simp] theorem forestRecovered_elements_eq (T : ResolvedRegionConstructionFromSectorValueSupply D)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    (T.forestRecovered z).elements = (forestDomain z).attach.image (T.componentToForest z) :=
  rfl

end ResolvedRegionConstructionFromSectorValueSupply

/-- **R-6c-body-277 — the S-free reduct of the old S-indexed region supply** (migration check, field-by-field `rfl`).
Not on the canonical path — body-278 re-keys the bridges onto the S-free core directly. -/
def ResolvedRegionConstructionFromSectorSupply.toValueCore
    {S : ResolvedConcreteSummandBundleSupply D} (T : ResolvedRegionConstructionFromSectorSupply D S) :
    ResolvedRegionConstructionFromSectorValueSupply D where
  componentToRight := T.componentToRight
  rightComponentCD := T.rightComponentCD
  rightComponentDisjoint := T.rightComponentDisjoint
  componentToForest := T.componentToForest
  forestComponentCD := T.forestComponentCD
  forestComponentDisjoint := T.forestComponentDisjoint

end GaugeGeometry.QFT.Combinatorial
