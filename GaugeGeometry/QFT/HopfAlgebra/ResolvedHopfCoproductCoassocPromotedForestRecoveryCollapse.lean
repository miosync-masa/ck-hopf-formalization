import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocComponentToForestConcreteScout

/-!
# R-6c-body-189 — promoted/forest-recovery collapse: the deep leaf PROVED by a biUnion collapse

Hundred-and-eighty-ninth genuine-body step, closing the forward-outer deep leaf.  Body-188 reduced the
de-contraction round-trip to a per-component collapse (`promotedComponentElements ⟨γ,_⟩ = {γ}` on the forest
region); this body runs the biUnion over all recovered components and lands on `forestRecovered` — **proving**
body-179's `promoted_region_eq` from the body-188 compatibility.

## The collapse

`promotedOf recovered .elements = unionOuter.elements.attach.biUnion promotedComponentElements` (`rfl`).  Split the
`unionOuter` components by `union_eq` (body-145) into the three regions:

* **`leftResidual` / `rightRecovered`** — tagged `inl true` / `inl false` (body-146 `left_tag` / `right_tag`), so
  `promotedComponentElements` is the `inl` branch `∅`;
* **`forestRecovered`** — `promotedComponentElements ⟨γ,_⟩ = {γ}` (body-188's
  `promotedComponentElements_forestRecovered`).

So the biUnion is `∅ ∪ ∅ ∪ ⋃_{γ ∈ forestRecovered} {γ} = forestRecovered .elements`.  Concretely, `Finset.ext` +
`Finset.mem_biUnion`: a promoted element must come from a forest component (the `inl` branches are empty), where it
is the parent `γ` itself; conversely each `γ ∈ forestRecovered ⊆ unionOuter` contributes `{γ}`.

## The result

`ResolvedPromotedForestRecoveryCollapseSupply D S Region` bundles body-188's compatibility `Compat`, and
`.promoted_region_eq` is **PROVED**:

```text
(promotedOf recovered).elements = (Region.Union.forestRecovered z).elements
```

This is exactly body-179's `promoted_region_eq` field — so the forward-outer forest-recovery box no longer fields it
(`.toPromotedRegionRoundTripSupply` — body-175's supply — follows too).  The whole de-contraction round-trip is now
proved from the three compatibility leaves of body-188: `forestTag`, `recoverChoice_forest_eq`, `promote_collapse`.

## Consequence — the forward-outer geometry floor

The forward-outer partition's genuinely geometric residual is now exactly the body-188 compatibility:

* `forestTag` — the forest index of a recovered parent;
* `recoverChoice_forest_eq` — the tag pinning (`recoverChoice = inr forestTag` on the forest region);
* `promote_collapse` — `(promote γ (forestTag …)).elements = {γ}` (the recovered forest tag is the whole component).

plus `forestComponentMem` (body-185) and the star/remnant classifier `represented_cases` (body-180).  Everything
structural above these is proved.

Per the HALT: `promote_collapse` / `recoverChoice_forest_eq` bodies are not entered; only the biUnion collapse over
the compatibility is proved; the region tags (`left_tag` / `right_tag`) and `union_eq` are reused from
bodies 146/145.

Landed:

* `ResolvedPromotedForestRecoveryCollapseSupply D S Region` — the body-188 compatibility bundle;
* `.promoted_region_eq` — body-179's field (PROVED by the biUnion collapse);
* `.toPromotedRegionRoundTripSupply` — body-175's supply from it.

Toolkit body (like body-181, the coverage assembly).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-189 — the promoted/forest-recovery collapse supply.**  Body-188's componentToForest / promote
compatibility, from which the de-contraction round-trip `promotedOf recovered = forestRecovered` is proved. -/
structure ResolvedPromotedForestRecoveryCollapseSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-188's componentToForest / promote compatibility. -/
  Compat : ResolvedComponentToForestPromoteCompatibility D S Region

namespace ResolvedPromotedForestRecoveryCollapseSupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-189 — body-179's `promoted_region_eq` by the biUnion collapse.**  The promoted forest of the
recovered choice equals the forest-recovered region: the `inl` regions contribute `∅`, and each forest parent
contributes its own singleton. -/
theorem promoted_region_eq (F : ResolvedPromotedForestRecoveryCollapseSupply D S Region)
    {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G) :
    ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.forestRecovered z).elements := by
  have hinl : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements})
      (b : Bool),
      ResolvedCoassocSplitChoice.choiceAt
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ
        = Sum.inl b →
      ResolvedCoassocSplitChoice.promotedComponentElements
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ = ∅ := by
    intro γ b h
    unfold ResolvedCoassocSplitChoice.promotedComponentElements
    rw [h]
  have bridge : ∀ (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (Region.Union.unionOuter z).1.elements}),
      ResolvedCoassocSplitChoice.choiceAt
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G) γ
        = Region.recoverChoice z γ (Finset.mem_attach _ _) := fun γ => rfl
  have hpe : ((S.Forward.imageSupply G).promotedOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).elements
      = (Region.Union.unionOuter z).1.elements.attach.biUnion
        (ResolvedCoassocSplitChoice.promotedComponentElements
          (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) := rfl
  rw [hpe]
  ext x
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨γ, -, hx⟩
    have hγu : γ.1 ∈ (Region.Union.unionOuter z).1.elements := γ.2
    rcases Finset.mem_union.mp ((Finset.ext_iff.mp (Region.Union.union_eq z) γ.1).mp hγu) with hlr | hf
    · exfalso
      rcases Finset.mem_union.mp hlr with hl | hr
      · rw [hinl γ true ((bridge γ).trans (Region.left_tag z γ hl))] at hx
        simp at hx
      · rw [hinl γ false ((bridge γ).trans (Region.right_tag z γ hr))] at hx
        simp at hx
    · rw [F.Compat.promotedComponentElements_forestRecovered z γ hf, Finset.mem_singleton] at hx
      subst hx
      exact hf
  · intro hx
    have hxu : x ∈ (Region.Union.unionOuter z).1.elements :=
      (Finset.ext_iff.mp (Region.Union.union_eq z) x).mpr (Finset.mem_union.mpr (Or.inr hx))
    refine ⟨⟨x, hxu⟩, Finset.mem_attach _ _, ?_⟩
    rw [F.Compat.promotedComponentElements_forestRecovered z ⟨x, hxu⟩ hx]
    exact Finset.mem_singleton_self x

/-- **R-6c-body-189 — body-175's promotion supply from the collapse.** -/
def toPromotedRegionRoundTripSupply (F : ResolvedPromotedForestRecoveryCollapseSupply D S Region) :
    ResolvedPromotedRegionRoundTripSupply D S Region where
  promoted_region_eq := fun {G} z => F.promoted_region_eq z

end ResolvedPromotedForestRecoveryCollapseSupply

end GaugeGeometry.QFT.Combinatorial
