import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForwardOuterCollectionCore

/-!
# R-6c-body-339 — the promoted forest-tag collection: `⋃ (promote γ (forestTag)) = promotedTouchedUnion` (PROVED)

Three-hundred-and-thirty-ninth genuine-body step — the honest, `promote_collapse`-FREE replacement for the
forest branch of `promotedOf(recovered) = forestRecovered`.  The old body-289 route reduced each promoted
forest component to the SINGLETON `{γ}` via `promote_collapse` (FALSE for a multi-star `B`).  Here each
promoted forest-recovered component is instead the touched COLLECTION `touchedOuterComponents z (forestSource γ)`,
and their union is body-334's `promotedTouchedUnion z`.

## The transport

`M.forestTag F z γ : (D.supply γ.1.toResolvedFeynmanGraph).ForestIdx` is body-333's CONSTRUCTED tag; it is
heterogeneously the source's `innerIdx` (`forestTag_heq_source`).  Since `parent (forestSource γ) = γ.1`
(`forestSource_spec`) is an equality of the outer subgraph, the `HEq` transports across `promote`'s
subgraph-dependent second argument (`promote_heq_congr`), landing each promoted component on body-334's
`promote_parent_innerIdx_elements = touchedOuterComponents z (forestSource γ)` — no `promote_collapse`, no
`{γ}` singleton.

Landed (all axiom-clean):

* `promote_heq_congr` — `promote` respects `HEq` of the `ForestIdx` along an equality of the outer subgraph;
* `promote_forestTag_elements` — `(promote γ.1 (forestTag z γ).1).elements = touchedOuterComponents z (forestSource γ)`;
* `promotedForestBiUnion_eq_promotedTouched` — the biUnion over `forestRecoveredMulti` equals
  `promotedTouchedUnion z` (reverse reindex via `forestSource_parent`, the D4-uniqueness datum needing `Measure`).

Per the HALT: only the promoted forest-tag COLLECTION identity is proved — the `promote_collapse` replacement.
The full `promotedOf(recovered) = promotedTouchedUnion` (the `inl → ∅` tag reduction over a concrete
`ResolvedRegionTagValueSupply`), the `leftOf` pure-tag equality, and the `selectedOuterRawOf` elements
equality (body-334 union) are the region-wiring body (340) — they need the concrete `T` (Region/Left/Closure)
and stay closure-conditional; `recovered_raw_mem` / forward-quotient / `forestTag_agrees` remain model gates.
No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton anywhere.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-339 — `promote` respects `HEq` of the tag along an outer-subgraph equality.**  When `a = b`
and the `ForestIdx`s are heterogeneously equal, the two promotions coincide. -/
theorem promote_heq_congr {G : ResolvedFeynmanGraph} {a b : ResolvedFeynmanSubgraph G}
    (hab : a = b) {X : (D.supply a.toResolvedFeynmanGraph).ForestIdx}
    {Y : (D.supply b.toResolvedFeynmanGraph).ForestIdx} (hXY : HEq X Y) :
    ResolvedAdmissibleSubgraph.promote a X.1 = ResolvedAdmissibleSubgraph.promote b Y.1 := by
  subst hab
  rw [eq_of_heq hXY]

namespace ResolvedMultiStarDecontractionSupply

variable (M : ResolvedMultiStarDecontractionSupply D) {G : ResolvedFeynmanGraph}

/-- **R-6c-body-339 — each promoted forest-recovered component is its source's touched collection.**  The
`promote_collapse`-free leaf: NOT the singleton `{γ}`, but `touchedOuterComponents z (forestSource γ)`. -/
theorem promote_forestTag_elements (F : ResolvedCanonicalStarFacts D) (z : ForestBlockCodType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ (M.forestRecoveredMulti F z).elements}) :
    (ResolvedAdmissibleSubgraph.promote γ.1 (M.forestTag F z γ).1).elements
      = touchedOuterComponents z (M.forestSource F z γ).1 := by
  rw [← M.promote_parent_innerIdx_elements z (M.forestSource F z γ)]
  exact congrArg ResolvedAdmissibleSubgraph.elements
    (promote_heq_congr (M.forestSource_spec F z γ).symm (M.forestTag_heq_source F z γ))

/-- **R-6c-body-339 — the promoted forest-tag union equals body-334's `promotedTouchedUnion`.**  The forest
branch of `promotedOf(recovered)`, reindexed against `forestDomain` via `forestSource` (reverse needs the
D4-uniqueness `forestSource_parent`, hence `Measure`). -/
theorem promotedForestBiUnion_eq_promotedTouched (F : ResolvedCanonicalStarFacts D)
    (Measure : ResolvedMeasureLeafSupply D) (z : ForestBlockCodType D G) :
    (M.forestRecoveredMulti F z).elements.attach.biUnion
        (fun γ => (ResolvedAdmissibleSubgraph.promote γ.1 (M.forestTag F z γ).1).elements)
      = M.promotedTouchedUnion z := by
  ext x
  constructor
  · intro hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨γ, -, hxγ⟩ := hx
    rw [M.promote_forestTag_elements F z γ] at hxγ
    rw [promotedTouchedUnion, Finset.mem_biUnion]
    refine ⟨M.forestSource F z γ, Finset.mem_attach _ _, ?_⟩
    rw [M.promote_parent_innerIdx_elements]; exact hxγ
  · intro hx
    rw [promotedTouchedUnion, Finset.mem_biUnion] at hx
    obtain ⟨δ, -, hxδ⟩ := hx
    rw [M.promote_parent_innerIdx_elements] at hxδ
    have hmem : M.parent z δ ∈ (M.forestRecoveredMulti F z).elements := by
      rw [M.forestRecoveredMulti_elements F z]
      exact Finset.mem_image.mpr ⟨δ, Finset.mem_attach _ _, rfl⟩
    rw [Finset.mem_biUnion]
    refine ⟨⟨M.parent z δ, hmem⟩, Finset.mem_attach _ _, ?_⟩
    rw [M.promote_forestTag_elements F z ⟨M.parent z δ, hmem⟩,
      M.forestSource_parent F Measure z δ hmem]
    exact hxδ

end ResolvedMultiStarDecontractionSupply

end GaugeGeometry.QFT.Combinatorial
