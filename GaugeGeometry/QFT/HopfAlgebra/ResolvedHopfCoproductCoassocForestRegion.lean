import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPromoteGen

/-!
# R-6c-heart-5c-1e — the global forest region + the left factor equality

The forest region of `leftFactorProduct` is identified with the promoted forest term:

  `∏ γ ∈ forestComponents, leftFactorOf s γ = resolvedForestLeftTerm (promotedOf s)`,

via `Finset.prod_biUnion` over the `promotedElements` biUnion (`promotedOf.elements =
attach.biUnion promotedComponentElements`), the per-parent equality
`leftFactorOf_eq_promote_of_forestChoice` (5c-1d), and the empty contribution of non-forest components.

`prod_biUnion` needs the per-parent promoted sets to be **pairwise disjoint as Finsets** — for distinct
outer parents the promoted pieces sit in vertex-disjoint regions, so they are distinct *provided the
components are nonempty*.  The carrier `D.carrier` is parametric (no nonemptiness guarantee), so — as
throughout this development — that disjointness is taken as a hypothesis (`hPD`), not assumed.

Combining with `leftFactorProduct_eq_leftOf_mul_forestPart` (5c-1c) and `resolvedForestLeftTerm_union`
(5c-1b) finishes the **left factor equality**:

  `leftFactorProduct s = resolvedForestLeftTerm (selectedOuterRaw s)` (= `resolvedSelectedOuterTerm`).

Landed:

* `forestPart_eq_promotedOf` — the forest region equals the promoted forest term (given `hPD`);
* `leftFactorProduct_eq_selectedOuterRawTerm` — the left factor equality (given `hPD` + leftOf/promotedOf
  Finset-disjointness `hLP`).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The nonemptiness-derived `hPD`/`hLP` and
`right_eq` are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1e — the global forest region.**  `∏ γ ∈ forestComponents, leftFactorOf s γ =
resolvedForestLeftTerm (promotedOf s)`, given that the per-parent promoted sets are pairwise disjoint
(`hPD` — true when the promoted components are nonempty, isolated here as the carrier is parametric). -/
theorem forestPart_eq_promotedOf (s : ResolvedCoassocSplitChoice D G)
    (hPD : (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements})
      |>.PairwiseDisjoint s.promotedComponentElements) :
    (∏ γ ∈ s.forestComponents, D.leftFactorOf s γ)
      = resolvedForestLeftTerm ((resolvedPromotedOfSupply D G).promotedOf s) := by
  classical
  symm
  rw [resolvedForestLeftTerm_eq_prod, ResolvedPromotedOfSupply.promotedOf_elements,
    ResolvedCoassocSplitChoice.promotedElements, Finset.prod_biUnion hPD,
    ← Finset.prod_subset (show s.forestComponents ⊆ s.1.1.elements.attach from Finset.filter_subset _ _)
      (fun x _ hx => ?_)]
  · apply Finset.prod_congr rfl
    intro γ hγ
    obtain ⟨B, hc⟩ : ∃ B, s.choiceAt γ = Sum.inr B := (Finset.mem_filter.mp hγ).2
    rw [s.promotedComponentElements_inr hc, ← resolvedForestLeftTerm_eq_prod,
      ← leftFactorOf_eq_promote_of_forestChoice hc]
  · rcases hcx : s.choiceAt x with b | B
    · rw [s.promotedComponentElements_inl hcx, Finset.prod_empty]
    · exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, ⟨B, hcx⟩⟩) hx

/-- **R-6c-heart-5c-1e — the left factor equality.**  `leftFactorProduct s = resolvedForestLeftTerm
(selectedOuterRaw s)` — the left primitives and promoted pieces assemble the selected-outer component
product.  Given `hPD` (forest region) and `hLP` (leftOf/promotedOf Finset-disjointness for the union),
both nonemptiness consequences on the parametric carrier. -/
theorem leftFactorProduct_eq_selectedOuterRawTerm (s : ResolvedCoassocSplitChoice D G)
    (hPD : (↑(s.1.1.elements.attach) : Set {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements})
      |>.PairwiseDisjoint s.promotedComponentElements)
    (hLP : Disjoint ((resolvedConcreteLeftSelectionSupply D G).leftOf s).elements
      ((resolvedPromotedOfSupply D G).promotedOf s).elements) :
    D.leftFactorProduct s
      = resolvedForestLeftTerm ((resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s) := by
  rw [D.leftFactorProduct_eq_leftOf_mul_forestPart, forestPart_eq_promotedOf s hPD,
    ← resolvedForestLeftTerm_union ((resolvedConcreteLeftSelectionSupply D G).leftOf s)
      ((resolvedPromotedOfSupply D G).promotedOf s) (cross_disjoint_leftOf_promotedOf s) hLP]
  rfl

end GaugeGeometry.QFT.Combinatorial
