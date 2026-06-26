import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPartition
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnant

/-!
# R-6c-heart-5c-1g — right factor assembly (region → quotient forest)

The right-factor partition (5c-1f) gives `rightFactorProduct s = (∏ rightComponents) * (∏ forestComponents)`.
The two regions identify with the quotient forest's two halves:

* the right-primitive region `∏ rightComponents, rightFactorOf` with the **right survivors**
  (`resolvedForestLeftTerm (rightSurvivorForest s)`);
* the forest region `∏ forestComponents, rightFactorOf` with the **remnants**
  (`resolvedForestLeftTerm (remnantForest s)`).

Those identifications (`hRight` / `hForest`) tie the local right factors to the **supply** survivor /
remnant embeddings (the abstract `survivorComponent` / `remnantComponent` and their generator
equalities), so — per the HALT — they are taken as hypotheses.  Given them, the assembly is the union

  `rightFactorProduct s = resolvedForestLeftTerm (remnantForest s ⊔ rightSurvivorForest s)`,

the quotient forest term (`= resolvedForestLeftTerm (imageOf s).quotientForest`, the right factor of
`product_eq`).  The union is via `resolvedForestLeftTerm_union` (5c-1b) and `mul_comm`.

Landed:

* `rightFactorProduct_eq_quotientForestTerm` — the assembly (given the two region equalities + the
  remnant/survivor cross- and Finset-disjointness).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The region equalities `hRight`/`hForest` (the
survivor/remnant generator equalities), the `toImage` identification, and `right_eq` remain.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-5c-1g — the right factor assembly.**  Given that the right-primitive region is the
right-survivor term (`hRight`) and the forest region is the remnant term (`hForest`), the right factor
product is the quotient forest term `resolvedForestLeftTerm (remnantForest s ⊔ rightSurvivorForest s)`.
The survivor/remnant cross-disjointness (`hCross`) builds the union; the Finset-disjointness (`hDisj`)
splits the forest left term. -/
theorem ResolvedCoproductProperForestData.rightFactorProduct_eq_quotientForestTerm
    (D : ResolvedCoproductProperForestData) {G : ResolvedFeynmanGraph}
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G)
    (s : ResolvedCoassocSplitChoice D G)
    (hRight : (∏ γ ∈ s.rightComponents, D.rightFactorOf s γ)
      = resolvedForestLeftTerm (R.rightSurvivorForest s))
    (hForest : (∏ γ ∈ s.forestComponents, D.rightFactorOf s γ)
      = resolvedForestLeftTerm (M.remnantForest s))
    (hCross : ∀ γ ∈ (M.remnantForest s).elements, ∀ δ ∈ (R.rightSurvivorForest s).elements,
        γ ≠ δ → γ.Disjoint δ)
    (hDisj : Disjoint (M.remnantForest s).elements (R.rightSurvivorForest s).elements) :
    D.rightFactorProduct s
      = resolvedForestLeftTerm ((M.remnantForest s).union (R.rightSurvivorForest s) hCross) := by
  rw [D.rightFactorProduct_eq_rightPart_mul_forestPart, hRight, hForest, mul_comm,
    ← resolvedForestLeftTerm_union (M.remnantForest s) (R.rightSurvivorForest s) hCross hDisj]

end GaugeGeometry.QFT.Combinatorial
