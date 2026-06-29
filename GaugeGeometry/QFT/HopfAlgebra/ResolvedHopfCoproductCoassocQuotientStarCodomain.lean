import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientStarIndexNormal
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarIndexRecover

/-!
# R-6c-heart-6a-10b — quotient-star codomain split from the full-quotient `Right ⊔ Remnant`

The codomain normal form (6a-10a, fielded as `ResolvedQuotientStarCodomainSplitSupply`) is concretised
here: the two-stage stars `≃ {δ ∈ quotientForest.elements}` (6a-8b-2), and the `Right ⊔ Remnant`
decomposition (5b-4) splits `quotientForest.elements = rightElements ∪ remnantElements` (disjoint), giving
`{δ ∈ quotientForest} ≃ {δ ∈ right} ⊕ {δ ∈ remnant}`.

So the codomain is built from two genuine but light facts — `quotientForest.elements = right ∪ remnant`
and their disjointness — both kept as supply fields.

Per the HALT, the `right` / `remnant` sector correspondences (`rightEquiv` / `forestEquiv`) are NOT built,
no remnant/survivor gen equality, no term/edge/retarget.

Landed:

* `disjointUnionSubtypeEquiv` — the generic disjoint-union subtype splitter;
* `ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf` — the `quotientForest.elements =
  right ∪ remnant` + disjoint data;
* `.toCodomainSplitSupply` — the concrete `ResolvedQuotientStarCodomainSplitSupply` (codomain normal form).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

/-- **R-6c-heart-6a-10b — the generic disjoint-union subtype splitter.**  `{x ∈ R ∪ M} ≃ {x ∈ R} ⊕ {x ∈ M}`
when `R`, `M` are disjoint. -/
def disjointUnionSubtypeEquiv {α : Type*} [DecidableEq α] {R M : Finset α} (hD : Disjoint R M) :
    {x : α // x ∈ R ∪ M} ≃ ({x : α // x ∈ R} ⊕ {x : α // x ∈ M}) where
  toFun := fun x => if hR : x.1 ∈ R then Sum.inl ⟨x.1, hR⟩
    else Sum.inr ⟨x.1, (Finset.mem_union.mp x.2).resolve_left hR⟩
  invFun := fun y => Sum.elim (fun r => ⟨r.1, Finset.mem_union_left _ r.2⟩)
    (fun m => ⟨m.1, Finset.mem_union_right _ m.2⟩) y
  left_inv := fun x => by
    rcases x with ⟨x, hx⟩
    by_cases hR : x ∈ R
    · simp only [dif_pos hR, Sum.elim_inl]
    · simp only [dif_neg hR, Sum.elim_inr]
  right_inv := fun y => by
    cases y with
    | inl r => simp only [Sum.elim_inl, dif_pos r.2]
    | inr m =>
        have hnr : m.1 ∉ R := fun hR => Finset.disjoint_left.mp hD hR m.2
        simp only [Sum.elim_inr, dif_neg hnr]

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-heart-6a-10b — the full-quotient codomain data.**  The `Right ⊔ Remnant` split of the quotient
forest's elements (5b-4): the right-survivor / remnant element sets, their union being all of the quotient
forest, and their disjointness. -/
structure ResolvedQuotientStarCodomainFullQuotientSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right-survivor element set. -/
  rightElements : ∀ s : ResolvedCoassocSplitChoice D G,
    Finset (ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
  /-- The remnant element set. -/
  remnantElements : ∀ s : ResolvedCoassocSplitChoice D G,
    Finset (ResolvedFeynmanSubgraph (resolvedCoassocQuotientGraph (imageOf s)))
  /-- The quotient forest is `Right ∪ Remnant`. -/
  elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (imageOf s).quotientForest.elements = rightElements s ∪ remnantElements s
  /-- `Right` and `Remnant` are disjoint. -/
  disjoint : ∀ s : ResolvedCoassocSplitChoice D G,
    Disjoint (rightElements s) (remnantElements s)

/-- **R-6c-heart-6a-10b — the concrete codomain split supply.** -/
noncomputable def ResolvedQuotientStarCodomainFullQuotientSupply.toCodomainSplitSupply
    (Q : ResolvedQuotientStarCodomainFullQuotientSupply D G imageOf) :
    ResolvedQuotientStarCodomainSplitSupply D G imageOf where
  RightSurvivorIndex := fun s => {δ // δ ∈ Q.rightElements s}
  RemnantIndex := fun s => {δ // δ ∈ Q.remnantElements s}
  codomainEquiv := fun s =>
    (twoStageStarIndexEquivSubtype imageOf s).trans
      ((Equiv.cast (congrArg (fun f => {δ // δ ∈ f}) (Q.elements_eq s))).trans
        (disjointUnionSubtypeEquiv (Q.disjoint s)))

end GaugeGeometry.QFT.Combinatorial
