import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightFactorGen

/-!
# R-6c-heart-6a-4 (scout) — the remnant embedding target, named precisely

**Scout decision (remnant vs survivor).**  Unlike the survivor (a disjoint component re-embedded
unchanged, 6a-3), the remnant of a forest choice `B ⊆ γ` is a genuine **de-contraction**:

* `fullQuotientOf.remnantComponents` are **built from** `M.remnantComponent` (5b-4), so routing the
  embedding "through `fullQuotientOf`" is circular — `M.remnantComponent` must be constructed;
* `localizeRemnantComponent` (`ResolvedActualSigmaCover`) runs the **opposite** direction (a
  whole-`Aout` quotient remnant → its single parent), the inverse of the forest-choice → remnant map,
  so it is not a drop-in;
* the remnant **generator target** is exactly the contracted source forest:
  `remnantGen` must hit `rightTerm B = X ((B.contractWithStars (D.starOf γGraph B)).toResolvedHopfGen)`
  — i.e. `B` contracted *inside `γ`'s graph*.  Matching it to the remnant component in
  `selectedOuter.contractWithStars` is the **same contract-twice = contract-once geometry** as `right_eq`
  (5c-2).

So the remnant embedding stays a supply (the heavy de-contraction); this file names the exact target.

Landed (first helper):

* `ForestChoiceOccurrence.sourceForest` / `contractedSourceGraph` / `rightTermOf` — the remnant's source
  forest, its in-`γ` contraction graph, and the `rightTerm` it must reproduce;
* `rightFactorOf_eq_rightTerm_of_choiceAt_inr` — a forest-choice component's right factor **is**
  `rightTerm B` (so `remnant_region_eq`'s `remnantGen` target is exactly this gen).

No facade, no flat term, no `forgetHopf`, no rep/perm.  The de-contraction construction of
`M.remnantComponent` (and its `remnantGen`) is the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-4 — the remnant's source forest.**  The chosen sub-forest `B` of the component
graph `γ.toResolvedFeynmanGraph`. -/
def ResolvedCoassocSplitChoice.ForestChoiceOccurrence.sourceForest
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) :
    ResolvedAdmissibleSubgraph o.γ.1.toResolvedFeynmanGraph := o.B.1

/-- **R-6c-heart-6a-4 — the remnant's in-`γ` contraction graph.**  `B` contracted inside `γ`'s graph —
the graph whose resolved class is the remnant generator target. -/
noncomputable def ResolvedCoassocSplitChoice.ForestChoiceOccurrence.contractedSourceGraph
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) : ResolvedFeynmanGraph :=
  o.B.1.contractWithStars (D.starOf o.γ.1.toResolvedFeynmanGraph o.B.1)

/-- **R-6c-heart-6a-4 — the `rightTerm` the remnant must reproduce.**  The forest-choice right factor
`rightTerm B` (a single generator of the contracted source graph). -/
noncomputable def ResolvedCoassocSplitChoice.ForestChoiceOccurrence.rightTermOf
    {s : ResolvedCoassocSplitChoice D G} (o : s.ForestChoiceOccurrence) : ResolvedHopfH :=
  (D.supply o.γ.1.toResolvedFeynmanGraph).rightTerm o.B

/-- **R-6c-heart-6a-4 — a forest-choice component's right factor is `rightTerm B`.**  So the remnant
generator target (`remnant_region_eq`'s `remnantGen`) is exactly `(D.supply γGraph).rightTerm B`. -/
theorem rightFactorOf_eq_rightTerm_of_choiceAt_inr
    {s : ResolvedCoassocSplitChoice D G} {γ : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements}}
    {B : (D.supply γ.1.toResolvedFeynmanGraph).ForestIdx} (hc : s.choiceAt γ = Sum.inr B) :
    D.rightFactorOf s γ = (D.supply γ.1.toResolvedFeynmanGraph).rightTerm B := by
  unfold ResolvedCoproductProperForestData.rightFactorOf
    ResolvedCoproductProperForestData.localChoiceRightFactor
  rw [hc]
  rfl

end GaugeGeometry.QFT.Combinatorial
