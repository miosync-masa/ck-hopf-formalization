import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocStarGeometry

/-!
# R-6c-heart-6a-5b — the contract-twice `ClassData` final supply (right + remnant in one record)

`ResolvedContractTwiceClassData` (6a-5a) is the single shape behind both `right_eq` and the remnant
class equality.  This file bundles, per split choice, the **right** datum (whole `A`) and the **remnant**
data (per forest choice) into one record `ResolvedContractTwiceClassDataSupply`, and wires it into the
two real supply chains:

* `.toRemnantDecontractionSupply` — the per-`s` `ResolvedRemnantDecontractionSupply` (6a-4b), giving
  `remnantGen`;
* `toRightEqSupply` — the `ResolvedContractTwiceOnceSupply` (5c-2a), giving `right_eq`.

So the **entire** contract-twice geometry — both `right_eq` and `remnantGen` for every split choice —
flows from one family `∀ s, ResolvedContractTwiceClassDataSupply D G imageOf s`, whose only unfilled
content is `ResolvedContractTwiceClassData` (a star permutation + the three field equalities) for the
relevant graph pairs.

Per the HALT, the star permutation and field equalities are **not** constructed here — this only
completes the wiring, so the last remaining obligation is exactly:

  `∀ relevant graph pair, ResolvedContractTwiceClassData`.

Landed:

* `ResolvedContractTwiceClassDataSupply D G imageOf s` — the right datum + the remnant component/CD/data;
* `.toRemnantDecontractionSupply` — into the remnant chain (`remnantGen`);
* `ResolvedContractTwiceClassDataSupply.toRightEqSupply` — into the right-`eq` chain (`right_eq`).

No facade, no flat term, no `forgetHopf`.  Constructing the `ClassData` (the star geometry) is the
remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-6a-5b — the contract-twice `ClassData` supply.**  Per split choice: the right datum
(whole `A` one/two-stage graphs), and the remnant embedding + CD + per-occurrence `ClassData`.  Its only
unfilled content is `ResolvedContractTwiceClassData` (star permutation + three field equalities). -/
structure ResolvedContractTwiceClassDataSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (s : ResolvedCoassocSplitChoice D G) where
  /-- The right (whole-`A`) contract-twice class datum. -/
  rightClassData : ResolvedContractTwiceClassData (oneStageContractGraph s)
    (twoStageContractGraph imageOf s)
  /-- The remnant embedding of each forest choice into the quotient graph. -/
  remnantComponent : s.ForestChoiceOccurrence → ResolvedFeynmanSubgraph s.selectedOuterContractGraph
  /-- Each remnant component is connected-divergent. -/
  remnantCD : ∀ o, (remnantComponent o).forget.IsConnectedDivergent
  /-- The per-occurrence (per forest choice `B`) contract-twice class data. -/
  remnantClassData : ∀ o, ResolvedContractTwiceClassData
    (remnantComponent o).toResolvedFeynmanGraph o.contractedSourceGraph

/-- **R-6c-heart-6a-5b — into the remnant chain.**  Build the per-`s` `ResolvedRemnantDecontraction
Supply` (whose `remnantGen` then follows). -/
def ResolvedContractTwiceClassDataSupply.toRemnantDecontractionSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G}
    (B : ResolvedContractTwiceClassDataSupply D G imageOf s) :
    ResolvedRemnantDecontractionSupply D G s where
  remnantComponent := B.remnantComponent
  remnantCD := B.remnantCD
  remnantClass_eq := fun o => (B.remnantClassData o).classEq

/-- **R-6c-heart-6a-5b — into the right-`eq` chain.**  A family of `ClassData` supplies (one per split
choice) builds the `ResolvedContractTwiceOnceSupply`, whose `.right_eq` is `right_eq`. -/
def ResolvedContractTwiceClassDataSupply.toRightEqSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ∀ s, ResolvedContractTwiceClassDataSupply D G imageOf s) :
    ResolvedContractTwiceOnceSupply D G imageOf where
  contract_class_eq := fun s => contract_class_eq_of_classData (B s).rightClassData

/-- **R-6c-heart-6a-5b — `right_eq` from the `ClassData` supply family.** -/
theorem ResolvedContractTwiceClassDataSupply.right_eq (R : ResolvedCoassocInnerRightSupply D G)
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ∀ s, ResolvedContractTwiceClassDataSupply D G imageOf s)
    (s : ResolvedCoassocSplitChoice D G) :
    (D.supply G).rightTerm s.1 = R.innerRightTerm (imageOf s) :=
  (ResolvedContractTwiceClassDataSupply.toRightEqSupply B).right_eq R s

/-- **R-6c-heart-6a-5b — `remnantGen` from the `ClassData` supply.** -/
theorem ResolvedContractTwiceClassDataSupply.remnantGen
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    {s : ResolvedCoassocSplitChoice D G}
    (B : ResolvedContractTwiceClassDataSupply D G imageOf s) (o : s.ForestChoiceOccurrence) :
    resolvedComponentGenTerm (B.remnantComponent o) = o.rightTermOf :=
  B.toRemnantDecontractionSupply.remnantGen o

end GaugeGeometry.QFT.Combinatorial
