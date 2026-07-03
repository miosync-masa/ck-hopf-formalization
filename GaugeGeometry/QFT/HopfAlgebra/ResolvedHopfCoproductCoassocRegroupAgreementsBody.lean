import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSupport9Body
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSide
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBranchSide

/-!
# R-6c-body-37 — regroup agreements scout: NOT rfl; factored through the representative

Thirty-seventh genuine-body step, a SCOUT of body-36's two regroup agreements (`image_agreement` /
`branch_agreement`) — the last top-level obligation before `coassoc_gen`.

## Finding: the agreements are GENUINE reindex leaves, not `rfl`

`regroupImageSum x = 1 ⊗ forestSum x.1 + coassocRightTail (forestSum x.1)` and `regroupBranchSum x =
assoc(forestSum x.1 ⊗ 1) + coassocLeftTail (forestSum x.1)` (`ResolvedHopfCoproductCoassocRegroup`).  The
agreements compare these `forestSum`-based sums to the *splitPhi-cover* sums `∑ imageCarrier imageWeight` /
`∑ (forest+mixed)Carrier splitTerm` — i.e. the resolved H5.8 reindex over the cover.  That is NOT `rfl`; it is
the resolved counterpart of the landed R-4-full `h58_resolved_carrier_double_sum_reindex`.

## What IS proved: the representative-level linearity descent

At a representative `G.toResolvedHopfGen hCD`, the regroup sums descend by pure linearity to a sum over the
outer forest carrier — already theorems:

* `regroupImageSum_eq_outerSum` : `regroupImageSum (G.toResolvedHopfGen hCD) = ∑ A ∈ (D.supply G).forestCarrier, …`;
* `regroupBranchSum_eq_outerSum` : likewise for the branch side.

So the agreements factor into two pieces: (a) the **representative choice** `x = repGraph x .toResolvedHopfGen
(repCD x)` — a single `Quot` equation on generators; and (b) the agreements **in representative coordinates**
— which, via the two `…_eq_outerSum` theorems, reduce further to the outer-forest-carrier sum = finite-cover
sum reindex (the genuine H5.8 cover content, the same shape already discharged at flat/full-grain level in
R-4-full).  This is NOT the deep `Quot.sound` representative-equivalence territory: the representative choice is
one equation, and the remaining reindex is finite-cover combinatorics.

This file factors body-36's agreements through the representative choice (via `congrArg D.regroupImageSum`),
putting them in the coordinates where the proved `…_eq_outerSum` machinery lives.  Per the HALT, the
representative equation and the representative-coordinate agreements are NAMED, not proved (no `Quot.sound`
proof-term comparison).

Landed:

* `ResolvedRegroupAgreementSupply D` — `repGraph` + `repCD` + `rep_eq` (the representative choice) + `grand` +
  the two agreements in representative coordinates;
* `.toRepresentativeFamilySupply` — body-36's record, via `congrArg`;
* `.coassoc_gen` — the capstone.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-37 — the regroup-agreement supply.**  The representative choice (`repGraph` + `rep_eq`), the
per-representative grand building block, and the two regroup agreements STATED IN REPRESENTATIVE COORDINATES
(where the proved `regroupImageSum_eq_outerSum` / `regroupBranchSum_eq_outerSum` descents live). -/
structure ResolvedRegroupAgreementSupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator (the representative choice). -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- Image agreement in representative coordinates (`regroupImageSum` at the representative = cover image sum). -/
  image_agreement_at_rep : ∀ x : ResolvedHopfGen,
    D.regroupImageSum ((repGraph x).toResolvedHopfGen (repCD x)) =
      ∑ z ∈ (grand x).toFiniteData.imageCarrier, (grand x).toFiniteData.imageWeight z
  /-- Branch agreement in representative coordinates (cover term sum = `regroupBranchSum` at the representative). -/
  branch_agreement_at_rep : ∀ x : ResolvedHopfGen,
    (∑ q ∈ (grand x).toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ (grand x).toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = D.regroupBranchSum ((repGraph x).toResolvedHopfGen (repCD x))

/-- **R-6c-body-37 — body-36's representative family from the regroup-agreement supply.**  The representative
choice `rep_eq` transports the two agreements from representative coordinates back to the generator `x` (via
`congrArg` on `regroupImageSum` / `regroupBranchSum`). -/
noncomputable def ResolvedRegroupAgreementSupply.toRepresentativeFamilySupply
    (F : ResolvedRegroupAgreementSupply D) :
    ResolvedCoassocRepresentativeFamilySupply D where
  repGraph := F.repGraph
  grand := F.grand
  image_agreement := fun x =>
    (congrArg D.regroupImageSum (F.rep_eq x)).trans (F.image_agreement_at_rep x)
  branch_agreement := fun x =>
    (F.branch_agreement_at_rep x).trans (congrArg D.regroupBranchSum (F.rep_eq x).symm)

/-- **R-6c-body-37 — the capstone from the regroup-agreement supply. -/
theorem ResolvedRegroupAgreementSupply.coassoc_gen
    (F : ResolvedRegroupAgreementSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  F.toRepresentativeFamilySupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
