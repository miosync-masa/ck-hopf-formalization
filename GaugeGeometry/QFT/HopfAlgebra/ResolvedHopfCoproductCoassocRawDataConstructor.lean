import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCorrectingPermContract
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightTermCorrectingPerm

/-!
# R-6c-body-412 — cycle-free `D` construction from the raw core (PROVED, ownership migration)

Four-hundred-and-twelfth genuine-body step — the ownership repair that breaks the definitional cycle.  Bodies 407–411
were migrated to the `rightTerm`-free raw core `R := ResolvedCoproductProperForestRawData` (they read only `starOf` /
`carrier`).  This body closes the loop: from the raw core `R` plus raw facts (freshness / injectivity / ambient support),
the correcting-permutation geometry yields the `rightTerm_mapPerm` law, and only THEN is the full
`ResolvedCoproductProperForestData` assembled — with NO reference to any pre-existing completed `D`.

* `resolvedForestRightTerm_eq_of_class_eq` — the `D`-free right-term identity from a contract-twice class equality (the
  raw counterpart of body-110's `resolved_rightTerm_eq_of_class_eq`);
* `ResolvedRightTermCorrectingPermRawSupply R` — the raw class-level socket (over `R.carrier` / `R.starOf`);
* `R.toDataOfCorrectingPerm` — the cycle-free constructor: raw core + raw socket → full `D` (rightTerm from `classEq`);
* `correctingPermRawSupplyOfFacts` — the raw socket from `AmbientRaw` + `StarRaw` (body-411's assembly, over `R`);
* `R.toDataOfFreshCorrecting` — the cycle-breaker: raw core + raw facts → full `D`.

Compatibility: the `D`-facing bodies 406/411 stay (they route through `D.toRaw` / `Fstar.toRaw` / `Ambient.toRaw`), so
no API regresses.

Per the HALT: `ResolvedCanonicalCarrierProperSupply` is NOT built; the supported-carrier emptying is NOT raw-ified; NO
canonical raw `W` inhabitant is claimed.  The deliverable is exactly "a full `D` is constructible from raw carrier/star
facts, cycle-free".  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse` / singleton /
floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {R : ResolvedCoproductProperForestRawData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-412 — the `D`-free right-term identity from a contract-twice class equality.**  If the two
star-contraction quotients have the same resolved class, their right terms agree — stated purely over `(A, starOf, hCD)`,
no `ResolvedCoproductProperForestData` needed.  The raw counterpart of body-110's `resolved_rightTerm_eq_of_class_eq`. -/
theorem resolvedForestRightTerm_eq_of_class_eq {G H : ResolvedFeynmanGraph}
    (A : ResolvedAdmissibleSubgraph G) (starOfA : ResolvedFeynmanSubgraph G → VertexId)
    (hCDA : (A.contractWithStars starOfA).forget.toClass.IsConnectedDivergent)
    (B : ResolvedAdmissibleSubgraph H) (starOfB : ResolvedFeynmanSubgraph H → VertexId)
    (hCDB : (B.contractWithStars starOfB).forget.toClass.IsConnectedDivergent)
    (class_eq : (A.contractWithStars starOfA).toResolvedClass
      = (B.contractWithStars starOfB).toResolvedClass) :
    resolvedForestRightTerm A starOfA hCDA = resolvedForestRightTerm B starOfB hCDB := by
  show MvPolynomial.X ((A.contractWithStars starOfA).toResolvedHopfGen hCDA)
    = MvPolynomial.X ((B.contractWithStars starOfB).toResolvedHopfGen hCDB)
  congr 1
  exact Subtype.ext class_eq

/-- **R-6c-body-412 — the raw correcting-permutation class socket.**  The body-406 socket, over the `rightTerm`-free raw
core `R`. -/
structure ResolvedRightTermCorrectingPermRawSupply (R : ResolvedCoproductProperForestRawData) where
  /-- The two-stage class datum: `τ` sends the relabeled forest's contraction to the original forest's contraction. -/
  classData : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId)
    (A : ResolvedAdmissibleSubgraph G) (_hA : A ∈ R.carrier G)
    (_hAσ : A.mapPerm σ ∈ R.carrier (G.mapPerm σ)),
    ResolvedContractTwiceClassData
      ((A.mapPerm σ).contractWithStars (R.starOf (G.mapPerm σ) (A.mapPerm σ)))
      (A.contractWithStars (R.starOf G A))

/-- **R-6c-body-412 — the cycle-free `D` constructor.**  Raw core + raw class socket → full
`ResolvedCoproductProperForestData`; the `rightTerm_mapPerm` field is read off the socket's `classEq` via the `D`-free
right-term identity.  NO completed `D` is referenced. -/
noncomputable def ResolvedCoproductProperForestRawData.toDataOfCorrectingPerm
    (Corr : ResolvedRightTermCorrectingPermRawSupply R) :
    ResolvedCoproductProperForestData where
  carrier := R.carrier
  starOf := R.starOf
  hCD := R.hCD
  carrier_mapPerm := R.carrier_mapPerm
  rightTerm_mapPerm := fun G σ A hA hAσ =>
    resolvedForestRightTerm_eq_of_class_eq A (R.starOf G A) (R.hCD G A hA)
      (A.mapPerm σ) (R.starOf (G.mapPerm σ) (A.mapPerm σ)) (R.hCD (G.mapPerm σ) (A.mapPerm σ) hAσ)
      (Corr.classData G σ A hA hAσ).classEq.symm

/-- **R-6c-body-412 — the raw class socket from fresh/ambient raw facts.**  Body-411's assembly, over the raw core. -/
noncomputable def correctingPermRawSupplyOfFacts
    (AmbientRaw : ResolvedCarrierAmbientSupportRawSupply R)
    (StarRaw : ResolvedCanonicalStarRawFacts R) :
    ResolvedRightTermCorrectingPermRawSupply R where
  classData := fun G σ A hA _hAσ =>
    have hgraph :
        (A.mapPerm σ).contractWithStars (R.starOf (G.mapPerm σ) (A.mapPerm σ))
          = (A.contractWithStars (R.starOf G A)).mapPerm (correctingPerm StarRaw σ A) :=
      correctingPerm_contractWithStars StarRaw σ A
        (AmbientRaw.edges_supported_of_mem hA) (AmbientRaw.legs_supported_of_mem hA)
    { starPerm := correctingPerm StarRaw σ A
      vertices_eq := congrArg (fun H : ResolvedFeynmanGraph => H.vertices) hgraph
      internalEdges_eq := congrArg (fun H : ResolvedFeynmanGraph => H.internalEdges) hgraph
      externalLegs_eq := congrArg (fun H : ResolvedFeynmanGraph => H.externalLegs) hgraph }

/-- **R-6c-body-412 ∎ — the cycle-breaker.**  A full `ResolvedCoproductProperForestData` from the raw core plus raw
freshness/injectivity/ambient-support facts — the honest ownership order (raw core → facts → geometry →
`rightTerm_mapPerm` → `D`), with no self-reference. -/
noncomputable def ResolvedCoproductProperForestRawData.toDataOfFreshCorrecting
    (AmbientRaw : ResolvedCarrierAmbientSupportRawSupply R)
    (StarRaw : ResolvedCanonicalStarRawFacts R) :
    ResolvedCoproductProperForestData :=
  R.toDataOfCorrectingPerm (correctingPermRawSupplyOfFacts AmbientRaw StarRaw)

end GaugeGeometry.QFT.Combinatorial
