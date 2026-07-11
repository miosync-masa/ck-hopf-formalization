import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRecoveredRegionMembershipAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocCarrierProperProvider
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocIsNonemptyTransfer

/-!
# R-6c-body-241 — recovered-outer nonemptiness on the forward image: `unionOuter (fwdMap S q)` is nonempty (PROVED)

Two-hundred-and-forty-first genuine-body step — the first `IsNonempty` conjunct discharged for a constructed forest,
`Y` (the recovered-outer region union) on the forward image `fwdMap S q`.  Body-239 found `Y` viable via the body-173
covering; body-240 gave the transfer infra.  This body proves it, using **only the domain outer's carrier
membership/properness** — never the recovered carrier membership.

## The proof (membership-independent)

`(Region.Union.unionOuter (fwdMap S q)).1.IsNonempty` from:

* `q.1.2 : q.1.1 ∈ D.carrier G` — the **domain** outer's carrier membership (free, the sigma subtype proof of
  `ForestBlockDomType`), NOT the recovered one;
* `P.carrier_isProperForest` → `.1` → `q.1.1.IsNonempty` (`isNonempty_of_isProperForest`);
* `recovered_region_partition` (body-168, from the assembly bundle's three sector bridges) — the Finset equality
  `leftResidual ∪ rightRecovered ∪ forestRecovered = q.1.1.elements`;
* `Region.Union.union_eq` — the pure `elements` equation
  `(unionOuter z).1.elements = leftResidual z .elements ∪ rightRecovered z .elements ∪ forestRecovered z .elements`.

Composing the last two gives `(unionOuter (fwdMap S q)).1.elements = q.1.1.elements`, so nonemptiness transfers.

## Audit — circularity and dependency (per the body-239 warning)

* **The proof never touches `recovered_outer_mem` (body-159).**  It uses `q.1.2` (the *domain* membership),
  `carrier_isProperForest` on the domain outer, `union_eq` (a pure elements equation), and the region partition
  (bridges + trichotomy).  In particular `(unionOuter …).2` — the *recovered* carrier membership, whose use would be
  circular for the certificate discharge — is **never referenced**.  So `Y.IsNonempty` is a **genuine,
  membership-independent discharge**, taking the `Region` supply as a hypothesis.
* **Dependency recorded**: the theorem is conditional on `Region : ResolvedRegionChoiceRoundTripSupply D S` existing,
  and *constructing* that supply is not membership-free — `Region.Union.unionOuter` has codomain
  `{A' // A' ∈ D.carrier G}`, whose `.2` is exactly `recovered_outer_mem` (body-159).  That membership is required to
  *build* `Region.Union`, but is **not required and not used** to prove `.1.IsNonempty`.  A later body that assembles
  the actual certificate must separate the raw (membership-free) region union from the carrier-tagged `unionOuter` if
  it is to avoid presupposing the very membership it discharges.

Per the HALT: only `Y`'s `IsNonempty` on the forward image is proved — no other conjunct, no certificate, no
`unionOuter.2` / `cert_mem`, no `X` (`selectedOuterRawOf`, which is genuinely empty on the all-right split, body-239).
No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {S : ResolvedConcreteSummandBundleSupply D}
  {Region : ResolvedRegionChoiceRoundTripSupply D S}

set_option linter.unusedSectionVars false

/-- **R-6c-body-241 — the recovered outer is nonempty on the forward image.**  `(unionOuter (fwdMap S q)).1` is
nonempty because its elements equal the domain outer `q.1.1.elements` (body-168 partition + `union_eq`), and the
domain outer is a nonempty carrier member (`q.1.2` + `carrier_isProperForest`).  Membership-independent: the recovered
carrier membership `(unionOuter …).2` is never used. -/
theorem recoveredOuter_isNonempty (P : ResolvedCarrierProperProvider D)
    (A : ResolvedRecoveredRegionMembershipAssemblySupply D S Region)
    (q : ForestBlockDomType D G) :
    (Region.Union.unionOuter (fwdMap S q)).1.IsNonempty := by
  have h1 : q.1.1.IsNonempty := (P.carrier_isProperForest G q.1.1 q.1.2).1
  have hunion : (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements := by
    rw [Region.Union.union_eq (fwdMap S q),
      A.toRecoveredOuterRegionPartitionSupply.recovered_region_partition q]
  show (Region.Union.unionOuter (fwdMap S q)).1.elements.Nonempty
  rw [hunion]
  exact h1

end GaugeGeometry.QFT.Combinatorial
