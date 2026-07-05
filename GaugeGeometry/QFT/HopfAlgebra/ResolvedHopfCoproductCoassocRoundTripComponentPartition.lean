import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteRoundTripObligations

/-!
# R-6c-body-160 — round-trip component partition: the outer round-trips as element equalities

Hundred-and-sixtieth genuine-body step, reducing body-154's two OUTER round-trips to component-set (element)
equalities.  The forward / backward outer round-trips are `{A // A ∈ carrier}` equalities; by `Subtype.ext` +
`ResolvedAdmissibleSubgraph.ext_elements` they reduce to plain `Finset` equalities of the underlying components.
The two quotient / choice round-trips are heterogeneous (their types depend on the outer) and are kept as fielded
`HEq` facts.

## The reduction (PROVED)

`ResolvedRoundTripComponentPartitionSupply D S Region` fields:

* `selectedOuter_partition` — `(selectedOuterOf ⟨unionOuter z, recoverChoice z⟩).1.elements = z.1.1.elements`
  (**A-reconstruction at the element level**: the recovered selected outer has exactly `A`'s components);
* `recoveredOuter_partition` — `(unionOuter (fwdMap q)).1.elements = q.1.1.elements` (**A'-recovery at the element
  level**: the reconstruction of a forward image has exactly the original outer's components);
* `forward_quotient` / `backward_choice` — the two heterogeneous round-trips (B-reconstruction / p-recovery), kept
  as `HEq` (their `Finset.ext` / componentwise reduction needs the sector `componentToRight` / `componentToForest`
  round-trips, deferred).

Then `forward_outer` / `backward_outer` are **proved** by `Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements …)`,
and `.toConcreteRoundTripObligationSupply` produces body-154's four obligations — hence, through body-154 → 147 →
… → 131, the whole bijection.

So the two outer round-trips are no longer opaque type equalities: they are exactly the two element partition facts
`selectedOuterOf(recovered) = A` and `recoverOuter(forward) = A'` at the `Finset`-of-components level, ready for the
region-partition proof (`A = leftResidual ∪ represented`).

Per the HALT: the partition facts are fielded; the outer round-trips are reduced to element equalities (via
`ext_elements`); the quotient / choice round-trips are kept as `HEq` (their sector round-trip is not entered).

Landed:

* `ResolvedRoundTripComponentPartitionSupply D S Region` — the two element partitions + the two `HEq` round-trips;
* `.toConcreteRoundTripObligationSupply` — body-154's obligations (outer ones PROVED from the partitions).

Toolkit body (like body-154).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-160 — the round-trip component-partition supply.**  The two OUTER round-trips as `Finset`
element partitions (`selectedOuter_partition`, `recoveredOuter_partition`), plus the two heterogeneous quotient /
choice round-trips. -/
structure ResolvedRoundTripComponentPartitionSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- A-reconstruction (element level): the recovered selected outer has exactly `A`'s components. -/
  selectedOuter_partition : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    ((S.Forward.imageSupply G).selectedOuterOf
        (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)).1.elements
      = z.1.1.elements
  /-- B-reconstruction (heterogeneous): the recovered quotient forest is `B`. -/
  forward_quotient : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G),
    HEq (S.quotientForest
      (⟨Region.Union.unionOuter z, Region.recoverChoice z⟩ : ResolvedCoassocSplitChoice D G)) z.2
  /-- A'-recovery (element level): the reconstruction of a forward image has exactly the original outer's
  components. -/
  recoveredOuter_partition : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements
  /-- p-recovery (heterogeneous): the reconstruction's choice of a forward image is the original choice. -/
  backward_choice : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    HEq (Region.recoverChoice (fwdMap S q)) q.2

/-- **R-6c-body-160 — body-154's round-trip obligations from the component partitions.**  The two outer round-trips
are proved from the element partitions by `Subtype.ext` + `ResolvedAdmissibleSubgraph.ext_elements`. -/
def ResolvedRoundTripComponentPartitionSupply.toConcreteRoundTripObligationSupply
    {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}
    (P : ResolvedRoundTripComponentPartitionSupply D S Region) :
    ResolvedConcreteRoundTripObligationSupply D S Region where
  forward_outer := fun {G} z =>
    Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements (P.selectedOuter_partition z))
  forward_quotient := fun {G} z => P.forward_quotient z
  backward_outer := fun {G} q =>
    Subtype.ext (ResolvedAdmissibleSubgraph.ext_elements (P.recoveredOuter_partition q))
  backward_choice := fun {G} q => P.backward_choice q

end GaugeGeometry.QFT.Combinatorial
