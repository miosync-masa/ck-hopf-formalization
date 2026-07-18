import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandValue
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightSurvivorTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocFreeClusterBank
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantComponentValueWiring

/-!
# R-6c-body-396 — the faithful Forward-free concrete `V` construction root (PROVED)

Three-hundred-and-ninety-sixth genuine-body step — the faithful direct `ResolvedConcreteSummandValueSupply`, the genuine
first root of body-395's residual.  The ONLY existing constructor was `ofLegacy`, whose legacy `Forward` is unfaithful;
this builds `V` Forward-free from the measure leaf (single owner) and the concrete remnant, so that body-384's `Wiring`
and body-369's `hSurvivorComponent` both become `rfl`, and the independent `Measure` collapses into `V.Measure`.

* `remnantComponentSupplyOfConcrete` — the abstract remnant supply built pointwise from the concrete remnant + its
  family disjointness (the impedance match `ResolvedConcreteRemnantReembedSupply` ⟶ `ResolvedRemnantComponentSupply`);
* `ResolvedConcreteSummandValueConstructionSupply D Concrete` — the honest raw-quotient ownership root: `Measure`,
  `remnantDisjoint`, the transport injectivity/gen leaves, `hcross` / `quotient_mem` / `hRdisj` / `quot_eq`;
* `.toConcreteSummandValueSupply` — `Survivor := survivorSupply_of_measure Measure`, `Remnant :=` the concrete remnant,
  `quotientForestRaw := ⟨survivor ∪ remnant, quotient_mem⟩` (`union_eq := rfl`), Forward-free;
* `hSurvivorComponent_of_construction` (`rfl`) and `remnantComponentValueWiring_of_construction` (`remnantComponent_eq
  := rfl`) — the two V-wirings, now `rfl` off the single owner.

The old `FullQuotient`'s `∀ s, selectedOuterRawOf s ∈ carrier` (the retired total selected-outer closure) is NOT used;
`ForestIdx = {A // A ∈ D.carrier _}` (`ResolvedHopfCoproductSupply.lean:151`), so the quotient is `⟨_, quotient_mem⟩`.

Per the HALT: `quotient_mem` / `quot_eq` / `survivorInj` / `remnantInj` / `remnantGen` / the cross-disjointness are NOT
proved — they are the honest raw-quotient ownership fields; the win is the Forward-free direct `V` constructor + `Measure`
single-owner + the two `rfl` V-wirings.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse`
/ singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence] [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-396 — the abstract remnant supply from the concrete remnant.**  `remnantComponent` / `remnantCD` are the
concrete re-embedding's; `remnantDisjoint` is the supplied family disjointness. -/
noncomputable def remnantComponentSupplyOfConcrete
    (Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ResolvedConcreteRemnantReembedSupply D G s)
    (remnantDisjoint : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ∀ ⦃δ⦄, δ ∈ s.forestComponents.attach.image
          (fun γ => (Concrete s).remnantComponent (s.forestComponentOccurrence γ)) →
      ∀ ⦃δ'⦄, δ' ∈ s.forestComponents.attach.image
          (fun γ => (Concrete s).remnantComponent (s.forestComponentOccurrence γ)) →
      δ ≠ δ' → δ.Disjoint δ')
    {G : ResolvedFeynmanGraph} : ResolvedRemnantComponentSupply D G where
  remnantComponent := fun s o => (Concrete s).remnantComponent o
  remnantCD := fun s o => (Concrete s).remnantCD o
  remnantDisjoint := fun s => remnantDisjoint s

/-- **R-6c-body-396 — the faithful Forward-free raw-quotient ownership root.** -/
structure ResolvedConcreteSummandValueConstructionSupply (D : ResolvedCoproductProperForestData)
    (Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
      ResolvedConcreteRemnantReembedSupply D G s) where
  /-- The measure leaves — the SINGLE owner (projected as `V.Measure`). -/
  Measure : ResolvedMeasureLeafSupply D
  /-- The concrete remnant family is pairwise disjoint in the quotient graph. -/
  remnantDisjoint : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ∀ ⦃δ⦄, δ ∈ s.forestComponents.attach.image
        (fun γ => (Concrete s).remnantComponent (s.forestComponentOccurrence γ)) →
    ∀ ⦃δ'⦄, δ' ∈ s.forestComponents.attach.image
        (fun γ => (Concrete s).remnantComponent (s.forestComponentOccurrence γ)) →
    δ ≠ δ' → δ.Disjoint δ'
  /-- Survivor `Finset` injectivity (over the measure survivor). -/
  survivorInj : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ q.rightComponents.attach, ∀ γ₂ ∈ q.rightComponents.attach,
      (survivorSupply_of_measure Measure G).survivorComponent q γ₁
        = (survivorSupply_of_measure Measure G).survivorComponent q γ₂ → γ₁ = γ₂
  /-- Survivor reembed generator equality (over the measure survivor). -/
  survivorGen : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ : {x : _ // x ∈ q.rightComponents},
      resolvedComponentGenTerm ((survivorSupply_of_measure Measure G).survivorComponent q γ)
        = resolvedComponentGenTerm γ.1.1
  /-- Remnant occurrence-injectivity (over the concrete remnant). -/
  remnantInj : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ q.forestComponents.attach, ∀ γ₂ ∈ q.forestComponents.attach,
      (Concrete q).remnantComponent (q.forestComponentOccurrence γ₁)
        = (Concrete q).remnantComponent (q.forestComponentOccurrence γ₂) → γ₁ = γ₂
  /-- Remnant de-contraction generator equality. -/
  remnantGen : ∀ {G : ResolvedFeynmanGraph} (q : ResolvedCoassocSplitChoice D G),
    ∀ γ : {x : _ // x ∈ q.forestComponents},
      resolvedComponentGenTerm ((Concrete q).remnantComponent (q.forestComponentOccurrence γ))
        = D.rightFactorOf q γ.1
  /-- Survivor/remnant cross-disjointness. -/
  hcross : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ∀ γ ∈ ((survivorSupply_of_measure Measure G).rightSurvivorForest q).elements,
    ∀ δ ∈ ((remnantComponentSupplyOfConcrete Concrete remnantDisjoint).remnantForest q).elements,
      γ ≠ δ → γ.Disjoint δ
  /-- The quotient forest (survivor ∪ remnant) lies in the carrier of the quotient graph. -/
  quotient_mem : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    ((survivorSupply_of_measure Measure G).rightSurvivorForest q).union
      ((remnantComponentSupplyOfConcrete Concrete remnantDisjoint).remnantForest q) (hcross q)
      ∈ D.carrier (ResolvedCoassocSplitChoice.selectedOuterContractGraph q)
  /-- Survivor and remnant forests are disjoint. -/
  hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Disjoint ((survivorSupply_of_measure Measure G).rightSurvivorForest q).elements
      ((remnantComponentSupplyOfConcrete Concrete remnantDisjoint).remnantForest q).elements
  /-- The right-term agreement. -/
  quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (D.supply G).rightTerm q.1
      = (D.supply (ResolvedCoassocSplitChoice.selectedOuterContractGraph q)).rightTerm
          ⟨((survivorSupply_of_measure Measure G).rightSurvivorForest q).union
            ((remnantComponentSupplyOfConcrete Concrete remnantDisjoint).remnantForest q) (hcross q),
           quotient_mem q⟩

namespace ResolvedConcreteSummandValueConstructionSupply

variable {Concrete : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    ResolvedConcreteRemnantReembedSupply D G s}

/-- **R-6c-body-396 — the faithful Forward-free concrete value supply.** -/
noncomputable def toConcreteSummandValueSupply
    (C : ResolvedConcreteSummandValueConstructionSupply D Concrete) :
    ResolvedConcreteSummandValueSupply D where
  Measure := C.Measure
  Survivor :=
    { survivor := fun {G} => survivorSupply_of_measure C.Measure G
      survivorInj := C.survivorInj
      survivorGen := C.survivorGen }
  Remnant :=
    { remnant := fun {_G} => remnantComponentSupplyOfConcrete Concrete C.remnantDisjoint
      remnantInj := C.remnantInj
      remnantGen := C.remnantGen }
  quotientForestRaw := fun {G} q =>
    ⟨((survivorSupply_of_measure C.Measure G).rightSurvivorForest q).union
      ((remnantComponentSupplyOfConcrete Concrete C.remnantDisjoint).remnantForest q) (C.hcross q),
     C.quotient_mem q⟩
  hcross := C.hcross
  union_eq := fun {_G} _q => rfl
  hRdisj := C.hRdisj
  quot_eq := C.quot_eq

/-- **R-6c-body-396 — the survivor-component wiring is `rfl`** (single owner). -/
theorem hSurvivorComponent_of_construction
    (C : ResolvedConcreteSummandValueConstructionSupply D Concrete)
    {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G)
    (γ : {y : {x : ResolvedFeynmanSubgraph G // x ∈ s.1.1.elements} //
      y ∈ ResolvedCoassocSplitChoice.rightComponents s}) :
    C.toConcreteSummandValueSupply.Survivor.survivor.survivorComponent s γ
      = (survivorSupply_of_measure C.Measure G).survivorComponent s γ :=
  rfl

/-- **R-6c-body-396 — the remnant-component value wiring is `rfl`** (body-384's gate discharged). -/
def remnantComponentValueWiring_of_construction
    (C : ResolvedConcreteSummandValueConstructionSupply D Concrete) :
    ResolvedRemnantComponentValueWiringSupply C.toConcreteSummandValueSupply Concrete where
  remnantComponent_eq := fun _s _o => rfl

end ResolvedConcreteSummandValueConstructionSupply

end GaugeGeometry.QFT.Combinatorial
