import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSummandFactorBundle
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRightPrimitiveSurvivalTransport
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantTransport

/-!
# R-6c-body-128 — forward-map coherence: the concrete image supply defeq-aligns the assembler's ambient graph

Hundred-and-twenty-eighth genuine-body step, closing the coherence body-127's honesty note flagged: the
assembler consumes the survivor/remnant forests over `(selectedOuterOf q).1.contractWithStars …`, while the
body-125/126 transport supplies produce them over `q.selectedOuterContractGraph`.  The two are identified by the
selected-outer alignment `(selectedOuterOf q).1 = selectedOuterRawOf q` — and for the CONCRETE image supply
`resolvedConcreteSelectedOuterImageSupply` (heart-4 P5) this alignment is `rfl`, so the two ambient graphs are
DEFINITIONALLY EQUAL and the transport supplies slot into `ResolvedSummandFactorBundle` with NO cast.

## The coherence is `rfl` (PROVED)

`resolvedConcreteSelectedOuterImageSupply D G mem` is built from the concrete pieces
`resolvedConcreteLeftSelectionSupply` / `(resolvedPromotedOfSupply _).promotedOf` / `cross_disjoint_leftOf_promotedOf`,
so its `promoteSupply` is DEFINITIONALLY `resolvedConcreteForestPromoteSupply` (both reduce to
`resolvedConcreteLeftSelectionSupply.toPromoteSupply (resolvedPromotedOfSupply _).promotedOf cross_disjoint`, since
`ResolvedPromotedOfSupply.toForestPromoteSupply P L cross = L.toPromoteSupply P.promotedOf cross`).  Hence:

* `selectedOuter_eq` — `(imageSupply.selectedOuterOf q).1 = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q` (`rfl`);
* `quotientGraph_eq` — `(imageSupply.selectedOuterOf q).1.contractWithStars (starOf …) = q.selectedOuterContractGraph` (`rfl`),
  since `selectedOuterContractGraph` is exactly `(resolvedConcreteForestPromoteSupply _).selectedOuterRawOf q` contracted.

## The coercion (PROVED)

`ResolvedForwardMapCoherenceSupply D` fields only the single closure leaf `selectedOuter_mem` (the parametric-carrier
sub-forest-closure of heart-4 P5, genuinely not derivable).  `.toSummandBundle` then assembles a
`ResolvedSummandFactorBundle D` from a body-121 survival-transport supply and a body-126 remnant-transport supply
(their forests / factor products slot in by the `rfl` graph alignment) plus the remaining summand-agreement leaves
(the left-primitive / promoted factors, the two disjointnesses, the quotient forest with its union split, and
`quot_eq`).  So once the forward-map coherence is present, the survivor/remnant transports feed the summand bundle
directly — exactly what body-127's honesty note deferred.

Per the HALT: `imageSupply` is instantiated as the CONCRETE supply so `selectedOuter_eq` / `quotientGraph_eq` are
`rfl` (not fielded); only the parametric-carrier closure `selectedOuter_mem` is a field; no backward map / inverse
law is entered — the coercion is graph/forest transport only.

Landed:

* `ResolvedForwardMapCoherenceSupply D` — the closure leaf `selectedOuter_mem` + `.imageSupply`;
* `.selectedOuter_eq` / `.quotientGraph_eq` — the coherence, `rfl`;
* `.toSummandBundle` — the `ResolvedSummandFactorBundle` from the survivor/remnant transport supplies + the
  remaining leaves (the survivor/remnant forests slot in by defeq).

Toolkit body (like body-125/126/127), one closure supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-128 — the forward-map coherence supply.**  The single closure leaf `selectedOuter_mem` (the
parametric-carrier sub-forest-closure of heart-4 P5); its `imageSupply` is the concrete selected-outer image
supply, whose selected-outer alignment is `rfl`. -/
structure ResolvedForwardMapCoherenceSupply (D : ResolvedCoproductProperForestData) where
  /-- The carrier-membership closure of the concrete selected-outer forest (heart-4 P5). -/
  selectedOuter_mem : ∀ {G : ResolvedFeynmanGraph} (s : ResolvedCoassocSplitChoice D G),
    (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G

/-- **R-6c-body-128 — the concrete image supply from the coherence supply.** -/
noncomputable def ResolvedForwardMapCoherenceSupply.imageSupply
    (C : ResolvedForwardMapCoherenceSupply D) (G : ResolvedFeynmanGraph) :
    ResolvedCoassocSelectedOuterImageSupply D G :=
  resolvedConcreteSelectedOuterImageSupply D G C.selectedOuter_mem

/-- **R-6c-body-128 — the selected-outer coherence** (`rfl`).  The concrete image's selected-outer forest is the
promote body's `selectedOuterRawOf`. -/
theorem ResolvedForwardMapCoherenceSupply.selectedOuter_eq (C : ResolvedForwardMapCoherenceSupply D)
    (q : ResolvedCoassocSplitChoice D G) :
    ((C.imageSupply G).selectedOuterOf q).1
      = (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf q :=
  rfl

/-- **R-6c-body-128 — the quotient-graph coherence** (`rfl`).  The assembler's ambient contract graph is
`q.selectedOuterContractGraph`, so the body-125/126 forests live over the same graph. -/
theorem ResolvedForwardMapCoherenceSupply.quotientGraph_eq (C : ResolvedForwardMapCoherenceSupply D)
    (q : ResolvedCoassocSplitChoice D G) :
    ((C.imageSupply G).selectedOuterOf q).1.contractWithStars
        (D.starOf G ((C.imageSupply G).selectedOuterOf q).1)
      = q.selectedOuterContractGraph :=
  rfl

/-- **R-6c-body-128 — the summand bundle from the forward-map coherence + the transport supplies.**  Assembles a
`ResolvedSummandFactorBundle` from a body-121 survival-transport supply and a body-126 remnant-transport supply
(whose forests / factor products slot in by the `rfl` graph alignment) plus the remaining summand-agreement leaves.
This realises body-127's deferred coercion: the survivor/remnant transports feed the summand bundle directly. -/
noncomputable def ResolvedForwardMapCoherenceSupply.toSummandBundle
    (C : ResolvedForwardMapCoherenceSupply D)
    (Sv : ResolvedRightPrimitiveSurvivalTransportSupply D)
    (Rm : ResolvedRemnantTransportSupply D)
    (quotientForest : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (D.supply (((C.imageSupply G).selectedOuterOf q).1.contractWithStars
        (D.starOf G ((C.imageSupply G).selectedOuterOf q).1))).ForestIdx)
    (hcross : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      ∀ γ ∈ (Sv.rightSurvivor q).elements, ∀ δ ∈ (Rm.remnant.remnantForest q).elements,
        γ ≠ δ → γ.Disjoint δ)
    (union_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (quotientForest q).1 = (Sv.rightSurvivor q).union (Rm.remnant.remnantForest q) (hcross q))
    (hRdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      Disjoint (Sv.rightSurvivor q).elements (Rm.remnant.remnantForest q).elements)
    (left_primitive_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm ((C.imageSupply G).leftSelection.leftOf q))
    (promoted_factor : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
          localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
        = resolvedForestLeftTerm ((C.imageSupply G).promotedOf q))
    (hLdisj : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      Disjoint ((C.imageSupply G).leftSelection.leftOf q).elements ((C.imageSupply G).promotedOf q).elements)
    (quot_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
      (D.supply G).rightTerm q.1
        = (D.supply (((C.imageSupply G).selectedOuterOf q).1.contractWithStars
            (D.starOf G ((C.imageSupply G).selectedOuterOf q).1))).rightTerm (quotientForest q)) :
    ResolvedSummandFactorBundle D where
  selected {G} := C.imageSupply G
  quotientForest {G} q := quotientForest q
  rightSurvivor {G} q := Sv.rightSurvivor q
  remnant {G} q := Rm.remnant.remnantForest q
  hcross {G} q := hcross q
  union_eq {G} q := union_eq q
  hRdisj {G} q := hRdisj q
  left_primitive_factor {G} q := left_primitive_factor q
  promoted_factor {G} q := promoted_factor q
  hLdisj {G} q := hLdisj q
  right_primitive_factor {G} q := Sv.right_primitive_factor q
  remnant_factor {G} q := Rm.remnant_factor q
  quot_eq {G} q := quot_eq q

end GaugeGeometry.QFT.Combinatorial
