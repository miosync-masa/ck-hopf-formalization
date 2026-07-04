import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotEqFromRightGeometry
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocLocalLeftFactorProduct
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForestTermFactors
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocContractTwice

/-!
# R-6c-body-113 — outer-mixing map assembly: all existing pieces wired into one supply → coassoc_gen

Hundred-and-thirteenth genuine-body step, the ASSEMBLY: every forest-block map field is now identified with
existing machinery (forward = `selectedOuterOf`/`quotientForestOf`, `quot_eq` = contract-twice geometry,
`invConstruct` = sector backward, factor identities = `resolvedForestLeftTerm_union`), so this body wires them
into a SINGLE high-level supply that flows to `coassoc_gen`.  The six geometric `*_eq` / `*_quot_eq` fields of
body-106's map data are DERIVED here from the clean leaves (factor products, union/disjoint, contract geometry)
via the body-107–111 toolkit; everything else passes through.

## The derivation

`ResolvedOuterMixingAssemblySupply` bundles the forward data (`imageSupply` / `quotientRaw` / `quotient_mem` /
`invConstruct`), the membership / inverse-law fields, and the clean leaves.  Its
`.toOuterMixingMapFromQuotientData` fills body-106's fields:

* `mixed_left_eq` / `forest_left_eq` := `resolved_selectedOuter_left_factor_eq_of_parts` (body-108) from
  `left_primitive_factor` + `promoted_factor` + `left_hdisj`;
* `mixed_right_eq` / `forest_right_eq` := `resolved_quotientForest_right_factor_eq_of_parts` (body-109) from the
  quotient union `rightSurvivor ∪ remnant` (`right_union_eq` / `right_hcross` / `right_hdisj`) +
  `right_primitive_factor` + `remnant_factor`;
* `mixed_quot_eq` / `forest_quot_eq` := `resolved_quot_eq_from_contract_geometry` (body-111) from the existing
  `ResolvedContractTwiceOnceGeometrySupply` (`contract`).

`.coassoc_gen` then chains body-106/105/104/102/101/98/…/88.

## The remaining leaf inventory (the WHOLE raid boss, in one place)

After this assembly, `coassoc_gen` follows from `ResolvedOuterMixingAssemblySupply`, whose fields are EXACTLY:

* forward: `imageSupply`, `quotientRaw`, `quotient_mem`;
* backward: `invConstruct` + the four inverse-law / two membership fields (mixed/forest) — the sector backward
  maps and their round-trips;
* LEFT factor: `left_primitive_factor`, `promoted_factor`, `left_hdisj`;
* RIGHT factor: `rightSurvivor`, `remnant`, `right_hcross`, `right_union_eq`, `right_hdisj`,
  `right_primitive_factor`, `remnant_factor`;
* geometry: `contract` (the bodies-27–49 `ResolvedContractTwiceOnceGeometrySupply`);
* `carrier_isProperForest` + representative lift.

Every one of these is a σ-cover / retarget / sector leaf already scoped in earlier bodies; none is new coassoc
content.  So `coassoc_gen` now flows from a single, fully-inventoried supply tree.

Per the HALT: this pass is dependency WIRING only — the leaves (selection factors, union/disjoint, inverse laws,
contract geometry, quotient membership, carrier properness) are NOT proved; the record is flattened (like
body-101) to avoid cyclic dependencies.

Landed:

* `ResolvedOuterMixingAssemblySupply D` — the single assembly supply (forward + backward + factor + geometry
  leaves);
* `.toOuterMixingMapFromQuotientData` / `.coassoc_gen` — to body-106/105/104/…/88.

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

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **R-6c-body-113 — the outer-mixing assembly supply.**  All existing map pieces (forward selected-outer /
quotient, backward inverse, LEFT / RIGHT factor leaves, contract-twice geometry) in one flattened record, from
which body-106's map data — and hence `coassoc_gen` — is derived. -/
structure ResolvedOuterMixingAssemblySupply (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply (forward `A_target`, body-105). -/
  imageSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G
  /-- The raw quotient forest `B` (forward, body-106). -/
  quotientRaw : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  /-- The quotient forest lies in the quotient carrier. -/
  quotient_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    quotientRaw G q ∈ D.carrier (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  /-- The backward map (body-112). -/
  invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G
  -- membership / inverse laws (sector backward)
  mixed_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G)
      ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  mixed_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ mixedDomFinset G
  mixed_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G),
    invConstruct G
        (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G) = q
  mixed_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        ⟨quotientRaw G (invConstruct G r), quotient_mem G (invConstruct G r)⟩⟩ : ForestBlockCodType D G) = r
  forest_toFun_mem : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G)
      ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G
  forest_invFun_mem : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    invConstruct G r ∈ forestCarryingDomFinset G
  forest_left_inv : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G)
    (hq : q ∈ forestCarryingDomFinset G),
    invConstruct G
        (⟨(imageSupply G).selectedOuterOf q, ⟨quotientRaw G q, quotient_mem G q⟩⟩ : ForestBlockCodType D G) = q
  forest_right_inv : ∀ (G : ResolvedFeynmanGraph) (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (⟨(imageSupply G).selectedOuterOf (invConstruct G r),
        ⟨quotientRaw G (invConstruct G r), quotient_mem G (invConstruct G r)⟩⟩ : ForestBlockCodType D G) = r
  -- LEFT factor leaves
  left_primitive_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((imageSupply G).leftSelection.leftOf q)
  promoted_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localLeftFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((imageSupply G).promotedOf q)
  left_hdisj : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    Disjoint ((imageSupply G).leftSelection.leftOf q).elements ((imageSupply G).promotedOf q).elements
  -- RIGHT factor leaves
  rightSurvivor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  remnant : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  right_hcross : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ∀ γ ∈ (rightSurvivor G q).elements, ∀ δ ∈ (remnant G q).elements, γ ≠ δ → γ.Disjoint δ
  right_union_eq : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    quotientRaw G q = (rightSurvivor G q).union (remnant G q) (right_hcross G q)
  right_hdisj : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    Disjoint (rightSurvivor G q).elements (remnant G q).elements
  right_primitive_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (rightSurvivor G q)
  remnant_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm (remnant G q)
  -- contract-twice geometry (bodies 27-49)
  contract : ∀ (G : ResolvedFeynmanGraph),
    ResolvedContractTwiceOnceGeometrySupply D G
      (fun q => ⟨(imageSupply G).selectedOuterOf q, quotientRaw G q⟩)
  -- shared
  carrier_isProperForest : ∀ (G : ResolvedFeynmanGraph) (A : ResolvedAdmissibleSubgraph G),
    A ∈ D.carrier G → A.IsProperForest
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-113 — body-106's map data from the assembly.**  Derive the six geometric identities from the
factor / union / contract leaves; pass the rest through. -/
def ResolvedOuterMixingAssemblySupply.toOuterMixingMapFromQuotientData
    (S : ResolvedOuterMixingAssemblySupply D) : ResolvedOuterMixingMapFromQuotientData D where
  imageSupply := S.imageSupply
  quotientRaw := S.quotientRaw
  quotient_mem := S.quotient_mem
  invConstruct := S.invConstruct
  mixed_toFun_mem := S.mixed_toFun_mem
  mixed_invFun_mem := S.mixed_invFun_mem
  mixed_left_inv := S.mixed_left_inv
  mixed_right_inv := S.mixed_right_inv
  mixed_left_eq := fun G q hq =>
    resolved_selectedOuter_left_factor_eq_of_parts (S.imageSupply G) q
      (S.left_primitive_factor G q) (S.promoted_factor G q) (S.left_hdisj G q)
  mixed_right_eq := fun G q hq =>
    resolved_quotientForest_right_factor_eq_of_parts q _ ⟨S.quotientRaw G q, S.quotient_mem G q⟩
      (S.rightSurvivor G q) (S.remnant G q) (S.right_hcross G q) (S.right_union_eq G q) (S.right_hdisj G q)
      (S.right_primitive_factor G q) (S.remnant_factor G q)
  mixed_quot_eq := fun G q hq =>
    resolved_quot_eq_from_contract_geometry (S.imageSupply G) (S.quotientRaw G) (S.quotient_mem G)
      (S.contract G) q
  forest_toFun_mem := S.forest_toFun_mem
  forest_invFun_mem := S.forest_invFun_mem
  forest_left_inv := S.forest_left_inv
  forest_right_inv := S.forest_right_inv
  forest_left_eq := fun G q hq =>
    resolved_selectedOuter_left_factor_eq_of_parts (S.imageSupply G) q
      (S.left_primitive_factor G q) (S.promoted_factor G q) (S.left_hdisj G q)
  forest_right_eq := fun G q hq =>
    resolved_quotientForest_right_factor_eq_of_parts q _ ⟨S.quotientRaw G q, S.quotient_mem G q⟩
      (S.rightSurvivor G q) (S.remnant G q) (S.right_hcross G q) (S.right_union_eq G q) (S.right_hdisj G q)
      (S.right_primitive_factor G q) (S.remnant_factor G q)
  forest_quot_eq := fun G q hq =>
    resolved_quot_eq_from_contract_geometry (S.imageSupply G) (S.quotientRaw G) (S.quotient_mem G)
      (S.contract G) q
  carrier_isProperForest := S.carrier_isProperForest
  rep := S.rep
  repCD := S.repCD
  rep_gen := S.rep_gen

/-- **R-6c-body-113 — `coassoc_gen` from the assembly** (via body-106/105/…/88). -/
theorem ResolvedOuterMixingAssemblySupply.coassoc_gen
    (S : ResolvedOuterMixingAssemblySupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toOuterMixingMapFromQuotientData.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
