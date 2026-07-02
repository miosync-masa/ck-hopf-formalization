import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocGrandFullSupply

/-!
# R-6c-leaf-38 — the final leaf inventory (the frozen proof boundary to `coassoc_gen`)

Thirty-third step — FREEZING the boundary.  Leaves 1–37 reduced every heart obligation to named
concrete-geometry supply fields flowing through the grand records.  `ResolvedCoassocGrandFullSupply` (leaf-12a)
is already the single per-`G` top record: `ImageTerm` (`Inner` + `selected` + `quotient` + `discriminatorOf` +
`Product` + `Right`) + the finite-cover fields, with `.toGlobalCoverSupply` / `.toGlobalCoverData` into
support-9.  This file wraps it as `ResolvedCoassocFinalLeafInventory` and records, in one place, the COMPLETE
list of remaining genuine bodies.

## The frozen leaf boundary (everything still to prove for `coassoc_gen`)

**Image side.**  `selectedOuter_eq` — ✅ PROVED `rfl` for the concrete image side (leaf-25); it discharges the
Product `hSel` (leaf-14) and the Sector `Align.quotientGraph_eq` (leaf-20) together.

**Product** (`ResolvedProductLeafBundle`, leaf-5): `survivorGen` ✅ / `remnantGen` ✅ (leaf-2); `survivorInj` ✅
(leaf-8); `remnantInj` ⟸ `occurrence_inj` (leaf-9); `hPD` / `hLP` / `hCross` / `hDisj` ✅ (leaf-10/12/13, modulo
`component_nonempty` + `vertex_cross`); `hSel` ✅ (leaf-25); `hQuot` ✅ (leaf-14/26, modulo the forest-term
transports).  Residual bodies: `occurrence_inj` (de-contraction uniqueness), `component_nonempty`,
`vertex_cross`, the remnant/survivor `right/remnant_transport`.

**Right** (`ResolvedRightLeafBundle`, leaf-6): `Mechanical` ✅ (leaf-1 ⟸ canonical star facts); `Codomain`
elements/disjoint ✅ (leaf-15 ⟸ star filter); `Edge` ✅ (leaf-16 ⟸ edge partition); `Transport` ⟸ {2 correct
containments + 2 vertex-partition facts} (leaf-17/34); `Sector` (`quotientStarEquiv`) fully reduced
(leaf-19..33): Forward {`Local` ⟸ nonempty+Remnant (leaf-27), `Align` ✅ (leaf-25), memberships ✅ ⟸ elements_eq
+ occurrence_match (leaf-29/30)}, Backward ⟸ forward surjectivity (leaf-31), Inverse ⟸ forward injectivity
(leaf-32/33); `Perm` ⟸ generic finite→global extension (leaf-22/35); `Retarget` ⟸ on-vertices `retarget_corr`
+ off-vertex bridge (leaf-21/36/37).  Residual bodies: `retarget_corr_on_vertices` (3-route action) + off-vertex
bridge; `FinsetSubtypePermExtensionSupply` (the `Equiv.Perm` construction); Transport 2 facts + 2 containments;
Sector `Remnant` / `component_nonempty` / `elements_eq×2` / `occurrence_match` / forward `surj×2` / forward
`inj×2`; Codomain forests.

**Inner** (`ResolvedCoassocInnerRightSupply`): `innerCD_forget` (leaf-18) — doubly-contracted CD.

**Finite cover / regroup / lift** (support-9): `forestCarrier` / `mixedCarrier` / `imageCarrier` + `cover_on`
+ `*_inj_on`; the two regroup agreements per `x`; the representative family for the `∀ x` lift into
`ResolvedCoassocFullCompatibilitySupply` → `coassoc_gen`.

Per the HALT, no body proofs; no refactor; the `∀ x` representative lift is NOT taken (per-`G` stop).

Landed:

* `ResolvedCoassocFinalLeafInventory D G` — wraps the `GrandFull` top record;
* `.toGrandFull` / `.toFiniteData` / `.toSplitPhiData` / `.toGlobalCoverSupply` / `.toGlobalCoverData`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-38 — the final leaf inventory.**  The single per-`G` record whose one field (`GrandFull`)
carries the entire frozen proof boundary to `coassoc_gen`. -/
structure ResolvedCoassocFinalLeafInventory (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The grand full supply (leaf-12a): image-term heart + finite-cover fields. -/
  GrandFull : ResolvedCoassocGrandFullSupply D G

/-- **R-6c-leaf-38 — the grand full supply. -/
def ResolvedCoassocFinalLeafInventory.toGrandFull
    (I : ResolvedCoassocFinalLeafInventory D G) : ResolvedCoassocGrandFullSupply D G :=
  I.GrandFull

/-- **R-6c-leaf-38 — the finite splitPhi cover. -/
noncomputable def ResolvedCoassocFinalLeafInventory.toFiniteData
    (I : ResolvedCoassocFinalLeafInventory D G) : ResolvedCoassocSplitPhiFiniteData D G :=
  I.GrandFull.toFiniteData

/-- **R-6c-leaf-38 — the resolved splitPhi data. -/
noncomputable def ResolvedCoassocFinalLeafInventory.toSplitPhiData
    (I : ResolvedCoassocFinalLeafInventory D G) : ResolvedCoassocSplitPhiData D G :=
  I.GrandFull.toSplitPhiData

/-- **R-6c-leaf-38 — the per-generator global cover supply (the support-9 building block). -/
noncomputable def ResolvedCoassocFinalLeafInventory.toGlobalCoverSupply
    (I : ResolvedCoassocFinalLeafInventory D G) (x : ResolvedHopfGen)
    (image_agreement : D.regroupImageSum x
      = ∑ z ∈ I.GrandFull.toFiniteData.imageCarrier, I.GrandFull.toFiniteData.imageWeight z)
    (branch_agreement :
      (∑ q ∈ I.GrandFull.toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ I.GrandFull.toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
        = D.regroupBranchSum x) :
    ResolvedCoassocGlobalCoverSupply D x :=
  I.GrandFull.toGlobalCoverSupply x image_agreement branch_agreement

/-- **R-6c-leaf-38 — the global cover bundle at a generator `x`. -/
noncomputable def ResolvedCoassocFinalLeafInventory.toGlobalCoverData
    (I : ResolvedCoassocFinalLeafInventory D G) (x : ResolvedHopfGen)
    (image_agreement : D.regroupImageSum x
      = ∑ z ∈ I.GrandFull.toFiniteData.imageCarrier, I.GrandFull.toFiniteData.imageWeight z)
    (branch_agreement :
      (∑ q ∈ I.GrandFull.toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
        + (∑ q ∈ I.GrandFull.toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
        = D.regroupBranchSum x) :
    ResolvedCoassocGlobalCoverData D x :=
  I.GrandFull.toGlobalCoverData x image_agreement branch_agreement

end GaugeGeometry.QFT.Combinatorial
