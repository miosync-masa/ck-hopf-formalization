import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorEquivAssembler

/-!
# R-6c-leaf-19 — Sector leaf inventory (Forward + Backward + Inverse), inverse laws grouped

Scout / organization pass on the BIGGEST RIGHT block — the sector equivalence.  The exact leaf inventory of
`ResolvedSectorEquivAssemblerSupply C` (6a-10g-1) is:

* **Forward** (`ResolvedSectorForwardConcreteSupply C`, 6a-10f) — ALREADY fully concrete: just the two forward
  maps + their memberships (`rightForward` / `rightForward_mem` into `C.rightForest`, `forestForward` /
  `forestForward_mem` into `C.remnantForest`).  (The earlier `hne` / `remnant` / `quotientGraph_eq` /
  `rightLocal_mem` / `forestLocal_mem` were the 6a-10f-2/3/4 *construction* leaves, already collapsed into
  these four fields — so Forward needs no further splitting.)
* **Backward** (`ResolvedSectorBackwardSupply C`) — `componentToRight` / `componentToForest`.
* **Inverse** — the four `Function.Left/RightInverse` laws (right & forest sectors).

This file records that split as one inventory record and groups the four inverse laws into
`ResolvedSectorInverseLawSupply` (they were genuinely PROVED in the fix-3c series — here they are only
re-bundled, not re-proved), with `.toAssembler` reconstructing the assembler.

Per the HALT, no concrete proofs; Perm / Retarget untouched; backward-map bodies untouched.

Landed:

* `ResolvedSectorInverseLawSupply C Forward Backward` — the four inverse laws;
* `ResolvedSectorLeafSupply C` — `Forward` + `Backward` + `Inverse`, with `.toAssembler`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}
  {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}

/-- **R-6c-leaf-19 — the four sector inverse laws, grouped.**  The right / forest sector left & right
inverses over the forward and backward maps. -/
structure ResolvedSectorInverseLawSupply {C : ResolvedCodomainConcreteSupply D G imageOf}
    (Forward : ResolvedSectorForwardConcreteSupply C) (Backward : ResolvedSectorBackwardSupply C) where
  /-- Right sector left inverse. -/
  right_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToRight s) (Forward.rightToComponent s)
  /-- Right sector right inverse. -/
  right_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToRight s) (Forward.rightToComponent s)
  /-- Forest sector left inverse. -/
  forest_left_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.LeftInverse (Backward.componentToForest s) (Forward.forestToComponent s)
  /-- Forest sector right inverse. -/
  forest_right_inv : ∀ s : ResolvedCoassocSplitChoice D G,
    Function.RightInverse (Backward.componentToForest s) (Forward.forestToComponent s)

/-- **R-6c-leaf-19 — the sector leaf inventory.**  The BIGGEST RIGHT block, split into its three parts. -/
structure ResolvedSectorLeafSupply (C : ResolvedCodomainConcreteSupply D G imageOf) where
  /-- The concrete forward maps + memberships (6a-10f). -/
  Forward : ResolvedSectorForwardConcreteSupply C
  /-- The backward maps. -/
  Backward : ResolvedSectorBackwardSupply C
  /-- The four inverse laws (fix-3c). -/
  Inverse : ResolvedSectorInverseLawSupply Forward Backward

/-- **R-6c-leaf-19 — reconstruct the full sector-equiv assembler from the inventory. -/
def ResolvedSectorLeafSupply.toAssembler {C : ResolvedCodomainConcreteSupply D G imageOf}
    (S : ResolvedSectorLeafSupply C) : ResolvedSectorEquivAssemblerSupply C where
  Forward := S.Forward
  Backward := S.Backward
  right_left_inv := S.Inverse.right_left_inv
  right_right_inv := S.Inverse.right_right_inv
  forest_left_inv := S.Inverse.forest_left_inv
  forest_right_inv := S.Inverse.forest_right_inv

end GaugeGeometry.QFT.Combinatorial
