import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientGraphAlign
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSelectedOuterMem
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSupply

/-!
# R-6c-leaf-25 — `selectedOuter_eq` PROVED for the concrete image side (`rfl`)

Twentieth leaf-body discharge — a high-leverage one.  For the CONCRETE image side (`imageOf` built from
`resolvedConcreteSelectedOuterImageSupply` via `toImageSupplySkeleton`/`toImageOfData`), the selected-outer
alignment `selectedOuter_eq` is definitional:

* `toImageOfData.imageOf s = ⟨S.selectedOuterOf s, S.quotientForestOf s⟩` (ImageSupply:64), so
  `(imageOf s).selectedOuter.1 = (S.selectedOuterOf s).1`;
* `S.selectedOuterOf = S.toSelectedOuterSupply.toSelectedOuterOf` with `selectedOuterRaw := S.promoteSupply.selectedOuterRawOf`,
  and for `S = resolvedConcreteSelectedOuterImageSupply D G mem` the promote supply's `selectedOuterRawOf`
  is `(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf` — the same `leftOf.union promotedOf`.

Both steps hold by `rfl`, so `selectedOuter_eq := fun s => rfl`.  Via leaf-20 this ONE `rfl` discharges BOTH
the Sector Align's `quotientGraph_eq` and the Product connector's `hSel`.

Per the HALT, `quotientForest_eq` is untouched; Sector maps / Perm / Retarget untouched.  `mem` (the carrier
closure of `selectedOuterRawOf`) and the skeleton inputs `quotientForestOf` / `imageWeightOf` /
`discriminatorOf` remain the caller's data (they don't affect `selectedOuter_eq`).

Landed:

* `concreteSelectedOuterAlignment` — the `ResolvedSelectedOuterAlignment` for the concrete image side, with
  `selectedOuter_eq := rfl`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-25 — the selected-outer alignment for the concrete image side (`selectedOuter_eq` by `rfl`).**
The image built from `resolvedConcreteSelectedOuterImageSupply` has `(imageOf s).selectedOuter.1` definitionally
equal to `(resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s`. -/
def concreteSelectedOuterAlignment
    (mem : ∀ s, (resolvedConcreteForestPromoteSupply D G).selectedOuterRawOf s ∈ D.carrier G)
    (quotientForestOf : (s : ResolvedCoassocSplitChoice D G) →
      ResolvedAdmissibleSubgraph
        (((resolvedConcreteSelectedOuterImageSupply D G mem).selectedOuterOf s).1.contractWithStars
          (D.starOf G ((resolvedConcreteSelectedOuterImageSupply D G mem).selectedOuterOf s).1)))
    (imageWeightOf : ResolvedCoassocQuotientImage D G → ResolvedHopfH3)
    (discriminatorOf : ResolvedCoassocQuotientImage D G → Prop) :
    ResolvedSelectedOuterAlignment D G
      (((resolvedConcreteSelectedOuterImageSupply D G mem).toImageSupplySkeleton
        quotientForestOf imageWeightOf discriminatorOf).toImageOfData.imageOf) where
  selectedOuter_eq := fun _ => rfl

end GaugeGeometry.QFT.Combinatorial
