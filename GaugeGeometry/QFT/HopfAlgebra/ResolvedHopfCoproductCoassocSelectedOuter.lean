import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocImageSupply

/-!
# R-6c-4f part 3c-1 — the selected-outer supply (scout result + isolation)

Scout result (flat template, `Coassoc.lean`): the selected outer forest of a split choice is

  `forestComponentForestChoiceOuterSubgraph A p = AdmissibleSubgraph.ofElements`
    `((forestComponentChoiceLeftSubgraph A p).elements ∪ forestComponentChoicePromotedForestComponents A p)`

— the **left-selected** components (`A.elements.filter isLeft`) together with the **promoted** forest
components (`A.elements.attach.biUnion (forest B ↦ promote B | _ ↦ ∅)`), with a substantial admissibility
proof (CD + nested-or-disjoint) and the promotion via `feynmanSubgraphRepForestPromoteAdmissibleSubgraph`.

The resolved building blocks for this — a resolved `AdmissibleSubgraph.ofElements`/`ofSubelements` and a
resolved `feynmanSubgraphRepForestPromoteAdmissibleSubgraph` (plus the disjointness lemmas) — **do not
yet exist**.  So (per the HALT) the selected-outer construction is **isolated as a supply**: the raw
forest and its carrier membership are fields, separating the (combinatorial) forest from the
(carrier-closure) membership obligation.

Landed:

* `ResolvedCoassocSelectedOuterSupply D G` — `selectedOuterRaw` (the selected outer forest) +
  `selectedOuter_mem` (its carrier membership);
* `ResolvedCoassocSelectedOuterSupply.toSelectedOuterOf` — the bundled
  `ResolvedCoassocSplitChoice D G → {A // A ∈ D.carrier G}` for the image supply.

No facade, no flat splitPhi theorem, no `forgetHopf`; the concrete `selectedOuterRaw` (needing the
resolved `ofElements`/promote infrastructure) is the deferred build.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-4f part 3c-1 — the selected-outer supply.**  The selected outer forest of a split choice
(the resolved `forestComponentForestChoiceOuterSubgraph`: left-selected ∪ promoted components),
isolated as a raw forest plus its carrier membership — the two genuine de-contraction obligations. -/
structure ResolvedCoassocSelectedOuterSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) where
  /-- The selected outer forest of a split choice (left-selected ∪ promoted components). -/
  selectedOuterRaw : ResolvedCoassocSplitChoice D G → ResolvedAdmissibleSubgraph G
  /-- The selected outer forest is a carrier forest (the sub-forest-closure obligation). -/
  selectedOuter_mem : ∀ s, selectedOuterRaw s ∈ D.carrier G

/-- The bundled selected-outer map `ResolvedCoassocSplitChoice D G → {A // A ∈ D.carrier G}` for the
image supply. -/
def ResolvedCoassocSelectedOuterSupply.toSelectedOuterOf
    (S : ResolvedCoassocSelectedOuterSupply D G) :
    ResolvedCoassocSplitChoice D G → {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G} :=
  fun s => ⟨S.selectedOuterRaw s, S.selectedOuter_mem s⟩

end GaugeGeometry.QFT.Combinatorial
