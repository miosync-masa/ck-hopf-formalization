import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardMembership
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorLocalConcrete

/-!
# R-6c-leaf-29 — concrete Codomain right forest ⇒ Sector `rightLocal_mem` (via `mem_image`)

Twenty-fourth leaf-body discharge — concretizing the Codomain right forest to discharge the Sector Forward
right membership.  When the Codomain's `rightForest` is the `ofElements` over the transported local survivor
components (indexed by `s.rightComponents.attach`), the membership `rightLocal_mem` is `mem_image` +
`mem_attach`: `Local.rightLocal s r = rightSurvivorComponentOf s (Local.hne s) (Local.hcompl s) r.toRightComponent`,
which is exactly the image function at `r.toRightComponent ∈ rightComponents.attach`.

The forest side (`forestLocal_mem`) needs `f.toOccurrence = forestComponentOccurrence γ` (an occurrence match
through `Classical.choose` proof-irrelevance) — heavier — so it stays a field here (per the HALT "land the
elements_eq connector and stop").

Per the HALT, no finite `RightPrimitiveIndex` enumeration is built (the image is over the concrete
`rightComponents.attach` Finset); CD / disjoint of the Codomain forest untouched.

Landed:

* `ResolvedConcreteCodomainRightMembershipSupply C Local Align` — `rightForest_elements_eq` (the image shape)
  + `forestLocal_mem` (field);
* `.toSectorForwardMembershipSupply` — `rightLocal_mem` DERIVED (`mem_image`), `forestLocal_mem` from the field.

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

open scoped Classical

/-- **R-6c-leaf-29 — concrete Codomain right forest + the forest-side membership.**  The right forest's
elements are the transported local survivor components over `rightComponents.attach`; the remnant-side
membership stays a field. -/
structure ResolvedConcreteCodomainRightMembershipSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Local : ResolvedSectorLocalComponentSupply D G)
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf) where
  /-- The Codomain right forest is the `ofElements`-image of the transported local survivor components. -/
  rightForest_elements_eq : ∀ s : ResolvedCoassocSplitChoice D G,
    (C.rightForest s).elements =
      s.rightComponents.attach.image (fun γ =>
        transportSubgraphAlongGraphEq (Align.quotientGraph_eq s)
          (rightSurvivorComponentOf s (Local.hne s) (Local.hcompl s) γ))
  /-- The transported remnant component lies in the remnant forest (heavier occurrence match — fielded). -/
  forestLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (f : ForestPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.forestLocal s f)
      ∈ (C.remnantForest s).elements

/-- **R-6c-leaf-29 — the Sector Forward membership supply, with `rightLocal_mem` DERIVED via `mem_image`. -/
def ResolvedConcreteCodomainRightMembershipSupply.toSectorForwardMembershipSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {Local : ResolvedSectorLocalComponentSupply D G}
    {Align : ResolvedSectorForwardGraphAlignment D G imageOf}
    (M : ResolvedConcreteCodomainRightMembershipSupply C Local Align) :
    ResolvedSectorForwardMembershipSupply C Local Align where
  rightLocal_mem := fun s r => by
    rw [M.rightForest_elements_eq s]
    exact Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
  forestLocal_mem := M.forestLocal_mem

end GaugeGeometry.QFT.Combinatorial
