import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardAssembler

/-!
# R-6c-leaf-28 — Sector Forward membership (completing the Forward bundle)

Twenty-third leaf-body discharge — the Forward assembler's two membership facts.  `ResolvedSectorForwardAssemblerSupply`
(6a-10f-4) is `Local` + `Align` + `rightLocal_mem` + `forestLocal_mem`.  With `Local` concrete (leaf-27) and
`Align` from the selected-outer equality (leaf-20/25), the only residual is the two memberships: the transported
local survivor / remnant components land in the Codomain's right / remnant forests.

The Codomain forests (`ResolvedCodomainConcreteSupply.rightForest` / `remnantForest`) are supply fields, so the
memberships stay fielded here (they become `mem_image` / `mem_ofElements` once the Codomain is the concrete
`ofElements`-over-transported-components — that is the Codomain's own construction, leaf-15's territory).  This
file groups them and completes the Forward bundle.

Per the HALT, the memberships are not proved (Codomain forests abstract); backward maps untouched.

Landed:

* `ResolvedSectorForwardMembershipSupply C Local Align` — `rightLocal_mem` + `forestLocal_mem`;
* `toSectorForwardAssemblerSupply` — the Forward assembler from `Local` + `Align` + membership.

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

/-- **R-6c-leaf-28 — the Sector Forward membership supply.**  The transported local components land in the
Codomain right / remnant forests. -/
structure ResolvedSectorForwardMembershipSupply
    (C : ResolvedCodomainConcreteSupply D G imageOf)
    (Local : ResolvedSectorLocalComponentSupply D G)
    (Align : ResolvedSectorForwardGraphAlignment D G imageOf) where
  /-- The transported survivor component lies in the right-survivor forest. -/
  rightLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (r : RightPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.rightLocal s r)
      ∈ (C.rightForest s).elements
  /-- The transported remnant component lies in the remnant forest. -/
  forestLocal_mem : ∀ (s : ResolvedCoassocSplitChoice D G) (f : ForestPrimitiveIndex D G s),
    transportSubgraphAlongGraphEq (Align.quotientGraph_eq s) (Local.forestLocal s f)
      ∈ (C.remnantForest s).elements

/-- **R-6c-leaf-28 — the Forward assembler from Local + Align + membership.** -/
def ResolvedSectorForwardMembershipSupply.toSectorForwardAssemblerSupply
    {C : ResolvedCodomainConcreteSupply D G imageOf}
    {Local : ResolvedSectorLocalComponentSupply D G}
    {Align : ResolvedSectorForwardGraphAlignment D G imageOf}
    (Mem : ResolvedSectorForwardMembershipSupply C Local Align) :
    ResolvedSectorForwardAssemblerSupply C where
  Local := Local
  Align := Align
  rightLocal_mem := Mem.rightLocal_mem
  forestLocal_mem := Mem.forestLocal_mem

end GaugeGeometry.QFT.Combinatorial
