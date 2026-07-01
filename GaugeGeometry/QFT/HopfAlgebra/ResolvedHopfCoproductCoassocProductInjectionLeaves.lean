import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductConnectors
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocProductDisjointLeaves

/-!
# R-6c-leaf-5 — Product injection leaves + the full Product leaf bundle

Fifth leaf-discharge step (the last STRUCTURAL Product grouping).  The two component-injectivity leaves are
grouped into one record, and — with the gen (leaf-2), connector (leaf-3), and disjointness (leaf-4) groups —
the whole `ResolvedProductEqGrandSupply` is assembled from ONE bundle:

```text
ResolvedProductEqGrandSupply  ⟸  Gen + Connector + Disjoint + Injection
```

* `ResolvedProductGenSupply` — `survivorGen` + `remnantGen` (grouping the leaf-2 targets);
* `ResolvedProductInjectionSupply` — `survivorInj` + `remnantInj`;
* `ResolvedProductLeafBundle` — `R` / `M` + the four groups, with `.toProductEqGrandSupply`.

Per the HALT, `survivorInj` / `remnantInj` are NOT proved (fields — id-tracked component injectivity is the
genuine remaining geometry); the gen/disjoint/connector bodies are the earlier groups' fields.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-leaf-5 — the Product gen supply.**  Groups the two generator equalities (leaf-2's targets). -/
structure ResolvedProductGenSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- Survivor component generator equality. -/
  survivorGen : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.rightComponents}),
    resolvedComponentGenTerm (R.survivorComponent s γ) = resolvedComponentGenTerm γ.1.1
  /-- Remnant component generator equality. -/
  remnantGen : ∀ (s : ResolvedCoassocSplitChoice D G)
    (γ : {x : {y : ResolvedFeynmanSubgraph G // y ∈ s.1.1.elements} // x ∈ s.forestComponents}),
    resolvedComponentGenTerm (M.remnantComponent s (s.forestComponentOccurrence γ))
      = D.rightFactorOf s γ.1

/-- **R-6c-leaf-5 — the Product injection supply.**  Groups the two component-injectivity leaves. -/
structure ResolvedProductInjectionSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (R : ResolvedRightSurvivorSupply D G) (M : ResolvedRemnantComponentSupply D G) where
  /-- Survivor component injectivity. -/
  survivorInj : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ s.rightComponents.attach, ∀ γ₂ ∈ s.rightComponents.attach,
      R.survivorComponent s γ₁ = R.survivorComponent s γ₂ → γ₁ = γ₂
  /-- Remnant component injectivity. -/
  remnantInj : ∀ (s : ResolvedCoassocSplitChoice D G),
    ∀ γ₁ ∈ s.forestComponents.attach, ∀ γ₂ ∈ s.forestComponents.attach,
      M.remnantComponent s (s.forestComponentOccurrence γ₁)
        = M.remnantComponent s (s.forestComponentOccurrence γ₂) → γ₁ = γ₂

/-- **R-6c-leaf-5 — the full Product leaf bundle.**  `R` / `M` + the four leaf groups; assembles the whole
`ResolvedProductEqGrandSupply`. -/
structure ResolvedProductLeafBundle (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph)
    (imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G) where
  /-- The right-survivor supply. -/
  R : ResolvedRightSurvivorSupply D G
  /-- The remnant component supply. -/
  M : ResolvedRemnantComponentSupply D G
  /-- The two generator equalities (leaf-2). -/
  Gen : ResolvedProductGenSupply D G imageOf R M
  /-- The two term connectors (leaf-3). -/
  Connector : ResolvedProductConnectorSupply D G imageOf R M
  /-- The four disjointness leaves (leaf-4). -/
  Disjoint : ResolvedProductDisjointSupply D G R M
  /-- The two injection leaves. -/
  Injection : ResolvedProductInjectionSupply D G R M

/-- **R-6c-leaf-5 — the Product grand supply from the leaf bundle.**  `product_eq` now flows from a single
`ResolvedProductLeafBundle`. -/
def ResolvedProductLeafBundle.toProductEqGrandSupply
    {imageOf : ResolvedCoassocSplitChoice D G → ResolvedCoassocQuotientImage D G}
    (B : ResolvedProductLeafBundle D G imageOf) : ResolvedProductEqGrandSupply D G imageOf where
  R := B.R
  M := B.M
  hPD := B.Disjoint.hPD
  hLP := B.Disjoint.hLP
  survivorInj := B.Injection.survivorInj
  survivorGen := B.Gen.survivorGen
  remnantInj := B.Injection.remnantInj
  remnantGen := B.Gen.remnantGen
  hCross := B.Disjoint.hCross
  hDisj := B.Disjoint.hDisj
  hSel := B.Connector.hSel
  hQuot := B.Connector.hQuot B.Disjoint.hCross B.Disjoint.hDisj

end GaugeGeometry.QFT.Combinatorial
