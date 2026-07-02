import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardInjectivity
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocSectorForwardLeaf
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRemnantScout

/-!
# R-6c-body-6 — Sector forward injectivity: right PROVED, forest ⟸ occurrence_inj

Sixth genuine-body step.  leaf-33's `right_forward_injective` / `forest_forward_injective` (the `LeftInverse`
side of the sector inverse laws) are discharged for the concrete assembler forward.

Both forward maps preserve `toResolvedFeynmanGraph` under the graph transport (`transport_pres`: `subst h; rfl`).

* **Right** — PROVED: `rightForward s r = transport (rightSurvivorComponentOf … r.toRightComponent)`, and the
  survivor re-embed keeps `γ`'s graph (`survivorReembed`, rfl), so `rightForward s r`'s graph is `r.i.η`'s;
  equal forwards ⇒ `r₁.i.η = r₂.i.η` (`ResolvedFeynmanSubgraph.ext`) ⇒ `r₁ = r₂` (index/subtype ext + proof
  irrelevance).
* **Forest** — from `occurrence_inj`: the remnant is the CONTRACTED source graph (`remnantGraph_eq :
  remnantComponent o = o.contractedSourceGraph`), so `forestForward s f`'s graph is `f.toOccurrence.contractedSourceGraph`;
  equal forwards ⇒ (`occurrence_inj`) `f₁.toOccurrence = f₂.toOccurrence` ⇒ `f₁ = f₂` (via `.γ`).  The
  `occurrence_inj` (de-contraction uniqueness, = leaf-9's) is the supply field.

Per the HALT, `occurrence_inj` is the supply field; element shapes / retarget / perm untouched.

Landed:

* `transport_pres` — transport preserves `toResolvedFeynmanGraph`;
* `ResolvedSectorForwardInjBodySupply C A` — `occurrence_inj`;
* `.toSectorForwardInjectivityConnector` — leaf-33's connector (right PROVED, forest from `occurrence_inj`).

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

set_option linter.unusedSectionVars false in
/-- **R-6c-body-6 — transport preserves the intrinsic resolved graph. -/
theorem transport_pres {H K : ResolvedFeynmanGraph} (h : H = K) (δ : ResolvedFeynmanSubgraph H) :
    (transportSubgraphAlongGraphEq h δ).toResolvedFeynmanGraph = δ.toResolvedFeynmanGraph := by
  subst h; rfl

variable {C : ResolvedCodomainConcreteSupply D G imageOf}

/-- **R-6c-body-6 — the forward-injectivity body supply.**  Only the occurrence de-contraction injectivity
(the forest side); the right side is proved. -/
structure ResolvedSectorForwardInjBodySupply (C : ResolvedCodomainConcreteSupply D G imageOf)
    (A : ResolvedSectorForwardAssemblerSupply C) where
  /-- Distinct forest occurrences have distinct contracted source graphs (de-contraction uniqueness). -/
  occurrence_inj : ∀ (s : ResolvedCoassocSplitChoice D G) (o₁ o₂ : s.ForestChoiceOccurrence),
    o₁.contractedSourceGraph = o₂.contractedSourceGraph → o₁ = o₂

/-- **R-6c-body-6 — the leaf-33 forward-injectivity connector (right PROVED, forest from `occurrence_inj`). -/
def ResolvedSectorForwardInjBodySupply.toSectorForwardInjectivityConnector
    {A : ResolvedSectorForwardAssemblerSupply C}
    (S : ResolvedSectorForwardInjBodySupply C A) :
    ResolvedSectorForwardInjectivityConnector C A.toSectorForwardConcreteSupply where
  right_forward_injective := fun s r₁ r₂ h => by
    have key : ∀ r : RightPrimitiveIndex D G s,
        (A.toSectorForwardConcreteSupply.rightForward s r).toResolvedFeynmanGraph
          = r.i.η.toResolvedFeynmanGraph := fun r => transport_pres _ _
    have hg : r₁.i.η.toResolvedFeynmanGraph = r₂.i.η.toResolvedFeynmanGraph := by
      rw [← key r₁, ← key r₂]; exact congrArg _ h
    obtain ⟨⟨η₁, hη₁⟩, hR₁⟩ := r₁
    obtain ⟨⟨η₂, hη₂⟩, hR₂⟩ := r₂
    have hη : η₁ = η₂ := ResolvedFeynmanSubgraph.ext
      (congrArg (·.vertices) hg) (congrArg (·.internalEdges) hg) (congrArg (·.externalLegs) hg)
    subst hη; rfl
  forest_forward_injective := fun s f₁ f₂ h => by
    have key : ∀ f : ForestPrimitiveIndex D G s,
        (A.toSectorForwardConcreteSupply.forestForward s f).toResolvedFeynmanGraph
          = f.toOccurrence.contractedSourceGraph := fun f =>
      (transport_pres _ _).trans ((A.Local.remnant s).remnantGraph_eq f.toOccurrence)
    have hcg : f₁.toOccurrence.contractedSourceGraph = f₂.toOccurrence.contractedSourceGraph := by
      rw [← key f₁, ← key f₂]; exact congrArg _ h
    have hocc := S.occurrence_inj s f₁.toOccurrence f₂.toOccurrence hcg
    have hη : f₁.i.η = f₂.i.η := congrArg (fun o => o.γ.1) hocc
    obtain ⟨⟨η₁, hη₁⟩, hF₁⟩ := f₁
    obtain ⟨⟨η₂, hη₂⟩, hF₂⟩ := f₂
    subst hη; rfl

end GaugeGeometry.QFT.Combinatorial
