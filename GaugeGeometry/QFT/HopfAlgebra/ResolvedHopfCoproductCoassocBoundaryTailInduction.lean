import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocDirectBoundaryTail

/-!
# R-6c-body-89 — boundary_tail_eq induction scaffold: well-founded on `internalEdges.card`

Eighty-ninth genuine-body step, setting up the well-founded induction that proves `boundary_tail_eq` (body-88's
single reindex, = `Δᵣ`-coassociativity on the forest sum).  The measure is fixed, the strictly-smaller graphs
identified, and the induction skeleton proved; only the per-generator induction STEP is fielded.

## The measure: `internalEdges.card`

The two tails of the reindex apply `Δᵣ` to STRICTLY SMALLER graphs:

* RIGHT tail `coassocRightTail(forestSum G) = ∑_A leftTerm A ⊗ Δᵣ(rightTerm A)` applies `Δᵣ` to the QUOTIENT
  generator `rightTerm A = X(A.contractWithStars)` — the quotient graph has `internalEdges = A.complementEdges`
  (`contractWithStars_internalEdges` + `card_map`), and `A.complementEdges.card = G.I.card − A.I.card < G.I.card`
  since `A` is a PROPER forest (`0 < A.I.card`).  The flat analogue is PROVED:
  `antipodeForestRight_internalEdges_card_lt` (`Antipode`).
* LEFT tail `coassocLeftTail(forestSum G) = ∑_A assoc(Δᵣ(leftTerm A) ⊗ rightTerm A)` applies `Δᵣ` to the
  COMPONENT generators of `leftTerm A = ∏ X(component gen)` — each component `γ` is a proper subgraph of `G`,
  strictly smaller.

So `internalEdges.card` strictly decreases from `G` to both its quotient graphs and its components — the
well-founded measure (the same one the antipode / `AntipodeConvolution` induction uses).

## The scaffold (PROVED) and the fielded step

`resolved_graph_strong_induction` — strong induction on `internalEdges.card` (`Nat.strong_induction_on`), PROVED.
`ResolvedBoundaryTailInductionSupply` bundles the per-generator induction STEP (the genuine coassoc recursion:
`Δᵣ`-coassoc for `G` from `Δᵣ`-coassoc for all strictly smaller `H`) plus a representative lift (`rep`); its
`boundary_tail_eq` runs the strong induction, and `coassoc_gen` chains body-88.

The induction step is the CK / Zimmermann forest argument: expand both tails, apply the IH on the quotient (right)
and component (left) generators, and match via the recursive coproduct structure.  The flat template is
`Coassoc.coassoc_strict_forest_*`.  This is the genuine remaining content, fielded as `boundary_tail_step`.

Per the HALT: the induction STEP is not proved (it is `boundary_tail_step`); the measure and smaller-graph facts
are identified (flat `antipodeForestRight_internalEdges_card_lt` template); the skeleton is proved; no
star-allocation / retarget detail is entered.

Landed:

* `resolved_graph_strong_induction` — strong induction on `internalEdges.card` (PROVED);
* `ResolvedBoundaryTailInductionSupply D` — the induction step + representative lift;
* `.boundary_tail_eq` / `.toDirectBoundaryTailCoassocSupply` / `.coassoc_gen`.

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

set_option linter.unusedSectionVars false

/-- **R-6c-body-89 — strong induction on `internalEdges.card`.**  If `P` holds for every graph whenever it holds
for all strictly-fewer-internal-edge graphs, then `P` holds for all graphs.  The well-founded measure is
`internalEdges.card` (the antipode's induction measure). -/
theorem resolved_graph_strong_induction (P : ResolvedFeynmanGraph → Prop)
    (step : ∀ G, (∀ H, H.internalEdges.card < G.internalEdges.card → P H) → P G) :
    ∀ G, P G := by
  have key : ∀ n G, G.internalEdges.card = n → P G := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih => intro G hG; exact step G (fun H hH => ih H.internalEdges.card (hG ▸ hH) H rfl)
  exact fun G => key _ G rfl

/-- **R-6c-body-89 — the boundary_tail induction supply.**  The per-generator induction STEP (`Δᵣ`-coassoc for
`G` from `Δᵣ`-coassoc for all strictly-smaller graphs — the CK forest argument) plus a representative lift. -/
structure ResolvedBoundaryTailInductionSupply (D : ResolvedCoproductProperForestData) where
  /-- The induction step: the reindex for `G` from the reindex for all strictly-smaller graphs. -/
  boundary_tail_step : ∀ (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent),
    (∀ (H : ResolvedFeynmanGraph) (hCDH : H.forget.toClass.IsConnectedDivergent),
      H.internalEdges.card < G.internalEdges.card →
      D.regroupImageSum (H.toResolvedHopfGen hCDH) = D.regroupBranchSum (H.toResolvedHopfGen hCDH)) →
    D.regroupImageSum (G.toResolvedHopfGen hCD) = D.regroupBranchSum (G.toResolvedHopfGen hCD)
  /-- A representative graph for each generator. -/
  rep : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (rep x).forget.toClass.IsConnectedDivergent
  /-- The representative's generator IS `x`. -/
  rep_gen : ∀ x : ResolvedHopfGen, x = (rep x).toResolvedHopfGen (repCD x)

/-- **R-6c-body-89 — the reindex on every generator, by strong induction.** -/
theorem ResolvedBoundaryTailInductionSupply.boundary_tail_eq (S : ResolvedBoundaryTailInductionSupply D) :
    ∀ x : ResolvedHopfGen, D.regroupImageSum x = D.regroupBranchSum x := by
  have hP : ∀ G : ResolvedFeynmanGraph, ∀ hCD : G.forget.toClass.IsConnectedDivergent,
      D.regroupImageSum (G.toResolvedHopfGen hCD) = D.regroupBranchSum (G.toResolvedHopfGen hCD) := by
    refine resolved_graph_strong_induction
      (fun G => ∀ hCD, D.regroupImageSum (G.toResolvedHopfGen hCD)
        = D.regroupBranchSum (G.toResolvedHopfGen hCD)) ?_
    intro G ih hCD
    exact S.boundary_tail_step G hCD (fun H hCDH hlt => ih H hlt hCDH)
  intro x
  rw [S.rep_gen x]
  exact hP (S.rep x) (S.repCD x)

/-- **R-6c-body-89 — to body-88's direct boundary+tail supply.** -/
def ResolvedBoundaryTailInductionSupply.toDirectBoundaryTailCoassocSupply
    (S : ResolvedBoundaryTailInductionSupply D) : ResolvedDirectBoundaryTailCoassocSupply D where
  boundary_tail_eq := S.boundary_tail_eq

/-- **R-6c-body-89 — `coassoc_gen` from the induction supply** (via body-88). -/
theorem ResolvedBoundaryTailInductionSupply.coassoc_gen
    (S : ResolvedBoundaryTailInductionSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  S.toDirectBoundaryTailCoassocSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
