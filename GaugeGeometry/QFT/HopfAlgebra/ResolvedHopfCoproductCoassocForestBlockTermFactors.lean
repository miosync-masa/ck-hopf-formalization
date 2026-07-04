import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForestImageClassifier

/-!
# R-6c-body-103 — term-factor geometry: the 6 identities reduce to component-set correspondences

Hundred-and-third genuine-body step, a scout/toolkit for the six geometric identities left in body-101/102's map
data.  Body-99/100 already discharged all tensor algebra (the split-term factors as `(∏ leftFactor) ⊗ ((∏
rightFactor) ⊗ rightTerm A)`), so each remaining identity is now a pure PRODUCT-OVER-COMPONENTS statement about
`leftTerm` / `rightTerm`.  This body proves the generic product algebra and pins the residue to map-specific
component-set correspondences.

## The generic term structure (PROVED)

* `resolved_leftTerm_eq_prod`: `leftTerm A = ∏_{γ ∈ A.elements} X(component gen)` — `leftTerm` IS a product over
  components (`resolvedForestLeftTerm`, definitional);
* `resolved_rightTerm_eq_X`: `rightTerm A = X(A.contractWithStars gen)` — the quotient generator (definitional);
* the local factor evaluations (`localLeftFactor_inl_true = X`, `_inl_false = 1`, `_inr = leftTerm B`; the
  mirror for `localRightFactor`) — each `rfl`.

## The generic product lemma (PROVED)

`resolved_prod_bif_eq_filter`: `∏_{i ∈ s} (bif c i then x i else 1) = ∏_{i ∈ s.filter (c · = true)} x i` — the
right-primitive factors (`1`) drop out of a product.  This is what turns `∏ localLeftFactor` (which is `X` on
left-primitives, `1` on right-primitives, `leftTerm Bᵧ` on forest components) into a product over the selected
components only.

## How the six identities reduce

With the above, each identity becomes a `Finset.prod` equality between the SOURCE component product and the
TARGET (`A_target` or `B`) component product — a `Finset.prod_bij` over the map's component correspondence:

* `left_eq` (`∏ localLeftFactor = leftTerm A_target`): `A_target` is the LEFT subgraph — its components are the
  left-primitive components plus the sub-forest components of the forest choices; `leftTerm A_target = ∏ X` over
  them equals `∏ localLeftFactor` (right-primitives contribute `1`).  Reduces to `A_target.elements ↔
  {left-selected source pieces}` with matching generators;
* `right_eq` (`∏ localRightFactor = leftTerm B`): symmetric — `B`'s components are the right-primitive components
  (mixed) / right-selected pieces (forest);
* `quotient_eq` (`rightTerm A' = rightTerm B`): a pure contract-twice graph identity `X(A'.contractWithStars) =
  X(B.contractWithStars-in-the-quotient)` — no product, fielded as a generator equality.

So the six identities need exactly: the map's component-set correspondences (`A_target` / `B` component
bijections) and the contract-twice generator identity — all map-specific, deferred to the map construction.  The
tensor and product algebra is done.

Per the HALT: only generic product algebra is proved; the map-specific component-set equalities stay fielded (in
body-101/102's map data); no FullQuotient map construction is entered; no star allocation detail.

Landed:

* `resolved_leftTerm_eq_prod` / `resolved_rightTerm_eq_X` — the term product/generator structure (PROVED);
* `localLeftFactor_inl_true` / `_inl_false` / `_inr`, `localRightFactor_inl_true` / `_inl_false` / `_inr` — the
  factor evaluations (PROVED);
* `resolved_prod_bif_eq_filter` — the right-primitive drop-out (PROVED).

No new supply (a scout/toolkit body, like body-86/87); these lemmas discharge the map data's geometric identities
once the map is built.  No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-103 — `leftTerm` is a product over components.**  `leftTerm A = ∏_{γ ∈ A.elements} X(component
gen)` — definitional (`resolvedForestLeftTerm`). -/
theorem resolved_leftTerm_eq_prod (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (D.supply G).leftTerm A
      = ∏ γ ∈ A.1.elements.attach,
          MvPolynomial.X (resolvedComponentGen γ.1 (A.1.isConnectedDivergent γ.1 γ.2)) :=
  rfl

/-- **R-6c-body-103 — `rightTerm` is the quotient generator.**  `rightTerm A = X(A.contractWithStars gen)`. -/
theorem resolved_rightTerm_eq_X (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}) :
    (D.supply G).rightTerm A
      = MvPolynomial.X ((A.1.contractWithStars (D.starOf G A.1)).toResolvedHopfGen (D.hCD G A.1 A.2)) :=
  rfl

/-- **R-6c-body-103 — left factor on a left primitive** (`X`). -/
theorem localLeftFactor_inl_true (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    localLeftFactor (D := D) γG hCD (Sum.inl true) = MvPolynomial.X (γG.toResolvedHopfGen hCD) := rfl

/-- **R-6c-body-103 — left factor on a right primitive** (`1`). -/
theorem localLeftFactor_inl_false (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    localLeftFactor (D := D) γG hCD (Sum.inl false) = (1 : ResolvedHopfH) := rfl

/-- **R-6c-body-103 — left factor on a forest choice** (`leftTerm Bᵧ`). -/
theorem localLeftFactor_inr (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) (B : (D.supply γG).ForestIdx) :
    localLeftFactor (D := D) γG hCD (Sum.inr B) = (D.supply γG).leftTerm B := rfl

/-- **R-6c-body-103 — right factor on a left primitive** (`1`). -/
theorem localRightFactor_inl_true (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    localRightFactor (D := D) γG hCD (Sum.inl true) = (1 : ResolvedHopfH) := rfl

/-- **R-6c-body-103 — right factor on a right primitive** (`X`). -/
theorem localRightFactor_inl_false (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) :
    localRightFactor (D := D) γG hCD (Sum.inl false) = MvPolynomial.X (γG.toResolvedHopfGen hCD) := rfl

/-- **R-6c-body-103 — right factor on a forest choice** (`rightTerm Bᵧ`). -/
theorem localRightFactor_inr (γG : ResolvedFeynmanGraph)
    (hCD : γG.forget.toClass.IsConnectedDivergent) (B : (D.supply γG).ForestIdx) :
    localRightFactor (D := D) γG hCD (Sum.inr B) = (D.supply γG).rightTerm B := rfl

/-- **R-6c-body-103 — right-primitive factors drop out.**  In a product where each factor is `bif c i then x i
else 1`, the `1`s (right primitives) drop, leaving the product over the selected components. -/
theorem resolved_prod_bif_eq_filter {ι : Type*} (s : Finset ι) (c : ι → Bool) (x : ι → ResolvedHopfH) :
    (∏ i ∈ s, (bif c i then x i else 1)) = ∏ i ∈ s.filter (fun i => c i = true), x i := by
  rw [Finset.prod_filter]
  exact Finset.prod_congr rfl (fun i _ => by cases c i <;> simp)

end GaugeGeometry.QFT.Combinatorial
