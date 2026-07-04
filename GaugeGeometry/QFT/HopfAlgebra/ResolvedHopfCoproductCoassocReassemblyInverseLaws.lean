import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocReassemblyFromSector
import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocConcreteSummandBundle

/-!
# R-6c-body-136 — regionwise inverse-law decomposition: the four inverse laws as outer + roundtrip

Hundred-and-thirty-sixth genuine-body step, decomposing the bijection's four inverse laws.  With `invConstruct =
⟨recoverOuter, recoverChoice⟩` (body-134), each inverse law is a DEPENDENT-PAIR (`Sigma`) equality; `Sigma.ext`
splits it into an OUTER forest equality and a (heterogeneous) SECOND-COMPONENT equality.  This body proves the
formal `Sigma.ext` adapter, reducing the four laws to those two ingredients — the outer equality and the
second-component roundtrip — so exactly what the concrete `recoverOuter` / `recoverChoice` must satisfy becomes
visible.

## The two roundtrips (`Sigma.ext`, PROVED)

Only two facts are distinct (mixed / forest differ only in the domain hypothesis `hq`, which the conclusion does
not use):

* `left_inv` (`invConstruct ∘ forward = id` on `(A', p)`): `Reassembly.invConstruct ⟨selectedOuterOf q,
  quotientForest q⟩ = q`, via `Sigma.ext (left_inv_outer q) (left_inv_choice q)` — the OUTER equality `recoverOuter
  (forward q) = q.1` plus the CHOICE roundtrip `HEq (recoverChoice (forward q)) q.2`;
* `right_inv` (`forward ∘ invConstruct = id` on `(A, B)`): `⟨selectedOuterOf (invConstruct r), quotientForest
  (invConstruct r)⟩ = r`, via `Sigma.ext (right_inv_outer r) (right_inv_quot r)` — the OUTER equality
  `selectedOuterOf (invConstruct r) = r.1` plus the QUOTIENT roundtrip `HEq (quotientForest (invConstruct r)) r.2`.

## What the roundtrips decompose into (region-wise, for the concrete `recoverOuter`)

The choice roundtrip `HEq (recoverChoice (forward q)) q.2` decomposes over `region_cover` (body-135): each
`A'`-component of `q` re-tags into the three regions by its original `p`-value, and

* a `leftRegion` component (`p = inl true`) roundtrips by the left-residual identity;
* a `rightRegion` component (`p = inl false`) roundtrips by the sector `componentToRight` round-trip
  (`right_left_inv`, `SectorLeafBundle`);
* a `forestRegion` component (`p = inr Bᵧ`) roundtrips by the sector `componentToForest` round-trip
  (`forest_left_inv`).

Symmetrically the quotient roundtrip uses the sector `right_right_inv` / `forest_right_inv` on `B`'s survivor /
remnant components.  So the four inverse laws reduce to the outer equalities plus the three region roundtrips
linked to the four `SectorLeafBundle` laws.

Per the HALT: only the formal `Sigma.ext` adapter is proved; the outer equalities and the second-component
roundtrips are fielded (they need the concrete `recoverOuter`); no concrete map is built.

Landed:

* `ResolvedReassemblyInverseLawSupply D S` — the reassembly + the outer/roundtrip fields;
* `.left_inv` / `.right_inv` — the two `Sigma.ext` roundtrips;
* `.mixed_left_inv` / `.forest_left_inv` / `.mixed_right_inv` / `.forest_right_inv` — the four provider inverse-law
  fields.

Toolkit body (like body-134/135), one adapter supply.  No facade, no flat term, no `forgetHopf`.
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
set_option linter.unusedVariables false

/-- **R-6c-body-136 — the regionwise inverse-law supply.**  The reassembly data together with the two outer
equalities and the two heterogeneous second-component roundtrips, against a fixed summand bundle `S`.  From these,
the four provider inverse laws follow by `Sigma.ext`. -/
structure ResolvedReassemblyInverseLawSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) where
  /-- The structured backward map (body-134). -/
  Reassembly : ResolvedOuterMixingReassemblyData D
  /-- `left_inv` outer: the recovered outer of the forward is the original outer. -/
  left_inv_outer : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    Reassembly.recoverOuter
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q.1
  /-- `left_inv` choice roundtrip: the recovered choice of the forward is the original choice (heterogeneous). -/
  left_inv_choice : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    HEq (Reassembly.recoverChoice
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)) q.2
  /-- `right_inv` outer: the selected outer of the reconstruction is the original target outer. -/
  right_inv_outer : ∀ {G : ResolvedFeynmanGraph} (r : ForestBlockCodType D G),
    (S.Forward.imageSupply G).selectedOuterOf (Reassembly.invConstruct r) = r.1
  /-- `right_inv` quotient roundtrip: the quotient forest of the reconstruction is the original `B`
  (heterogeneous). -/
  right_inv_quot : ∀ {G : ResolvedFeynmanGraph} (r : ForestBlockCodType D G),
    HEq (S.quotientForest (Reassembly.invConstruct r)) r.2

namespace ResolvedReassemblyInverseLawSupply

variable {S : ResolvedConcreteSummandBundleSupply D}

/-- **R-6c-body-136 — the `left_inv` roundtrip** (`invConstruct ∘ forward = id`). -/
theorem left_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    M.Reassembly.invConstruct
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q :=
  Sigma.ext (M.left_inv_outer q) (M.left_inv_choice q)

/-- **R-6c-body-136 — the `right_inv` roundtrip** (`forward ∘ invConstruct = id`). -/
theorem right_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (r : ForestBlockCodType D G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf (M.Reassembly.invConstruct r),
        S.quotientForest (M.Reassembly.invConstruct r)⟩ : ForestBlockCodType D G) = r :=
  Sigma.ext (M.right_inv_outer r) (M.right_inv_quot r)

/-- **R-6c-body-136 — the provider's `mixed_left_inv`.** -/
theorem mixed_left_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) (hq : q ∈ mixedDomFinset G) :
    M.Reassembly.invConstruct
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q :=
  M.left_inv G q

/-- **R-6c-body-136 — the provider's `forest_left_inv`.** -/
theorem forest_left_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) (hq : q ∈ forestCarryingDomFinset G) :
    M.Reassembly.invConstruct
        (⟨(S.Forward.imageSupply G).selectedOuterOf q, S.quotientForest q⟩ : ForestBlockCodType D G)
      = q :=
  M.left_inv G q

/-- **R-6c-body-136 — the provider's `mixed_right_inv`.** -/
theorem mixed_right_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (r : ForestBlockCodType D G)
    (hr : r ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf (M.Reassembly.invConstruct r),
        S.quotientForest (M.Reassembly.invConstruct r)⟩ : ForestBlockCodType D G) = r :=
  M.right_inv G r

/-- **R-6c-body-136 — the provider's `forest_right_inv`.** -/
theorem forest_right_inv (M : ResolvedReassemblyInverseLawSupply D S) (G : ResolvedFeynmanGraph)
    (r : ForestBlockCodType D G)
    (hr : r ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    (⟨(S.Forward.imageSupply G).selectedOuterOf (M.Reassembly.invConstruct r),
        S.quotientForest (M.Reassembly.invConstruct r)⟩ : ForestBlockCodType D G) = r :=
  M.right_inv G r

end ResolvedReassemblyInverseLawSupply

end GaugeGeometry.QFT.Combinatorial
