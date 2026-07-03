import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRegroupReindexBody

/-!
# R-6c-body-50 — the outer double-sum reindex interface to the R-4-full H5.8 machinery

Fiftieth genuine-body step, an INTERFACE scout fixing how body-38's `image_cover_reindex` /
`branch_cover_reindex` connect to the landed R-4-full reindex engines, and the exact adapter list.

## The R-4-full reindex engines (`ResolvedActualSigmaCover` / `ResolvedH58Reindex`)

* **`ResolvedFiniteBranchMapLayer.sum_reindex (FL) (w) : ∑ z ∈ FL.imageCarrier, w z = ∑ q ∈ FL.forestCarrier,
  w (FL.layer.forestImage q) + ∑ q ∈ FL.mixedCarrier, w (FL.layer.mixedImage q)`** — the abstract PARTITION
  reindex (image cover = forest ⊕ mixed cover), PROVED (`imageCarrier_eq` + `disjoint_images` + `sum_image`).
* **`ResolvedActualSigmaCoverSupply.concrete_sum_reindex (S) : ∑ z ∈ FL.imageCarrier, quotientTerm (flatImageOf
  z) = ∑ q ∈ FL.forestCarrier, splitChoiceTerm (forestSplitOf q) + ∑ q ∈ FL.mixedCarrier, splitChoiceTerm
  (mixedSplitOf q)`** — the concrete partition (image-weight = split-term over the σ-cover), for a `g`.
* **`ResolvedH58FullGrainOuterSkeleton.outer_sum_reindex (Sk) : ∑ A ∈ h58BridgeOuterCarrier g, innerImageSum A =
  ∑ A ∈ h58BridgeOuterCarrier g, innerBranchSum A`** — the OUTER H5.8 (outer forest sum of inner image = inner
  branch).

## The gap: carrier and weight identification

Body-38's two reindexes connect the **outer forest carrier** `(D.supply (repGraph x)).forestCarrier` (proper
forests `A`) to the **splitPhi finite cover** `(grand x).toFiniteData.{image,forest,mixed}Carrier`.  R-4-full's
engines use `h58BridgeOuterCarrier g` (outer) and `S.toActualSigmaCover.FL` (σ-cover) — DIFFERENT carriers of
DIFFERENT constructions.  So the engines do NOT apply verbatim; the exact adapter list to bridge them is:

1. **outer carrier identification** — `(D.supply (repGraph x)).forestCarrier` ↔ `h58BridgeOuterCarrier` at the
   representative (the resolved outer forest carrier is the σ-cover's outer carrier);
2. **cover identification** — `(grand x).toFiniteData.{image,forest,mixed}Carrier` ↔ a per-representative
   `ResolvedFiniteBranchMapLayer` (`FL`) built from the GrandFull cover (body-39's `cross` disjointness is the
   one non-fielded `layer` ingredient);
3. **weight identification** — `(grand x).toFiniteData.imageWeight` ↔ `quotientTerm ∘ flatImageOf`;
   `D.resolvedSplitChoiceTerm` ↔ `splitChoiceTerm ∘ splitOf`;
4. **summand identification** — the outer image / branch summands (body-38, from `regroupImageSum_eq_outerSum`)
   ↔ `innerImageSum` / `innerBranchSum` of the outer skeleton.

Given (1)–(4), `image_cover_reindex` and `branch_cover_reindex` are `concrete_sum_reindex` +
`outer_sum_reindex` re-carriered — no new double-sum bijection.  This file packages body-38's reindexes as the
named `H5.8 σ-cover reindex at the representative` interface, so the remaining work is precisely the (1)–(4)
carrier/weight wiring (a per-`x` `ResolvedActualSigmaCoverSupply` built from the grand data), not fresh
combinatorics.

Per the HALT, no double-sum bijection is entered; the σ-cover is not built here — the adapter list is fixed and
the two reindexes are surfaced as the interface.

Landed:

* `ResolvedOuterReindexInterfaceSupply D` — the representative data + the two σ-cover reindex interface leaves;
* `.toRegroupReindexSupply` — body-38's `ResolvedRegroupReindexSupply` (whence `coassoc_gen`).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData}

/-- **R-6c-body-50 — the outer reindex interface supply.**  The representative data (as in body-38) plus the
two σ-cover reindex leaves stated in the outer-forest / splitPhi-cover coordinates — the interface to the
R-4-full `concrete_sum_reindex` / `outer_sum_reindex` engines (via the (1)–(4) carrier/weight adapters). -/
structure ResolvedOuterReindexInterfaceSupply (D : ResolvedCoproductProperForestData) where
  /-- A representative resolved graph for each generator. -/
  repGraph : ResolvedHopfGen → ResolvedFeynmanGraph
  /-- The representative is connected-divergent. -/
  repCD : ∀ x : ResolvedHopfGen, (repGraph x).forget.toClass.IsConnectedDivergent
  /-- The representative's class IS the generator. -/
  rep_eq : ∀ x : ResolvedHopfGen, x = (repGraph x).toResolvedHopfGen (repCD x)
  /-- The per-`G` grand full supply at each representative. -/
  grand : ∀ x : ResolvedHopfGen, ResolvedCoassocGrandFullSupply D (repGraph x)
  /-- **Image σ-cover reindex** (outer-forest image sum = cover image-weight sum). -/
  image_cover_reindex : ∀ x : ResolvedHopfGen,
    (∑ A ∈ (D.supply (repGraph x)).forestCarrier,
        ((1 : ResolvedHopfH) ⊗ₜ[ℚ]
            ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)
          + D.coassocRightTail
              ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)))
      = ∑ z ∈ (grand x).toFiniteData.imageCarrier, (grand x).toFiniteData.imageWeight z
  /-- **Branch σ-cover reindex** (cover (forest + mixed) term sum = outer-forest branch sum). -/
  branch_cover_reindex : ∀ x : ResolvedHopfGen,
    (∑ q ∈ (grand x).toFiniteData.forestCarrier, D.resolvedSplitChoiceTerm q.1)
      + (∑ q ∈ (grand x).toFiniteData.mixedCarrier, D.resolvedSplitChoiceTerm q.1)
      = ∑ A ∈ (D.supply (repGraph x)).forestCarrier,
          ((Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom
              (((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A)
                ⊗ₜ[ℚ] (1 : ResolvedHopfH))
            + D.coassocLeftTail
                ((D.supply (repGraph x)).leftTerm A ⊗ₜ[ℚ] (D.supply (repGraph x)).rightTerm A))

/-- **R-6c-body-50 — body-38's regroup reindex supply from the interface** (identity wiring; the reindex
leaves are exactly body-38's). -/
def ResolvedOuterReindexInterfaceSupply.toRegroupReindexSupply
    (F : ResolvedOuterReindexInterfaceSupply D) :
    ResolvedRegroupReindexSupply D where
  repGraph := F.repGraph
  repCD := F.repCD
  rep_eq := F.rep_eq
  grand := F.grand
  image_cover_reindex := F.image_cover_reindex
  branch_cover_reindex := F.branch_cover_reindex

/-- **R-6c-body-50 — the capstone from the outer reindex interface. -/
theorem ResolvedOuterReindexInterfaceSupply.coassoc_gen
    (F : ResolvedOuterReindexInterfaceSupply D) (x : ResolvedHopfGen) :
    D.coassocLeft (MvPolynomial.X x) = D.coassocRight (MvPolynomial.X x) :=
  F.toRegroupReindexSupply.coassoc_gen x

end GaugeGeometry.QFT.Combinatorial
