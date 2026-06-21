import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassoc
import GaugeGeometry.QFT.HopfAlgebra.ResolvedH58Weight

/-!
# R-6c-2a — the resolved-term H5.8 reindex spine (per-outer `resolvedTermAgreement`)

The first of the three frontier obligations (`ResolvedCoproductH58Compatibility`): the **per-outer
reindex** `innerImageSum A = innerBranchSum A`, entirely in resolved terms (`ResolvedHopfH3`).

The decisive observation: the abstract H5.8 reindex spine built in R-4-superfull
(`ResolvedCarrierFiniteBranchMapLayer.sum_reindex` and `ResolvedH58WeightData.sum_reindex`) is
**generic in the value type** `Target` and proved by pure `Finset` combinatorics (a cover partition
into disjoint forest/mixed branch images + `Finset.sum_image` with carrier injectivity), using only
`FL.sep.cross`.  No flat `HopfH` term, no facade, no gated theorem enters.  So the resolved replay of
the reindex spine is *immediate* at `Target := ResolvedHopfH3`: this file specialises the generic
spine to the resolved triple-tensor and packages it as the per-outer reindex datum.

This is the **native replay**, not a flat plug-in: the terms live in `ResolvedHopfH3`, the value type
is the resolved-generator algebra throughout.  The genuinely new id-bearing content — *constructing*
the cover layer `FL` and the resolved weights from resolved generators — is the geometry of R-6c-2b/c
(the iterated-coproduct expansions) and the concrete σ-cover; the reindex *spine* itself is shared
and facade-free, which is exactly why building it generic in R-4-superfull paid off.

Landed:

* `ResolvedH58TermReindex` — a per-outer reindex datum: a finite cover layer
  `FL : ResolvedCarrierFiniteBranchMapLayer` together with resolved-term weights
  `W : ResolvedH58WeightData FL ResolvedHopfH3`;
* `ResolvedH58TermReindex.imageSum` / `.branchSum` — the image-side and (forest + mixed)
  branch-side resolved sums in `ResolvedHopfH3`;
* `ResolvedH58TermReindex.reindex` — the **per-outer reindex** `imageSum = branchSum`, the resolved
  analogue of the flat `concrete_sum_reindex`, facade-free (just `W.sum_reindex`);
* `resolvedTermAgreement_ofTermReindex` — the bridge: a family of per-outer reindex data discharges
  the `resolvedTermAgreement` field of `ResolvedCoproductH58Compatibility`.

No `coassocLeft`/`coassocRight` expansion yet (R-6c-2b/c), no flat term theorem, no `forgetHopf`, no
flat `splitPhiBranchReindexing`, no facade.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

/-- **R-6c-2a — a resolved-term H5.8 reindex datum for one outer forest.**  A finite cover layer
(`ResolvedCarrierFiniteBranchMapLayer`: forest/mixed/image carriers with cover + carrier injectivity)
together with resolved-term weights valued in `ResolvedHopfH3` (the image weight and the forest/mixed
branch weights, the latter agreeing with the image weight along the branch maps).  This is the
graph-free, value-generic spine of the flat σ-cover specialised to the resolved triple tensor. -/
structure ResolvedH58TermReindex where
  /-- The finite cover layer (forest/mixed/image carriers, cover, injectivity). -/
  FL : ResolvedCarrierFiniteBranchMapLayer
  /-- The resolved-term weights (image + forest/mixed branch, with branch agreements). -/
  W : ResolvedH58WeightData FL ResolvedHopfH3

namespace ResolvedH58TermReindex

variable (R : ResolvedH58TermReindex)

/-- The image-side resolved sum: the quotient (image) weight summed over the image carrier. -/
noncomputable def imageSum : ResolvedHopfH3 :=
  ∑ z ∈ R.FL.imageCarrier, R.W.imageWeight z

/-- The branch-side resolved sum: the forest branch weights plus the mixed branch weights. -/
noncomputable def branchSum : ResolvedHopfH3 :=
  (∑ q ∈ R.FL.forestCarrier, R.W.forestWeight q) +
    (∑ q ∈ R.FL.mixedCarrier, R.W.mixedWeight q)

/-- **R-6c-2a — the per-outer resolved-term H5.8 reindex.**  The image-side sum equals the
branch-side sum, in `ResolvedHopfH3`.  This is the resolved analogue of the flat
`concrete_sum_reindex`; its proof is the value-generic `ResolvedH58WeightData.sum_reindex`, i.e. the
pure `Finset` cover bijection — facade-free, no flat term, no gated theorem. -/
theorem reindex : R.imageSum = R.branchSum :=
  R.W.sum_reindex

end ResolvedH58TermReindex

/-- **R-6c-2a — the reindex datum discharges `resolvedTermAgreement`.**  Given a family of per-outer
resolved-term reindex data, whose `imageSum`/`branchSum` are the compatibility's inner sums, the
per-outer agreement `innerImageSum A = innerBranchSum A` holds by the reindex spine.  This is the
field `ResolvedCoproductH58Compatibility.resolvedTermAgreement`, ready to be slotted in when the
concrete compatibility is assembled (R-6c-2d). -/
theorem resolvedTermAgreement_ofTermReindex
    {OuterIdx : ResolvedHopfGen → Type}
    (data : (x : ResolvedHopfGen) → OuterIdx x → ResolvedH58TermReindex)
    (x : ResolvedHopfGen) (A : OuterIdx x) :
    (data x A).imageSum = (data x A).branchSum :=
  (data x A).reindex

end GaugeGeometry.QFT.Combinatorial
