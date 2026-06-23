import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocQuotientForest
import GaugeGeometry.QFT.HopfAlgebra.ResolvedActualSigmaCover

/-!
# R-6c-heart-3 — `quotientForestOf` body via the existing full-grain σ-cover

The quotient forest of a split choice lives over `(selectedOuterOf s).1.contractWithStars (D.starOf G
(selectedOuterOf s).1)`.  The existing resolved σ-cover already has the matching object:
`ResolvedFullQuotientForestImageData D` (`D : ResolvedSigmaCoverData G`) with
`.toImage : ResolvedAdmissibleSubgraph (D.Aout.contractWithStars D.starOf)` — the remnant ⊔ right-survivor
quotient forest.  Setting `Aout := (selectedOuterOf s).1` and `starOf := D.starOf G (selectedOuterOf s).1`
makes `toImage` land in EXACTLY the target type (definitionally), since `(selectedOuterOf s).1` is a value
the supply already provides (even while `selectedOuterOf` itself is still abstract).

So `quotientForestOf` reduces to two isolated, REUSABLE obligations:

1. a per-`s` `ResolvedSigmaCoverData G` built from `selectedOuterOf` (its `parents` + the three structural
   facts `containsAoutEdges` / `starFresh` / `componentPositiveEdges` about the selected outer forest and
   `D.starOf`);
2. a per-`s` `ResolvedFullQuotientForestImageData` over it (the genuine remnant/right de-contraction —
   which components of the contract graph form the quotient forest).

Then `quotientForestOf s := (fullQuotientOf s).toImage`, and `.toQuotientForestSupply` produces the
support-6 `ResolvedCoassocQuotientForestSupply`.  **Dependency recorded:** both obligations reference
`(selectedOuterOf s).1` only as a value, so they do NOT require `selectedOuterOf`'s *body* — they are
genuinely independent of the promote (heart-4); only the eventual *proofs* of the structural facts will
use whatever `selectedOuterOf` concretely is.

Landed:

* `ResolvedCoassocSigmaDataSupply D G S` (+ `.sigmaDataOf`) — the per-`s` `ResolvedSigmaCoverData` over
  the selected outer forest;
* `ResolvedCoassocFullQuotientSupply D G S Sig` (+ `.quotientForestOf`, `.toQuotientForestSupply`,
  `.forest_sat`) — the per-`s` full-grain quotient image, giving `quotientForestOf := toImage`.

No facade, no flat term, no `forgetHopf`; the SigmaCoverData structural facts and the
ResolvedFullQuotientForestImageData (the de-contraction) are the remaining work.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable {D : ResolvedCoproductProperForestData} {G : ResolvedFeynmanGraph}

/-- **R-6c-heart-3 — the per-split-choice σ-cover data over the selected outer forest.**  For each split
choice `s`, the `ResolvedSigmaCoverData G` with `Aout = (selectedOuterOf s).1` and `starOf = D.starOf G
(selectedOuterOf s).1` — its parents and the three structural facts (`containsAoutEdges` / `starFresh` /
`componentPositiveEdges`) as supply fields.  This packages the selected outer forest as a σ-cover so the
existing full-grain quotient machinery applies. -/
structure ResolvedCoassocSigmaDataSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (S : ResolvedCoassocSelectedOuterImageSupply D G) where
  /-- The parent set of the σ-cover over the selected outer forest. -/
  parentsOf : ResolvedCoassocSplitChoice D G → Finset (ResolvedFeynmanSubgraph G)
  /-- Each parent contains the selected outer forest's edges. -/
  containsAoutEdgesOf : ∀ s, ∀ γ ∈ parentsOf s,
    (S.selectedOuterOf s).1.internalEdges ≤ γ.internalEdges
  /-- The selected outer forest's stars are fresh (outside `G`). -/
  starFreshOf : ∀ s, ∀ η ∈ (S.selectedOuterOf s).1.elements,
    D.starOf G (S.selectedOuterOf s).1 η ∉ G.vertices
  /-- Each selected outer component has positive internal-edge count. -/
  componentPositiveEdgesOf : ∀ s, ∀ η ∈ (S.selectedOuterOf s).1.elements,
    0 < η.internalEdges.card

/-- The `ResolvedSigmaCoverData G` over the selected outer forest of a split choice (`Aout` / `starOf`
set definitionally from `selectedOuterOf`). -/
noncomputable def ResolvedCoassocSigmaDataSupply.sigmaDataOf
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    (Sig : ResolvedCoassocSigmaDataSupply D G S) (s : ResolvedCoassocSplitChoice D G) :
    ResolvedSigmaCoverData G where
  Aout := (S.selectedOuterOf s).1
  starOf := D.starOf G (S.selectedOuterOf s).1
  parents := Sig.parentsOf s
  containsAoutEdges := Sig.containsAoutEdgesOf s
  starFresh := Sig.starFreshOf s
  componentPositiveEdges := Sig.componentPositiveEdgesOf s

/-- **R-6c-heart-3 — the per-split-choice full-grain quotient image.**  For each split choice, a
`ResolvedFullQuotientForestImageData` over the selected-outer σ-cover data — the remnant ⊔ right-survivor
de-contraction.  This is the genuine quotient-forest geometry, isolated as a supply field. -/
structure ResolvedCoassocFullQuotientSupply (D : ResolvedCoproductProperForestData)
    (G : ResolvedFeynmanGraph) (S : ResolvedCoassocSelectedOuterImageSupply D G)
    (Sig : ResolvedCoassocSigmaDataSupply D G S) where
  /-- The full-grain quotient image (remnant ⊔ right survivors) of a split choice. -/
  fullQuotientOf : (s : ResolvedCoassocSplitChoice D G) →
    ResolvedFullQuotientForestImageData (Sig.sigmaDataOf s)

/-- **R-6c-heart-3 — the concrete quotient forest.**  `(fullQuotientOf s).toImage`, landing in the target
type `ResolvedAdmissibleSubgraph ((selectedOuterOf s).1.contractWithStars (D.starOf G (selectedOuterOf
s).1))` (the σ-cover data's `Aout`/`starOf` are definitionally the selected outer forest + its star). -/
noncomputable def ResolvedCoassocFullQuotientSupply.quotientForestOf
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    {Sig : ResolvedCoassocSigmaDataSupply D G S}
    (Full : ResolvedCoassocFullQuotientSupply D G S Sig)
    (s : ResolvedCoassocSplitChoice D G) :
    ResolvedAdmissibleSubgraph
      ((S.selectedOuterOf s).1.contractWithStars (D.starOf G (S.selectedOuterOf s).1)) :=
  (Full.fullQuotientOf s).toImage

/-- The support-6 `ResolvedCoassocQuotientForestSupply` from the full-grain quotient supply — so the
de-contraction quotient forest plugs straight into the image-side pipeline. -/
noncomputable def ResolvedCoassocFullQuotientSupply.toQuotientForestSupply
    {S : ResolvedCoassocSelectedOuterImageSupply D G}
    {Sig : ResolvedCoassocSigmaDataSupply D G S}
    (Full : ResolvedCoassocFullQuotientSupply D G S Sig) :
    ResolvedCoassocQuotientForestSupply D G S where
  quotientForestOf := Full.quotientForestOf

/- The forest discriminator witness (`ResolvedFullQuotientForestImageData.forest_sat`:
`resolvedIsForestByStar (Sig.sigmaDataOf s) (Full.fullQuotientOf s).toImage`) is available per `s` and
will feed `discriminatorOf` in the heart-6 cover step (where the divergence-preservation instances are in
scope); it is not re-exported here to keep this body file instance-light. -/

end GaugeGeometry.QFT.Combinatorial
