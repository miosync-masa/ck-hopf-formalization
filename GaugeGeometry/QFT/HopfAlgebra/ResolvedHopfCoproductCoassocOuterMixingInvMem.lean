import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocBijectionProvider

/-!
# R-6c-body-133 — outer-mixing invFun membership: `invFun_mem` reduced to the reconstructed `p`-tag

Hundred-and-thirty-third genuine-body step, the domain-side twin of body-132.  The two backward-membership fields
`mixed_invFun_mem` / `forest_invFun_mem` (body-131) are pure `Finset.sigma` plumbing over the DOMAIN carriers, and
they reduce to EXACTLY the reconstructed choice's tag: `invConstruct z`'s choice `p` must be a non-extreme
(`≠ p_R`, `≠ p_L`) choice that is mixed-boundary (mixed case) resp. forest-carrying (forest case).

## The reduction (PROVED)

`mixedDomFinset` / `forestCarryingDomFinset` are `(D.carrier G).attach.sigma (fun A => (forestChoiceCarrier A).filter …)`;
the reconstructed `q = invConstruct z` always has `q.1 ∈ (D.carrier G).attach`, so `Finset.mem_sigma` +
`Finset.mem_filter` collapse the membership to the two filter conditions — the `forestChoiceCarrier` membership of
`q.2` and the class tag:

* `mixed_invFun_mem_of_tag`: from `q.2 ∈ forestChoiceCarrier q.1` and `¬ isForestCarryingChoice q.1 q.2`;
* `forest_invFun_mem_of_tag`: from `q.2 ∈ forestChoiceCarrier q.1` and `isForestCarryingChoice q.1 q.2`.

`forestChoiceCarrier A := (attach.pi localChoiceCarrier).filter (· ≠ p_R ∧ · ≠ p_L)` with `p_R = fun _ _ =>
inl false` (all-right), `p_L = fun _ _ => inl true` (all-left) — the non-extreme choices (body-94).

## The two `p`-tag facts (fielded)

The genuine content is the two reconstruction facts — that `invConstruct` sends a mixed (star-avoiding) codomain
forest to a non-extreme mixed-boundary choice, and a forest-image (star-touching) one to a non-extreme
forest-carrying choice.  These are properties of the (still-abstract) `invConstruct` reassembly, so they are
exposed as `ResolvedOuterMixingInvMemSupply` fields (each bundling the `forestChoiceCarrier` membership with the
class tag).  They are the domain-side counterparts of body-132's forward star facts, and both hang off the same
`invConstruct` reassembly leaf.

`.toMixedInvFunMem` / `.toForestInvFunMem` fill the provider's two `invFun_mem` fields; with body-132, all FOUR
membership fields of the bijection provider are now plumbing over fielded classifier / tag facts.

Per the HALT: `invConstruct` is not constructed; the two `invFun_mem` are reduced to the reconstructed `p`-tag
(`forestChoiceCarrier` membership + `isForestCarryingChoice`); the tag facts are exposed as exact fields.

Landed:

* `mixed_invFun_mem_of_tag` / `forest_invFun_mem_of_tag` — the `Finset.sigma` reduction to the `p`-tag;
* `ResolvedOuterMixingInvMemSupply D S invConstruct` — the two reconstructed `p`-tag facts;
* `.toMixedInvFunMem` / `.toForestInvFunMem` — the provider's two `invFun_mem` fields.

Toolkit body (like body-132), one small supply.  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-133 — mixed `invFun_mem` from the reconstructed tag.**  The `Finset.sigma` domain membership
collapses to the `forestChoiceCarrier` membership plus the mixed-boundary tag. -/
theorem mixed_invFun_mem_of_tag (q : ForestBlockDomType D G)
    (hmem : q.2 ∈ forestChoiceCarrier q.1)
    (htag : ¬ isForestCarryingChoice q.1 q.2) :
    q ∈ mixedDomFinset G := by
  rw [mixedDomFinset, Finset.mem_sigma]
  exact ⟨Finset.mem_attach _ _, Finset.mem_filter.mpr ⟨hmem, htag⟩⟩

/-- **R-6c-body-133 — forest `invFun_mem` from the reconstructed tag.**  The `Finset.sigma` domain membership
collapses to the `forestChoiceCarrier` membership plus the forest-carrying tag. -/
theorem forest_invFun_mem_of_tag (q : ForestBlockDomType D G)
    (hmem : q.2 ∈ forestChoiceCarrier q.1)
    (htag : isForestCarryingChoice q.1 q.2) :
    q ∈ forestCarryingDomFinset G := by
  rw [forestCarryingDomFinset, Finset.mem_sigma]
  exact ⟨Finset.mem_attach _ _, Finset.mem_filter.mpr ⟨hmem, htag⟩⟩

/-- **R-6c-body-133 — the outer-mixing invFun-membership supply.**  The two reconstruction `p`-tag facts against a
fixed summand bundle `S` and a backward map `invConstruct`: `invConstruct` sends a mixed codomain forest to a
non-extreme mixed-boundary choice and a forest-image one to a non-extreme forest-carrying choice. -/
structure ResolvedOuterMixingInvMemSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D)
    (invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G) where
  /-- A mixed (star-avoiding) codomain forest reconstructs to a non-extreme mixed-boundary choice. -/
  mixed_inv_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (invConstruct G z).2 ∈ forestChoiceCarrier (invConstruct G z).1
      ∧ ¬ isForestCarryingChoice (invConstruct G z).1 (invConstruct G z).2
  /-- A forest-image (star-touching) codomain forest reconstructs to a non-extreme forest-carrying choice. -/
  forest_inv_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (invConstruct G z).2 ∈ forestChoiceCarrier (invConstruct G z).1
      ∧ isForestCarryingChoice (invConstruct G z).1 (invConstruct G z).2

/-- **R-6c-body-133 — the provider's mixed `invFun_mem` from the invMem supply.** -/
theorem ResolvedOuterMixingInvMemSupply.toMixedInvFunMem {S : ResolvedConcreteSummandBundleSupply D}
    {invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G}
    (M : ResolvedOuterMixingInvMemSupply D S invConstruct) (G : ResolvedFeynmanGraph)
    (z : ForestBlockCodType D G)
    (hz : z ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    invConstruct G z ∈ mixedDomFinset G :=
  mixed_invFun_mem_of_tag (invConstruct G z) (M.mixed_inv_tag z hz).1 (M.mixed_inv_tag z hz).2

/-- **R-6c-body-133 — the provider's forest `invFun_mem` from the invMem supply.** -/
theorem ResolvedOuterMixingInvMemSupply.toForestInvFunMem {S : ResolvedConcreteSummandBundleSupply D}
    {invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G}
    (M : ResolvedOuterMixingInvMemSupply D S invConstruct) (G : ResolvedFeynmanGraph)
    (z : ForestBlockCodType D G)
    (hz : z ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G) :
    invConstruct G z ∈ forestCarryingDomFinset G :=
  forest_invFun_mem_of_tag (invConstruct G z) (M.forest_inv_tag z hz).1 (M.forest_inv_tag z hz).2

end GaugeGeometry.QFT.Combinatorial
