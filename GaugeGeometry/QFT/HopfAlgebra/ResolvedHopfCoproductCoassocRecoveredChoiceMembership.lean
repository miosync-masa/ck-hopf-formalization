import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingInvMem

/-!
# R-6c-body-151 — recovered choice carrier membership: the `invFun_mem` `p`-tags from the choice structure

Hundred-and-fifty-first genuine-body step, the `invFun_mem` twin of body-150.  Body-133's two `p`-tag facts (the
backward-membership classifiers) are reduced to the choice structure: the `forestChoiceCarrier` membership of the
reconstructed choice is `piCarrier` membership (**always true**) plus non-extremality (`≠ p_R`, `≠ p_L`).  The
**forest** side is proved outright from the `inr` witness; the **mixed** side reduces to the primitive-mixture
nontriviality.

## The membership mechanics (generic, PROVED)

`forestChoiceCarrier A = piCarrier A |>.filter (· ≠ p_R ∧ · ≠ p_L)` with `p_R = fun _ _ => inl false`,
`p_L = fun _ _ => inl true` (body-94), and `localChoiceCarrier γ = (univ : Finset Bool).disjSum forestCarrier`.  So:

* `choice_mem_piCarrier` — **every** choice `p` lies in `piCarrier`: each value is `inl b` (`b ∈ univ`) or `inr B`
  (`B : {A // A ∈ carrier}`, so `B ∈ forestCarrier = carrier.attach`); PROVED via `Finset.mem_pi` +
  `Finset.mem_disjSum` + `mem_univ` / `mem_attach`;
* `ne_pR_pL_of_isForestCarrying` — a forest-carrying choice (`∃` component `inr`) is neither `p_R` nor `p_L` (an
  `inr` value cannot be `inl false` / `inl true`); PROVED;
* `mem_forestChoiceCarrier_of_ne` — `piCarrier` membership + `≠ p_R` + `≠ p_L` gives `forestChoiceCarrier`
  membership (`Finset.mem_filter`); PROVED;
* `mem_forestChoiceCarrier_of_isForestCarrying` — a forest-carrying choice is in `forestChoiceCarrier` (combines
  the three); PROVED.

## The supply

`ResolvedRecoveredChoiceMembershipSupply D S invConstruct` fields the branch tags (`forest_tag` / `mixed_tag`, the
`isForestCarryingChoice` / `¬` facts — body-143/142 for `witnessSplit`) and the **mixed** non-extremality
(`mixed_ne_pR` / `mixed_ne_pL`, the primitive-mixture nontriviality of the reconstructed mixed choice).  From these,
`.toOuterMixingInvMemSupply` produces body-133's `ResolvedOuterMixingInvMemSupply`:

* `forest_inv_tag` — `⟨mem_forestChoiceCarrier_of_isForestCarrying forest_tag, forest_tag⟩` (fully from the `inr`
  witness);
* `mixed_inv_tag` — `⟨mem_forestChoiceCarrier_of_ne choice_mem_piCarrier mixed_ne_pR mixed_ne_pL, mixed_tag⟩`.

So the forest `invFun_mem` is proved outright, and the mixed one reduces to the two non-extremality facts — the
primitive-mixture nontriviality of the reconstructed choice.  Combined with body-132/150 (the `toFun_mem` star
facts), all four membership fields of the bijection provider are now local classifier facts.

Per the HALT: the forest side is proved from the `inr` witness; the mixed non-extremality is fielded
(`mixed_ne_pR` / `mixed_ne_pL`); no round-trip content is entered.

Landed:

* `choice_mem_piCarrier` / `ne_pR_pL_of_isForestCarrying` / `mem_forestChoiceCarrier_of_ne` /
  `mem_forestChoiceCarrier_of_isForestCarrying` — the generic membership lemmas (PROVED);
* `ResolvedRecoveredChoiceMembershipSupply D S invConstruct` — branch tags + mixed non-extremality;
* `.toOuterMixingInvMemSupply` — body-133's invFun-membership supply (→ the two `invFun_mem` fields).

Toolkit body (like body-150).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-151 — every choice lies in `piCarrier`.**  Each component value is `inl b` (`b ∈ univ`) or `inr B`
(`B ∈ forestCarrier = carrier.attach`). -/
theorem choice_mem_piCarrier (A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G})
    (p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx) :
    p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)) := by
  rw [Finset.mem_pi]
  intro γ hγ
  rw [ResolvedCoproductProperForestData.localChoiceCarrier, Finset.mem_disjSum]
  cases hpc : p γ hγ with
  | inl b => exact Or.inl ⟨b, Finset.mem_univ _, rfl⟩
  | inr B => exact Or.inr ⟨B, Finset.mem_attach _ _, rfl⟩

/-- **R-6c-body-151 — a forest-carrying choice is non-extremal** (`≠ p_R` and `≠ p_L`).  An `inr` value is neither
`inl false` nor `inl true`. -/
theorem ne_pR_pL_of_isForestCarrying {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (h : isForestCarryingChoice A p) :
    p ≠ (fun _ _ => Sum.inl false) ∧ p ≠ (fun _ _ => Sum.inl true) := by
  obtain ⟨γ, hγ, b, hb⟩ := h
  refine ⟨fun heq => ?_, fun heq => ?_⟩
  · exact Sum.inl_ne_inr ((congrFun (congrFun heq γ) hγ).symm.trans hb)
  · exact Sum.inl_ne_inr ((congrFun (congrFun heq γ) hγ).symm.trans hb)

/-- **R-6c-body-151 — `forestChoiceCarrier` membership from non-extremality.** -/
theorem mem_forestChoiceCarrier_of_ne {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (hpi : p ∈ (A.1.elements.attach).pi (fun γ => D.localChoiceCarrier (γ.1.toResolvedFeynmanGraph)))
    (hR : p ≠ (fun _ _ => Sum.inl false)) (hL : p ≠ (fun _ _ => Sum.inl true)) :
    p ∈ forestChoiceCarrier A := by
  rw [forestChoiceCarrier, Finset.mem_filter]
  exact ⟨hpi, hR, hL⟩

/-- **R-6c-body-151 — a forest-carrying choice is in `forestChoiceCarrier`.** -/
theorem mem_forestChoiceCarrier_of_isForestCarrying
    {A : {A : ResolvedAdmissibleSubgraph G // A ∈ D.carrier G}}
    {p : ∀ γ ∈ A.1.elements.attach, Bool ⊕ (D.supply (γ.1.toResolvedFeynmanGraph)).ForestIdx}
    (h : isForestCarryingChoice A p) : p ∈ forestChoiceCarrier A :=
  mem_forestChoiceCarrier_of_ne (choice_mem_piCarrier A p)
    (ne_pR_pL_of_isForestCarrying h).1 (ne_pR_pL_of_isForestCarrying h).2

/-- **R-6c-body-151 — the recovered-choice membership supply.**  The branch tags (forest / mixed
`isForestCarryingChoice` facts) plus the mixed non-extremality, against a fixed summand bundle `S` and backward
map `invConstruct`. -/
structure ResolvedRecoveredChoiceMembershipSupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D)
    (invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G) where
  /-- A forest codomain forest reconstructs to a forest-carrying choice (body-143). -/
  forest_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ forestCarryingCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    isForestCarryingChoice (invConstruct G z).1 (invConstruct G z).2
  /-- A mixed codomain forest reconstructs to a non-forest-carrying choice (body-142). -/
  mixed_tag : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    ¬ isForestCarryingChoice (invConstruct G z).1 (invConstruct G z).2
  /-- The reconstructed mixed choice is not all-right (`≠ p_R`) — primitive-mixture nontriviality. -/
  mixed_ne_pR : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (invConstruct G z).2 ≠ (fun _ _ => Sum.inl false)
  /-- The reconstructed mixed choice is not all-left (`≠ p_L`). -/
  mixed_ne_pL : ∀ {G : ResolvedFeynmanGraph} (z : ForestBlockCodType D G)
    (hz : z ∈ mixedCodFinset (D := D) (fun {G} A B => resolvedIsForestImage A B) G),
    (invConstruct G z).2 ≠ (fun _ _ => Sum.inl true)

/-- **R-6c-body-151 — body-133's invFun-membership supply from the recovered-choice membership.**  Forest side
proved outright from the `inr` witness; mixed side from the two non-extremality facts. -/
def ResolvedRecoveredChoiceMembershipSupply.toOuterMixingInvMemSupply
    {S : ResolvedConcreteSummandBundleSupply D}
    {invConstruct : ∀ (G : ResolvedFeynmanGraph), ForestBlockCodType D G → ForestBlockDomType D G}
    (R : ResolvedRecoveredChoiceMembershipSupply D S invConstruct) :
    ResolvedOuterMixingInvMemSupply D S invConstruct where
  mixed_inv_tag := fun {G} z hz =>
    ⟨mem_forestChoiceCarrier_of_ne (choice_mem_piCarrier _ _) (R.mixed_ne_pR z hz) (R.mixed_ne_pL z hz),
      R.mixed_tag z hz⟩
  forest_inv_tag := fun {G} z hz =>
    ⟨mem_forestChoiceCarrier_of_isForestCarrying (R.forest_tag z hz), R.forest_tag z hz⟩

end GaugeGeometry.QFT.Combinatorial
