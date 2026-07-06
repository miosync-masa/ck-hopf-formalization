import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocRoundTripHEqScout

/-!
# R-6c-body-193 — backward-choice HEq assembly: the `HEq` from a componentwise `Eq`

Hundred-and-ninety-third genuine-body step, assembling body-164's `backward_choice_heq` from the componentwise
`Eq` isolated in body-192.  This body contains only the dependent-type transport — no tag or de-contraction
content — so it discharges the `HEq` wrapper once and for all, leaving the honest componentwise leaf.

## The transport helper (PROVED)

`heq_of_index_eq` is the reusable dependent-function transport: two choice functions over *equal* index Finsets
that agree pointwise are heterogeneously equal.

```text
heq_of_index_eq :
  (A = B) →
  (∀ x (ha : x ∈ A) (hb : x ∈ B), f ⟨x,ha⟩ (mem_attach) = g ⟨x,hb⟩ (mem_attach)) →
  HEq f g
```

where `f : (γ : {x // x ∈ A}) → γ ∈ A.attach → T γ.1` and `g` the analogue over `B`.  Proof: `subst` the index
equality (aligning the two dependent-function types), `heq_of_eq`, then `funext` — the flat-`Coassoc` pattern
(`Coassoc.lean:9448-9455`) as a clean Resolved-namespace lemma (there was no such helper).  The inner `mem_attach`
argument is proof-irrelevant, so `funext γ hγ; exact hfg γ.1 γ.2 γ.2` closes it.

## The assembly (PROVED)

`ResolvedBackwardChoiceHEqAssemblySupply D S Region` fields the index transport (`outer_partition`, body-160's
`recoveredOuter_partition`) and the componentwise `Eq` (`choice_component_eq`, body-192).  Then
`.backward_choice_heq` is **proved** by `heq_of_index_eq` with `A := (unionOuter (fwdMap q)).1.elements`,
`B := q.1.1.elements`, `f := recoverChoice (fwdMap q)`, `g := q.2`:

```text
HEq (recoverChoice (fwdMap q)) q.2
```

which is exactly body-164's leaf.  `.toRecoveredChoiceRoundTripSupply` produces body-164's supply, so the
backward-choice round-trip is no longer fielded as an `HEq`: it is the componentwise `Eq` + the (already proved)
outer partition, wrapped by the transport.

## Consequence

The backward-choice residual is now the single homogeneous componentwise `Eq` `choice_component_eq` (whose only
fresh point is the `inr` value match, body-192) and the proved `outer_partition`.  The `HEq` type mismatch is
retired.  `forward_quotient_heq` (the heavier leaf) is untouched.

Per the HALT: `choice_component_eq`'s tag content is not entered; `forward_quotient_heq` is untouched; this body is
the `HEq` transport only.

Landed:

* `heq_of_index_eq` — the reusable dependent-function transport (PROVED);
* `ResolvedBackwardChoiceHEqAssemblySupply D S Region` — the outer partition + the componentwise `Eq`;
* `.backward_choice_heq` — body-164's leaf (PROVED from the componentwise `Eq`);
* `.toRecoveredChoiceRoundTripSupply` — body-164's supply.

Toolkit body (like body-181).  No facade, no flat term, no `forgetHopf`.
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

/-- **R-6c-body-193 — the dependent-function index transport.**  Two choice functions over equal index Finsets
that agree pointwise are heterogeneously equal.  `subst` the index equality, then `heq_of_eq` + `funext` (the inner
`mem_attach` argument is proof-irrelevant). -/
theorem heq_of_index_eq {G : ResolvedFeynmanGraph}
    {A B : Finset (ResolvedFeynmanSubgraph G)}
    {T : ResolvedFeynmanSubgraph G → Type}
    {f : (γ : {x // x ∈ A}) → γ ∈ A.attach → T γ.1}
    {g : (γ : {x // x ∈ B}) → γ ∈ B.attach → T γ.1}
    (he : A = B)
    (hfg : ∀ (x : ResolvedFeynmanSubgraph G) (ha : x ∈ A) (hb : x ∈ B),
      f ⟨x, ha⟩ (Finset.mem_attach _ _) = g ⟨x, hb⟩ (Finset.mem_attach _ _)) :
    HEq f g := by
  subst he
  apply heq_of_eq
  funext γ hγ
  exact hfg γ.1 γ.2 γ.2

/-- **R-6c-body-193 — the backward-choice HEq assembly supply.**  The index transport `outer_partition` (body-160's
`recoveredOuter_partition`) and the componentwise `Eq` `choice_component_eq` (body-192). -/
structure ResolvedBackwardChoiceHEqAssemblySupply (D : ResolvedCoproductProperForestData)
    (S : ResolvedConcreteSummandBundleSupply D) (Region : ResolvedRegionChoiceRoundTripSupply D S) where
  /-- Body-160's backward-outer element partition (the index transport). -/
  outer_partition : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G),
    (Region.Union.unionOuter (fwdMap S q)).1.elements = q.1.1.elements
  /-- Body-192's componentwise choice agreement (homogeneous). -/
  choice_component_eq : ∀ {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G)
    (γ : {x : ResolvedFeynmanSubgraph G // x ∈ q.1.1.elements})
    (hu : γ.1 ∈ (Region.Union.unionOuter (fwdMap S q)).1.elements),
    Region.recoverChoice (fwdMap S q) ⟨γ.1, hu⟩ (Finset.mem_attach _ _)
      = q.2 γ (Finset.mem_attach _ _)

namespace ResolvedBackwardChoiceHEqAssemblySupply

variable {S : ResolvedConcreteSummandBundleSupply D} {Region : ResolvedRegionChoiceRoundTripSupply D S}

/-- **R-6c-body-193 — body-164's `backward_choice_heq` from the componentwise `Eq`.** -/
theorem backward_choice_heq (P : ResolvedBackwardChoiceHEqAssemblySupply D S Region)
    {G : ResolvedFeynmanGraph} (q : ForestBlockDomType D G) :
    HEq (Region.recoverChoice (fwdMap S q)) q.2 :=
  heq_of_index_eq (T := fun x => Bool ⊕ (D.supply (x.toResolvedFeynmanGraph)).ForestIdx)
    (f := Region.recoverChoice (fwdMap S q)) (g := q.2) (P.outer_partition q)
    (fun x ha hb => P.choice_component_eq q ⟨x, hb⟩ ha)

/-- **R-6c-body-193 — body-164's recovered-choice round-trip supply from the assembly.** -/
def toRecoveredChoiceRoundTripSupply (P : ResolvedBackwardChoiceHEqAssemblySupply D S Region) :
    ResolvedRecoveredChoiceRoundTripSupply D S Region where
  backward_choice_heq := fun {G} q => P.backward_choice_heq q

end ResolvedBackwardChoiceHEqAssemblySupply

end GaugeGeometry.QFT.Combinatorial
