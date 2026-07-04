import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocOuterMixingAssembly
import GaugeGeometry.QFT.HopfAlgebra.ResolvedAdmissibleSubgraphOfElements

/-!
# R-6c-body-115 — right-factor union instantiation: `quotientRaw = rightSurvivor ∪ remnant` PROVED from a star filter

Hundred-and-fifteenth genuine-body step, instantiating the assembly's RIGHT-factor union block (body-113) from
the star-filter structure of the quotient forest.  The quotient forest `B = quotientForestOf q` splits into its
star-AVOIDING components (right survivors) and its star-TOUCHING components (remnant) — a `filterElements`
partition — and the union / disjoint / cross facts are PROVED here (the resolved analogue of the Codomain
leaf-15 `filter_union_filter_not_eq` / `disjoint_filter_filter_not`).  Only the two factor products remain.

## The star filter (PROVED union / disjoint / cross)

With a residual-star predicate `starPred` on the quotient forest's components:

* `rightSurvivor q := quotientRaw q |>.filterElements (¬ starPred)` — the star-avoiding components;
* `remnant q := quotientRaw q |>.filterElements starPred` — the star-touching components;
* `right_union_eq`: `quotientRaw q = rightSurvivor q ∪ remnant q` — PROVED via `admissible_ext_elements`
  (`ResolvedAdmissibleSubgraph` is determined by `elements`) + `Finset.filter_union_filter_neg_eq`;
* `right_hdisj`: `Disjoint rightSurvivor.elements remnant.elements` — PROVED via `disjoint_filter_filter_not`;
* `right_hcross`: the cross-disjointness — PROVED from the quotient forest's own `pairwiseDisjoint` (both
  filtered sets sit inside `quotientRaw.elements`).

So the whole geometric union block is discharged; only the two factor products (`right_primitive_factor` /
`remnant_factor`) — the per-component agreement of `∏ localRightFactor` with `leftTerm rightSurvivor` /
`leftTerm remnant` — remain, isolated as fields.

## The named helper

`admissible_ext_elements`: `A.elements = B.elements → A = B` (the two `Prop` fields of
`ResolvedAdmissibleSubgraph` are proof-irrelevant), the bridge from the Codomain's element-level split to the
assembly's graph-level `right_union_eq`.

Per the HALT: `rightSurvivor` / `remnant` / union / disjoint / cross are RECOVERED (proved from the star
filter); the two factor products are isolated as fields; no backward map, no `starPred` construction (fielded).

Landed:

* `admissible_ext_elements` — subgraph extensionality by elements (PROVED);
* `ResolvedRightFactorUnionSupply D` — the star predicate + the two factor products (+ forward data);
* `.rightSurvivorField` / `.remnantField` / `.right_union_eqField` / `.right_hdisjField` /
  `.right_hcrossField` — the assembly's RIGHT union block (union / disjoint / cross PROVED).

Partial-instantiation body (no `coassoc_gen`; feeds the RIGHT block of body-113's assembly).  No facade, no flat
term, no `forgetHopf`.
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

/-- **R-6c-body-115 — subgraph extensionality by elements.**  `ResolvedAdmissibleSubgraph` is determined by its
`elements` (the `isConnectedDivergent` / `pairwiseDisjoint` fields are proof-irrelevant). -/
theorem admissible_ext_elements {A B : ResolvedAdmissibleSubgraph G} (h : A.elements = B.elements) : A = B := by
  cases A; cases B; cases h; rfl

/-- **R-6c-body-115 — the right-factor union supply.**  A residual-star predicate on the quotient forest's
components (splitting it into right survivors / remnant) plus the two factor products, from which the assembly's
RIGHT union block is filled (union / disjoint / cross PROVED). -/
structure ResolvedRightFactorUnionSupply (D : ResolvedCoproductProperForestData) where
  /-- The selected-outer image supply (forward `A_target`). -/
  imageSupply : ∀ (G : ResolvedFeynmanGraph), ResolvedCoassocSelectedOuterImageSupply D G
  /-- The raw quotient forest `B`. -/
  quotientRaw : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedAdmissibleSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1))
  /-- The residual-star predicate: which quotient-forest components are remnant (star-touching). -/
  starPred : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    ResolvedFeynmanSubgraph (((imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((imageSupply G).selectedOuterOf q).1)) → Prop
  /-- The right-survivor factor product (isolated). -/
  right_primitive_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => ¬ (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((quotientRaw G q).filterElements (fun x => ¬ starPred G q x))
  /-- The remnant factor product (isolated). -/
  remnant_factor : ∀ (G : ResolvedFeynmanGraph) (q : ForestBlockDomType D G),
    (∏ γ ∈ (q.1.1.elements.attach).attach.filter (fun γ => (q.2 γ.1 γ.2).isRight),
        localRightFactor (D := D) (γ.1.1.toResolvedFeynmanGraph) (componentCD q.1.1 γ.1) (q.2 γ.1 γ.2))
      = resolvedForestLeftTerm ((quotientRaw G q).filterElements (fun x => starPred G q x))

variable (S : ResolvedRightFactorUnionSupply D)

/-- **R-6c-body-115 — `rightSurvivor`** (star-avoiding quotient components). -/
noncomputable def ResolvedRightFactorUnionSupply.rightSurvivorField (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    ResolvedAdmissibleSubgraph (((S.imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((S.imageSupply G).selectedOuterOf q).1)) :=
  (S.quotientRaw G q).filterElements (fun x => ¬ S.starPred G q x)

/-- **R-6c-body-115 — `remnant`** (star-touching quotient components). -/
noncomputable def ResolvedRightFactorUnionSupply.remnantField (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    ResolvedAdmissibleSubgraph (((S.imageSupply G).selectedOuterOf q).1.contractWithStars
      (D.starOf G ((S.imageSupply G).selectedOuterOf q).1)) :=
  (S.quotientRaw G q).filterElements (fun x => S.starPred G q x)

/-- **R-6c-body-115 — `right_hcross`** (cross-disjointness, from `pairwiseDisjoint`). -/
theorem ResolvedRightFactorUnionSupply.right_hcrossField (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    ∀ γ ∈ (S.rightSurvivorField G q).elements, ∀ δ ∈ (S.remnantField G q).elements,
      γ ≠ δ → ResolvedFeynmanSubgraph.Disjoint γ δ := by
  intro γ hγ δ hδ hne
  simp only [ResolvedRightFactorUnionSupply.rightSurvivorField,
    ResolvedRightFactorUnionSupply.remnantField, ResolvedAdmissibleSubgraph.filterElements,
    ResolvedAdmissibleSubgraph.ofElements_elements, Finset.mem_filter] at hγ hδ
  exact (S.quotientRaw G q).pairwiseDisjoint hγ.1 hδ.1 hne

/-- **R-6c-body-115 — `right_union_eq`** (`quotientRaw = rightSurvivor ∪ remnant`), PROVED. -/
theorem ResolvedRightFactorUnionSupply.right_union_eqField (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    S.quotientRaw G q
      = (S.rightSurvivorField G q).union (S.remnantField G q) (S.right_hcrossField G q) := by
  apply admissible_ext_elements
  rw [ResolvedAdmissibleSubgraph.union_elements]
  ext x
  simp only [ResolvedRightFactorUnionSupply.rightSurvivorField,
    ResolvedRightFactorUnionSupply.remnantField, ResolvedAdmissibleSubgraph.filterElements,
    ResolvedAdmissibleSubgraph.ofElements_elements, Finset.mem_union, Finset.mem_filter]
  tauto

/-- **R-6c-body-115 — `right_hdisj`** (`rightSurvivor` / `remnant` disjoint), PROVED. -/
theorem ResolvedRightFactorUnionSupply.right_hdisjField (G : ResolvedFeynmanGraph)
    (q : ForestBlockDomType D G) :
    Disjoint (S.rightSurvivorField G q).elements (S.remnantField G q).elements := by
  simp only [ResolvedRightFactorUnionSupply.rightSurvivorField,
    ResolvedRightFactorUnionSupply.remnantField, ResolvedAdmissibleSubgraph.filterElements,
    ResolvedAdmissibleSubgraph.ofElements_elements]
  exact (Finset.disjoint_filter_filter_not (S.quotientRaw G q).elements (S.quotientRaw G q).elements
    (fun x => S.starPred G q x)).symm

end GaugeGeometry.QFT.Combinatorial
