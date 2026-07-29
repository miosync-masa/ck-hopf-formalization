import GaugeGeometry.QFT.HopfAlgebra.Phi4ResolvedForestLeft

/-!
# QFT-R1-body-591 — family-native resolved W″ coproduct owner

Body-590 assembled the resolved forest **left** aggregate `ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH`
(+ rename invariance); body-588 assembled the resolved forest **right** term `resolvedForestRightTermFor`
(+ `rightTerm_mapPerm`) and the full family carrier `phi4WDoublePrimeCanonicalSupply`.  This body issues the
forest sum and the genuine resolved coproduct `Δᵣ` from ONE owner.

It is a **faithful family re-key** of the old `ResolvedHopfCoproduct.lean` (template lines 75-215): every
`ResolvedHopfGen` / `ResolvedHopfH` becomes the family type `ResolvedHopfGenFor D Inv` / `ResolvedHopfHFor D Inv`,
and the concrete owner is wired from body-588's `phi4WDoublePrimeCanonicalSupply` (right terms + carrier) and
body-590's left aggregate.

## Contents

* Step 1 — `ResolvedCoproductForestSummandSupplyFor` (family summand interface, structure #1) + `.sum` +
  `.sum_eq_of_bij` (the pure `Finset.sum_bij` invariance fact).
* Step 2 — `ResolvedCanonicalCarrierProperSupplyFor.summandSupply` (the single φ⁴ owner reading its `index` /
  `starOf` / `hCD` off the 588 supply; left = body-590 aggregate, right = body-588 right term).
* Step 3 — `summandSupply_sum_mapPerm` (forest-sum rename invariance via `sum_eq_of_bij`: carrier bijection
  from `carrier_mapPerm`, left via body-590, right via the 588 `rightTerm_mapPerm`).
* Step 4 — `resolvedCoproductGenPrimitiveFor` + `ResolvedCoproductGenSupplyFor` (structure #2) +
  `phi4WDoublePrimeResolvedCoproductSupply` (the concrete owner).
* Step 5 — `forestSum` (`Quotient.liftOn`) + `gen` + `coproduct` (`aeval`) + `coproduct_X`, and the concrete
  `coproduct_resolved_phi4 : ResolvedPhi4HopfH →ₐ[ℚ] ResolvedPhi4HopfH ⊗ ResolvedPhi4HopfH` + computation laws.

Per the HALT: no equality / compatibility with the flat `coproduct_phi4`; no `forgetPhi4Hopf` / `rigidifyPhi4Hopf`
wiring; no Measure / E / rep*; no coassoc / counit / bialgebra / antipode; no old `ResolvedHopfGen` /
`ResolvedHopfH` / old `ResolvedCoproduct*Supply` (family types only); zero forbidden divergence classes in any
type (only `D` / `Inv`; the concrete ones are `phi4…`); no star / correcting-permutation re-expansion; exactly
TWO new `structure`s; no `class` / `instance`; no `sorry`.
-/

open scoped TensorProduct
open scoped Classical

namespace GaugeGeometry.QFT.Combinatorial

/-! ## Step 1 — family summand interface (structure #1) -/

/-- **body-591 (Step 1) — a finite family of resolved coproduct forest summands for a representative graph
`G`, family-keyed.**  Each index contributes `leftTerm A ⊗ rightTerm A`, with both factors resolved-algebra
terms (the left is the forest's component-generator product, not a single generator).  Faithful family re-key of
`ResolvedCoproductForestSummandSupply`. -/
structure ResolvedCoproductForestSummandSupplyFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (G : ResolvedFeynmanGraph) where
  /-- The forest index type. -/
  ForestIdx : Type
  /-- The finite forest carrier. -/
  forestCarrier : Finset ForestIdx
  /-- The left (outer forest) resolved-algebra term of each summand. -/
  leftTerm : ForestIdx → ResolvedHopfHFor D Inv
  /-- The right (quotient/remnant) resolved-algebra term of each summand. -/
  rightTerm : ForestIdx → ResolvedHopfHFor D Inv

/-- The forest-sum tensor term of a family summand supply. -/
noncomputable def ResolvedCoproductForestSummandSupplyFor.sum
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    {G : ResolvedFeynmanGraph} (S : ResolvedCoproductForestSummandSupplyFor D Inv G) :
    ResolvedHopfHFor D Inv ⊗[ℚ] ResolvedHopfHFor D Inv :=
  ∑ A ∈ S.forestCarrier, S.leftTerm A ⊗ₜ[ℚ] S.rightTerm A

/-- **body-591 (Step 1) — the graph-free forest-sum invariance.**  A carrier bijection preserving both the
left and right resolved-algebra terms gives equal forest sums.  Faithful family re-key of
`ResolvedCoproductForestSummandSupply.sum_eq_of_bij` (pure `Finset.sum_bij`). -/
theorem ResolvedCoproductForestSummandSupplyFor.sum_eq_of_bij
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    {G G' : ResolvedFeynmanGraph}
    (S : ResolvedCoproductForestSummandSupplyFor D Inv G)
    (T : ResolvedCoproductForestSummandSupplyFor D Inv G')
    (i : (a : S.ForestIdx) → a ∈ S.forestCarrier → T.ForestIdx)
    (hmaps : ∀ a (ha : a ∈ S.forestCarrier), i a ha ∈ T.forestCarrier)
    (i_inj : ∀ a₁ (ha₁ : a₁ ∈ S.forestCarrier) a₂ (ha₂ : a₂ ∈ S.forestCarrier),
      i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ T.forestCarrier, ∃ a, ∃ (ha : a ∈ S.forestCarrier), i a ha = b)
    (hleft : ∀ a (ha : a ∈ S.forestCarrier), S.leftTerm a = T.leftTerm (i a ha))
    (hright : ∀ a (ha : a ∈ S.forestCarrier), S.rightTerm a = T.rightTerm (i a ha)) :
    S.sum = T.sum := by
  unfold ResolvedCoproductForestSummandSupplyFor.sum
  exact Finset.sum_bij i hmaps i_inj i_surj
    (fun a ha => by rw [hleft a ha, hright a ha])

/-! ## Step 2 — the single-owner summand supply (φ⁴-fixed receiver) -/

/-- **body-591 (Step 2) — the φ⁴ W″ forest-summand supply from one owner.**  Reads `index` / `starOf` / `hCD`
off the body-588 full carrier supply `R`; the left term is body-590's resolved forest aggregate, the right term
is body-588's resolved forest right term.  One owner, no re-issued index/star/CD. -/
noncomputable def ResolvedCanonicalCarrierProperSupplyFor.summandSupply
    (R : ResolvedCanonicalCarrierProperSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily)
    (G : ResolvedFeynmanGraph) :
    ResolvedCoproductForestSummandSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily G :=
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  { ForestIdx := {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G // A ∈ (R.index G).carrier}
    forestCarrier := (R.index G).carrier.attach
    leftTerm := fun A => A.1.toResolvedPhi4HopfH
    rightTerm := fun A => resolvedForestRightTermFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily A.1 (R.starOf G A.1) (R.hCD G A.1 A.2) }

/-! ## Step 3 — forest-sum rename invariance -/

/-- **body-591 (Step 3, load-bearing) — the φ⁴ W″ forest sum is rename-invariant.**  Via `sum_eq_of_bij`: the
carrier bijection is the resolved forest relabeling (body-587, membership from `R.carrier_mapPerm`), the left
factors match by body-590 `toResolvedPhi4HopfH_mapPermFor`, the right factors by the body-588 field
`rightTerm_mapPerm`.  No star / correcting permutation is unfolded (the 588 field already absorbed it). -/
theorem ResolvedCanonicalCarrierProperSupplyFor.summandSupply_sum_mapPerm
    (R : ResolvedCanonicalCarrierProperSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily)
    (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    (R.summandSupply (G.mapPerm σ)).sum = (R.summandSupply G).sum := by
  letI : (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily
  symm
  -- membership transport `(R.index G).carrier → (R.index (G.mapPerm σ)).carrier` via `carrier_mapPerm`
  have hmem : ∀ A : {A : @ResolvedAdmissibleSubgraph phi4DivergenceMeasureFamily G
        // A ∈ (R.index G).carrier},
      mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1
        ∈ (R.index (G.mapPerm σ)).carrier := by
    intro A
    rw [R.carrier_mapPerm G σ]
    exact Finset.mem_image.mpr ⟨A.1, A.2, rfl⟩
  refine ResolvedCoproductForestSummandSupplyFor.sum_eq_of_bij
    (R.summandSupply G) (R.summandSupply (G.mapPerm σ))
    (fun A _ => ⟨mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
        phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) A.1, hmem A⟩)
    (fun _ _ => Finset.mem_attach _ _) ?_ ?_ ?_ ?_
  · -- injective
    intro a₁ _ a₂ _ heq
    have h1 : mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) a₁.1
        = mapPermResolvedAdmissibleSubgraphFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) a₂.1 :=
      congrArg Subtype.val heq
    exact Subtype.ext (mapPermResolvedAdmissibleSubgraphFor_injective phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily (rfl : G.mapPerm σ = G.mapPerm σ) h1)
  · -- surjective
    intro b _
    obtain ⟨bv, hbv⟩ := b
    rw [R.carrier_mapPerm G σ] at hbv
    obtain ⟨A, hA, hAeq⟩ := Finset.mem_image.mp hbv
    exact ⟨⟨A, hA⟩, Finset.mem_attach _ _, Subtype.ext hAeq⟩
  · -- left factors (body-590)
    intro a _
    exact (ResolvedAdmissibleSubgraph.toResolvedPhi4HopfH_mapPermFor
      (rfl : G.mapPerm σ = G.mapPerm σ) a.1).symm
  · -- right factors (body-588 field)
    intro a _
    exact R.rightTerm_mapPerm G σ a.1 a.2 (hmem a)

/-! ## Step 4 — the coproduct owner (structure #2) + concrete owner -/

/-- **body-591 (Step 4) — the primitive part of the resolved coproduct on a family generator**:
`X x ⊗ 1 + 1 ⊗ X x`, defined on `x` directly (no representative choice).  Faithful family re-key of
`resolvedCoproductGenPrimitive`. -/
noncomputable def resolvedCoproductGenPrimitiveFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D)
    (x : ResolvedHopfGenFor D Inv) :
    ResolvedHopfHFor D Inv ⊗[ℚ] ResolvedHopfHFor D Inv :=
  MvPolynomial.X x ⊗ₜ[ℚ] (1 : ResolvedHopfHFor D Inv)
    + (1 : ResolvedHopfHFor D Inv) ⊗ₜ[ℚ] MvPolynomial.X x

/-- **body-591 (Step 4) — a `mapPerm`-equivariant family of resolved forest-summand supplies.**  One supply per
representative graph, with the forest sum invariant under id-preserving relabeling — the single datum
`Quotient.lift` needs.  Faithful family re-key of `ResolvedCoproductGenSupply`. -/
structure ResolvedCoproductGenSupplyFor
    (D : DivergenceMeasureFamily) (Inv : PermInvariantDivergenceMeasureFamily D) where
  /-- A forest-summand supply for every representative graph. -/
  supply : (G : ResolvedFeynmanGraph) → ResolvedCoproductForestSummandSupplyFor D Inv G
  /-- **Equivariance**: the forest sum is invariant under id-preserving relabeling. -/
  sum_mapPerm : ∀ (G : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId),
    (supply (G.mapPerm σ)).sum = (supply G).sum

/-- **body-591 (Step 4) — the concrete φ⁴ W″ resolved coproduct owner.**  The body-588 full carrier supply
`phi4WDoublePrimeCanonicalSupply`, read as an equivariant forest-summand supply family (`summandSupply` +
`summandSupply_sum_mapPerm`). -/
noncomputable def phi4WDoublePrimeResolvedCoproductSupply :
    ResolvedCoproductGenSupplyFor phi4DivergenceMeasureFamily
      phi4PermInvariantDivergenceMeasureFamily where
  supply := phi4WDoublePrimeCanonicalSupply.summandSupply
  sum_mapPerm := fun G σ => phi4WDoublePrimeCanonicalSupply.summandSupply_sum_mapPerm G σ

/-! ## Step 5 — the genuine resolved `Δᵣ` -/

/-- **body-591 (Step 5) — the forest sum descended through the resolved graph class** (well defined by
`sum_mapPerm`).  Faithful family re-key of `ResolvedCoproductGenSupply.forestSum`. -/
noncomputable def ResolvedCoproductGenSupplyFor.forestSum
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (S : ResolvedCoproductGenSupplyFor D Inv) (c : ResolvedFeynmanGraphClass) :
    ResolvedHopfHFor D Inv ⊗[ℚ] ResolvedHopfHFor D Inv :=
  Quotient.liftOn c (fun G => (S.supply G).sum) (by
    intro G₁ G₂ h
    obtain ⟨σ, rfl⟩ := h
    exact (S.sum_mapPerm G₁ σ).symm)

@[simp] theorem ResolvedCoproductGenSupplyFor.forestSum_mk
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (S : ResolvedCoproductGenSupplyFor D Inv) (G : ResolvedFeynmanGraph) :
    S.forestSum G.toResolvedClass = (S.supply G).sum := rfl

/-- **body-591 (Step 5) — `Δᵣ` on family generators.**  The primitive part (on `x` directly) plus the forest
sum descended from the class.  Faithful family re-key of `ResolvedCoproductGenSupply.gen`. -/
noncomputable def ResolvedCoproductGenSupplyFor.gen
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (S : ResolvedCoproductGenSupplyFor D Inv) (x : ResolvedHopfGenFor D Inv) :
    ResolvedHopfHFor D Inv ⊗[ℚ] ResolvedHopfHFor D Inv :=
  resolvedCoproductGenPrimitiveFor D Inv x + S.forestSum x.1

/-- **body-591 (Step 5) — the family-native resolved coproduct as an algebra hom**
`ResolvedHopfHFor D Inv →ₐ ResolvedHopfHFor D Inv ⊗ ResolvedHopfHFor D Inv`, the `MvPolynomial.aeval` extension
of `Δᵣ` on generators.  Faithful family re-key of `ResolvedCoproductGenSupply.coproduct`. -/
noncomputable def ResolvedCoproductGenSupplyFor.coproduct
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (S : ResolvedCoproductGenSupplyFor D Inv) :
    ResolvedHopfHFor D Inv →ₐ[ℚ] ResolvedHopfHFor D Inv ⊗[ℚ] ResolvedHopfHFor D Inv :=
  MvPolynomial.aeval S.gen

@[simp] theorem ResolvedCoproductGenSupplyFor.coproduct_X
    {D : DivergenceMeasureFamily} {Inv : PermInvariantDivergenceMeasureFamily D}
    (S : ResolvedCoproductGenSupplyFor D Inv) (x : ResolvedHopfGenFor D Inv) :
    S.coproduct (MvPolynomial.X x) = S.gen x := by
  simp [ResolvedCoproductGenSupplyFor.coproduct]

/-- **body-591 (Step 5, TARGET) — the genuine φ⁴ resolved-native coproduct** `Δᵣ : ResolvedPhi4HopfH →ₐ
ResolvedPhi4HopfH ⊗ ResolvedPhi4HopfH`, from the single owner `phi4WDoublePrimeResolvedCoproductSupply`.  Every
tensor factor is a `ResolvedPhi4HopfGen` (id-preserving class); no flat shadow, no facade, no coassoc. -/
noncomputable def coproduct_resolved_phi4 :
    ResolvedPhi4HopfH →ₐ[ℚ] ResolvedPhi4HopfH ⊗[ℚ] ResolvedPhi4HopfH :=
  phi4WDoublePrimeResolvedCoproductSupply.coproduct

/-- **body-591 — `Δᵣ` on a φ⁴ resolved generator.**  Primitive part plus the descended forest sum. -/
@[simp] theorem coproduct_resolved_phi4_X (x : ResolvedPhi4HopfGen) :
    coproduct_resolved_phi4 (MvPolynomial.X x) = phi4WDoublePrimeResolvedCoproductSupply.gen x := by
  unfold coproduct_resolved_phi4
  rw [ResolvedCoproductGenSupplyFor.coproduct_X]

/-- **body-591 — `Δᵣ` preserves the unit.** -/
theorem coproduct_resolved_phi4_one : coproduct_resolved_phi4 1 = 1 := map_one _

/-- **body-591 — `Δᵣ` is multiplicative.** -/
theorem coproduct_resolved_phi4_mul (a b : ResolvedPhi4HopfH) :
    coproduct_resolved_phi4 (a * b) = coproduct_resolved_phi4 a * coproduct_resolved_phi4 b :=
  map_mul _ _ _

/-- **body-591 — `Δᵣ` on a resolved-graph generator** is the primitive part plus the full W″ forest summand
sum (body-590 left aggregates ⊗ body-588 right terms over the W″ carrier). -/
theorem coproduct_resolved_phi4_of_graph (G : ResolvedFeynmanGraph)
    (hCD : ∃ hWF : G.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget)
        (FeynmanSubgraph.self G.forget hWF)) :
    coproduct_resolved_phi4 (MvPolynomial.X (G.toResolvedPhi4HopfGen hCD))
      = resolvedCoproductGenPrimitiveFor phi4DivergenceMeasureFamily
          phi4PermInvariantDivergenceMeasureFamily (G.toResolvedPhi4HopfGen hCD)
        + (phi4WDoublePrimeCanonicalSupply.summandSupply G).sum := by
  rw [coproduct_resolved_phi4_X]
  rfl

end GaugeGeometry.QFT.Combinatorial
