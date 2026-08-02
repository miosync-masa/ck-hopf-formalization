import GaugeGeometry.QFT.HopfAlgebra.Phi4StableCoassocAlphaCompletion

/-!
# QFT-R1-body-651 — the STABLE resolved φ⁴ coproduct coassociativity CROWN

Body-650b proved graph-generator coassociativity
`coproduct_resolved_stable_phi4_coassoc_of_graph : stableCoassocLeft (X g) = stableCoassocRight (X g)` for a
generator arising from a resolved graph.  This body promotes it to ALL generators — and hence to the WHOLE
algebra `StableResolvedPhi4HopfH` — by representative selection (`Quotient.out`) + `MvPolynomial.algHom_ext`.
NO geometry, NO finite sum, NO alpha re-expansion.

## Steps
* **Step 1 — stable representative.**  `stablePhi4ResolvedRep x := Quotient.out x.val`, a `ResolvedFeynmanGraph`
  representing the generator's class; `stablePhi4ResolvedRep_class` is the `Quotient.out_eq` class anchor.
* **Step 2 — recover the two certificates.**  `stablePhi4ResolvedRep_isConnectedDivergent` (from `x.property.1`
  through the class-CD descent) and `stablePhi4ResolvedRep_stableBoundaryIds` (from `x.property.2` through
  `hasStableBoundaryIds_mk`) — the raw-representative forms of the generator's two class certificates.
* **Step 3 — representative regenerates the generator.**  `stablePhi4ResolvedRep_gen`:
  `x = (rep).toStableResolvedPhi4HopfGen …` (`Subtype.ext` + `Quotient.out_eq`; the certificate witnesses enter
  proof-irrelevantly).
* **Step 4 — coassociativity on an arbitrary generator.**  `coproduct_resolved_stable_phi4_coassoc_X`: rewrite
  the generator by Step 3 and apply body-650b's graph headline.
* **Step 5 (CROWN) — coassociativity on the whole algebra.**  `coproduct_resolved_stable_phi4_coassociative`
  (`stableCoassocLeft = stableCoassocRight`, via `MvPolynomial.algHom_ext`) and the pointwise
  `coproduct_resolved_stable_phi4_coassoc`.

## HALT compliance
Body-650b's graph headline is NOT re-proved; `Quotient.out` is used ONLY for representative selection; ZERO
`HEq` / `cast` / graph-data `▸`; ZERO forest / bijection / `sum_bij` / alpha re-expansion; ZERO new
`structure` / `class` / `instance`; ZERO forbidden divergence class in any declaration TYPE; NO bridge to the
old resolved / flat coproducts; no `counit` / `Bialgebra` claim.  Axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`).  This proves EXACTLY the whole-algebra coassociativity of the concrete φ⁴₄ stable resolved
coproduct.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-! ## Step 1 — the stable representative -/

/-- **body-651 (Step 1) — the stable representative.**  The `Quotient.out` representative of a stable
generator's graph class.  Representative *selection* on `ResolvedFeynmanGraphClass`; NOT a bridge. -/
noncomputable def stablePhi4ResolvedRep (x : StableResolvedPhi4HopfGen) : ResolvedFeynmanGraph :=
  Quotient.out x.val

/-- **body-651 (Step 1) — the representative lands back on the generator's class.** -/
theorem stablePhi4ResolvedRep_class (x : StableResolvedPhi4HopfGen) :
    (stablePhi4ResolvedRep x).toResolvedClass = x.val :=
  Quotient.out_eq x.val

/-! ## Step 2 — recover the two class certificates on the raw representative -/

/-- **body-651 (Step 2) — the representative is connected-divergent (graph form).**  From the generator's
class-level `IsConnectedDivergentFor` (`x.property.1`) through the class-CD descent. -/
theorem stablePhi4ResolvedRep_isConnectedDivergent (x : StableResolvedPhi4HopfGen) :
    ∃ hWF : (stablePhi4ResolvedRep x).forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (stablePhi4ResolvedRep x).forget
        (phi4DivergenceMeasureFamily (stablePhi4ResolvedRep x).forget)
        (FeynmanSubgraph.self (stablePhi4ResolvedRep x).forget hWF) := by
  refine (ResolvedFeynmanGraphClass.isConnectedDivergentFor_toResolvedClass phi4DivergenceMeasureFamily
    phi4PermInvariantDivergenceMeasureFamily (stablePhi4ResolvedRep x)).mp ?_
  rw [stablePhi4ResolvedRep_class]
  exact x.property.1

/-- **body-651 (Step 2) — the representative owns the stable boundary-ID certificate.**  From the generator's
class-level `HasStableBoundaryIds` (`x.property.2`) through `hasStableBoundaryIds_mk`. -/
theorem stablePhi4ResolvedRep_stableBoundaryIds (x : StableResolvedPhi4HopfGen) :
    StableResolvedBoundaryIds (stablePhi4ResolvedRep x) := by
  rw [← ResolvedFeynmanGraphClass.hasStableBoundaryIds_mk, stablePhi4ResolvedRep_class]
  exact x.property.2

/-! ## Step 3 — the representative regenerates the generator -/

/-- **body-651 (Step 3) — the generator equals the stable generator built from its own representative.**
Representative selection is closed: `Subtype.ext` + `Quotient.out_eq`; the two certificate witnesses enter
proof-irrelevantly. -/
theorem stablePhi4ResolvedRep_gen (x : StableResolvedPhi4HopfGen) :
    x = (stablePhi4ResolvedRep x).toStableResolvedPhi4HopfGen
          (stablePhi4ResolvedRep_isConnectedDivergent x)
          (stablePhi4ResolvedRep_stableBoundaryIds x) := by
  apply Subtype.ext
  rw [ResolvedFeynmanGraph.toStableResolvedPhi4HopfGen_val]
  exact (stablePhi4ResolvedRep_class x).symm

/-! ## Step 4 — coassociativity on an arbitrary generator -/

/-- **body-651 (Step 4) — the stable coproduct is coassociative on an arbitrary generator.**  Rewrite the
generator by its representative (Step 3) and apply body-650b's graph-generator coassociativity. -/
theorem coproduct_resolved_stable_phi4_coassoc_X (x : StableResolvedPhi4HopfGen) :
    stableCoassocLeft (MvPolynomial.X x) = stableCoassocRight (MvPolynomial.X x) := by
  rw [stablePhi4ResolvedRep_gen x]
  exact coproduct_resolved_stable_phi4_coassoc_of_graph (stablePhi4ResolvedRep x)
    (stablePhi4ResolvedRep_isConnectedDivergent x) (stablePhi4ResolvedRep_stableBoundaryIds x)

/-! ## Step 5 — the CROWN: whole-algebra coassociativity -/

/-- **body-651 (Step 5, CROWN) — the concrete φ⁴₄ stable resolved coproduct is COASSOCIATIVE.**  The two
iterated coproducts `assoc ∘ (Δˢ ⊗ id) ∘ Δˢ` and `(id ⊗ Δˢ) ∘ Δˢ` agree on every generator (Step 4), hence
agree as algebra homs by `MvPolynomial.algHom_ext`.  Whole-algebra `Δᵣˢ`-coassociativity of the stable resolved
φ⁴ Hopf coproduct — the crowning terminus of the stable forest-block bijection → finite-sum reindex → alpha
bridge arc. -/
theorem coproduct_resolved_stable_phi4_coassociative :
    (stableCoassocLeft : StableResolvedPhi4HopfH →ₐ[ℚ] StableResolvedPhi4HopfH3) = stableCoassocRight := by
  apply MvPolynomial.algHom_ext
  intro x
  exact coproduct_resolved_stable_phi4_coassoc_X x

/-- **body-651 (Step 5, pointwise) — the coassociativity computation rule.**  For every element `p`,
`stableCoassocLeft p = stableCoassocRight p`. -/
theorem coproduct_resolved_stable_phi4_coassoc (p : StableResolvedPhi4HopfH) :
    stableCoassocLeft p = stableCoassocRight p :=
  AlgHom.congr_fun coproduct_resolved_stable_phi4_coassociative p

end GaugeGeometry.QFT.Combinatorial
