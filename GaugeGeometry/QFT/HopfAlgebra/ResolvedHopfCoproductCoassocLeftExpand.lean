import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocReindex

/-!
# R-6c-2b — the left iterated-coproduct expansion (`lhsExpansion`, first level)

The second frontier obligation: identify what `coassocLeft D (X x)` *is*, in terms of a primitive part
plus an outer branch sum.  This is the **first-level linear expansion** — it splits the iterated
coproduct along `Δᵣ(X x) = primitive + ∑ forest summands` and uses that the remaining map
`coassocLeftTail = assoc ∘ (Δᵣ ⊗ id)` is an algebra hom (hence additive and sum-distributing).  It
does **not** yet expand `Δᵣ(leftTerm A)` into its inner forest/mixed double sum (that inner expansion,
which matches `ResolvedH58TermReindex.branchSum`, is the next step); here we pin the *outer* shape.

Every generator is `G.toResolvedHopfGen hCD` for a representative graph `G` (the `ResolvedHopfGen`
quotient), and the forest sum computes on representatives (`forestSum_mk`), so the expansion is stated
at the representative level.

Landed:

* `ResolvedCoproductProperForestData.coassocLeftTail` — the post-`Δᵣ` part of `coassocLeft`,
  `assoc ∘ (Δᵣ ⊗ id) : ResolvedHopfH ⊗ ResolvedHopfH →ₐ ResolvedHopfH3`, so that
  `coassocLeft D y = coassocLeftTail D (Δᵣ y)` (`coassocLeft_apply`, definitional);
* `ResolvedCoproductProperForestData.coassocLeft_expand` — **the first-level left expansion**:
  `coassocLeft D (X (G.toResolvedHopfGen hCD))` equals the primitive part
  `coassocLeftTail D (primitive g)` plus the outer branch sum
  `∑ A ∈ (D.supply G).forestCarrier, coassocLeftTail D (leftTerm A ⊗ rightTerm A)`.

This identifies `primitivePart` (= `coassocLeftTail D (resolvedCoproductGenPrimitive g)`) and the
per-outer branch term (= `coassocLeftTail D (leftTerm A ⊗ rightTerm A)`) concretely.  No facade, no
flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]

variable (D : ResolvedCoproductProperForestData)

/-- The post-`Δᵣ` tail of `coassocLeft`: apply `Δᵣ` to the left tensor factor, then re-associate.
By definition `coassocLeft D = coassocLeftTail D ∘ Δᵣ`. -/
noncomputable def ResolvedCoproductProperForestData.coassocLeftTail :
    ResolvedHopfH ⊗[ℚ] ResolvedHopfH →ₐ[ℚ] ResolvedHopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ ResolvedHopfH ResolvedHopfH ResolvedHopfH).toAlgHom.comp
    (Algebra.TensorProduct.map D.coproduct (AlgHom.id ℚ ResolvedHopfH))

/-- `coassocLeft` factors through `coassocLeftTail` after `Δᵣ` (definitional). -/
theorem ResolvedCoproductProperForestData.coassocLeft_apply (y : ResolvedHopfH) :
    D.coassocLeft y = D.coassocLeftTail (D.coproduct y) := rfl

/-- **R-6c-2b — the first-level left expansion of the iterated coproduct.**  On a generator
`X (G.toResolvedHopfGen hCD)`, `coassocLeft D` splits into the primitive part (the tail applied to
`X g ⊗ 1 + 1 ⊗ X g`) plus the outer branch sum (the tail applied to each forest summand
`leftTerm A ⊗ rightTerm A`).  Proof: `coassocLeft = coassocLeftTail ∘ Δᵣ`, `Δᵣ(X g) = gen g =
primitive + forest sum`, and `coassocLeftTail` is an algebra hom (`map_add`, `map_sum`). -/
theorem ResolvedCoproductProperForestData.coassocLeft_expand
    (G : ResolvedFeynmanGraph) (hCD : G.forget.toClass.IsConnectedDivergent) :
    D.coassocLeft (MvPolynomial.X (G.toResolvedHopfGen hCD))
      = D.coassocLeftTail (resolvedCoproductGenPrimitive (G.toResolvedHopfGen hCD))
        + ∑ A ∈ (D.supply G).forestCarrier,
            D.coassocLeftTail ((D.supply G).leftTerm A ⊗ₜ[ℚ] (D.supply G).rightTerm A) := by
  rw [D.coassocLeft_apply]
  simp only [ResolvedCoproductProperForestData.coproduct]
  rw [ResolvedCoproductGenSupply.coproduct_X]
  simp only [ResolvedCoproductGenSupply.gen, ResolvedFeynmanGraph.toResolvedHopfGen_val,
    ResolvedCoproductGenSupply.forestSum_mk]
  rw [map_add]
  simp only [ResolvedCoproductForestSummandSupply.sum]
  rw [map_sum]
  rfl

end GaugeGeometry.QFT.Combinatorial
