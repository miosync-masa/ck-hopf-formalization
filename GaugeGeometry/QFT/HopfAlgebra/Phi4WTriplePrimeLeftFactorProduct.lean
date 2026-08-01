import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeSummandAgreement

/-!
# QFT-R1-body-625 — family-native LEFT-factor product identity: a CRITICAL COHERENCE AUDIT (verdict = **Branch B**)

Body-624 reduced the forward summand agreement to three geometric identities, the first of which is the
**left-factor product identity**

```text
∏_{γ} phi4EdgeCompleteLocalLeftFactor γ (s.choice γ)  =  (selectedOuter s).toResolvedPhi4HopfH .
```

This body was to prove that identity family-natively.  It is written instead as a **critical audit**: the
victory condition is NOT to force the identity through, but to DETERMINE IN LEAN whether the per-occurrence
resolved-class equality that the identity secretly requires actually holds on the current resolved carrier.

The generator keying is class-valued: `toResolvedPhi4HopfGenBoundaryCompleted γ` has
`.val = γ.boundaryCompletedResolvedGraph.toResolvedClass` (body-589).  So the two sides of the left-factor
identity agree per FOREST occurrence `(γ, δ)` iff

```text
δ.boundaryCompletedResolvedGraph.toResolvedClass  =  (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass ,
```

the LOCAL nested completion (of `δ ⊆ γ.boundaryCompletedResolvedGraph`) against the ROOT direct completion
of the lift `rootRelativeInner γ δ`.  Body-596/597 already diagnosed this pair: the local route RE-ENCODES an
inherited boundary leg (odd `2e+1`) as an existing leg (`existingLegId = 4e+2`, even), while the root route
keeps it a fresh boundary leg (`boundaryLegId = 2e+1`, odd).

## Verdict: **Branch B — a genuine no-go.**

The per-occurrence class equality FAILS whenever `δ` carries an inherited outer boundary edge
(`e ∈ inheritedOuter γ δ`).  The `legId` multiset profile is a `mapPerm`-invariant, resolved class equality is
`∃ σ, · = ·.mapPerm σ`, and `mapPerm` preserves every `legId`; the odd value `2e+1` occurs in the ROOT
profile but — using ambient `EdgeIdsUnique` to exclude an accidental proxy by another boundary edge — is
ABSENT from the LOCAL profile.  So no relabeling can reconcile the two, the classes differ, and the two
left-factor generators `X …` are unequal.  The full target
`phi4WTriplePrime_selectedOuter_leftFactor_product` is therefore **NOT emitted** (that would require the very
class equality this body refutes).

## Contents

* **Step 1 — primitive half (unconditional).**  `…_leftFactor_inl_true/false` (branch values) and
  `…_leftFactor_primitive_product`: over the LEFT-selected outer forest `leftOf s`, the primitive left factor
  reproduces exactly `(leftOf s).toResolvedPhi4HopfH` (multiplicity-exact, no bijection — a `Finset.prod`
  over `leftOf.elements.attach` with matching generators).  The primitive half is fine; the crack is FOREST.
* **Step 2 — occurrence normal form.**  `…_forestLeftFactor_eq_localAggregate`: the FOREST left factor is the
  LOCAL nested aggregate `B.1.toResolvedPhi4HopfH = ∏_{δ ∈ B.1.elements} X(δ.boundaryCompletedResolvedGraph …)`
  (δ-nested keys).  `…_promotedComponent_key`: the promoted component's generator is keyed by the ROOT-direct
  `(rootRelativeInner γ δ).boundaryCompletedResolvedGraph` class.  These are the two per-occurrence keys.
* **Step 3 — the class-level NO-GO (the crux).**  `…_legIdProfile` (+ `…_mapPerm` invariance, mirrored
  family-natively from body-596 which is NOT in this import chain), the root-profile membership /
  local-profile non-membership of `boundaryLegId e = 2e+1`, then the HEADLINE
  `…_nestedLeft_class_ne_of_inheritedOuter` and its algebraic manifestation
  `…_nestedLeft_gen_ne_of_inheritedOuter` (the two left-factor generators are unequal).
* **Step 4 — verdict.**  Branch B fired; the strict resolved-coproduct coassoc target is a REDESIGN target.
  The evidence points to a **stable / idempotent completion** route: body-597 already builds the stable nested
  completion `stableNestedBoundaryCompletedGraph γ δ = (rootRelativeInner γ δ).boundaryCompletedResolvedGraph`,
  i.e. the SAME graph the promoted branch uses — so re-keying the FOREST left factor through body-597's stable
  completion (rather than the naive `δ.boundaryCompletedResolvedGraph`) is the natural repair, not an
  ID-renaming quotient or a `forget`-flattening.

## HALT compliance
No full target `phi4WTriplePrime_selectedOuter_leftFactor_product`; NO added coherence hypothesis on the
audited class equality (`EdgeIdsUnique` is the honest traceability tool, NOT a coherence axiom); NO vertex
correcting permutation applied to the `legId` comparison; NO orbit quotient / dedup; NO right factor /
`quot_eq` / summand agreement.  Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); ZERO forbidden
divergence classes in any declaration type; NO polluted `D`-keyed body-258 theorem consumed; NO public
`HEq` / `cast` / `▸`; NO `sorry` / `admit` / `native_decide`; bodies 601/596/597/624 unedited; ONE new file;
a file-local `local instance` for the divergence measure family, no other new `class` / `instance`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

noncomputable local instance phi4Inst625 : (H : FeynmanGraph) → DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the primitive half (unconditional) -/

/-- **body-625 (Step 1) — the LEFT primitive branch value.**  On `Sum.inl true` the left factor is the
boundary-completed generator (`bif true`). -/
theorem phi4WTriplePrime_leftFactor_inl_true {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    phi4EdgeCompleteLocalLeftFactor γ hCD (Sum.inl true)
      = MvPolynomial.X (γ.toResolvedPhi4HopfGenBoundaryCompleted hCD) := rfl

/-- **body-625 (Step 1) — the RIGHT primitive branch value.**  On `Sum.inl false` the left factor is `1`
(`bif false`), so a right-selected component contributes nothing to the left product. -/
theorem phi4WTriplePrime_leftFactor_inl_false {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF)) :
    phi4EdgeCompleteLocalLeftFactor γ hCD (Sum.inl false) = (1 : ResolvedPhi4HopfH) := rfl

/-- **body-625 (Step 1, HEADLINE primitive) — the primitive left product is exactly `leftOf`'s aggregate.**
Over the LEFT-selected outer forest `leftOf s`, the boundary-completed left generator (the `Sum.inl true`
branch value) assembled over `leftOf.elements.attach` reproduces `(leftOf s).toResolvedPhi4HopfH`
multiplicity-exactly.  Pure `Finset.prod` term matching — no bijection, no dedup; the CD witnesses enter
proof-irrelevantly (identical `hCD` terms on both sides). -/
theorem phi4WTriplePrime_leftFactor_primitive_product
    (s : Phi4EdgeCompleteFilteredCoassocSplitChoice G) :
    (∏ c ∈ (phi4WTriplePrime_leftOf s).elements.attach,
        phi4EdgeCompleteLocalLeftFactor c.1
          (c.1.boundaryCompletedResolvedGraph_exists_self_isConnectedDivergent
            ((phi4WTriplePrime_leftOf s).isConnectedDivergent c.1 c.2))
          (Sum.inl true))
      = (phi4WTriplePrime_leftOf s).toResolvedPhi4HopfH := rfl

/-! ## Step 2 — occurrence normal form: the two per-occurrence keys -/

/-- **body-625 (Step 2) — the FOREST left factor is the LOCAL nested aggregate.**  On `Sum.inr B` the left
factor is `(summandSupply γ.boundaryCompletedResolvedGraph).leftTerm B = B.1.toResolvedPhi4HopfH`, i.e. the
product of the LOCAL nested generators `X(δ.boundaryCompletedResolvedGraph …)` over `δ ∈ B.1.elements` —
generators keyed by the *nested* completion of `δ ⊆ γ.boundaryCompletedResolvedGraph`. -/
theorem phi4WTriplePrime_forestLeftFactor_eq_localAggregate {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G)
    (hCD : ∃ hWF : γ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent γ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily γ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self γ.boundaryCompletedResolvedGraph.forget hWF))
    (B : (phi4WTriplePrimeCanonicalSupply.summandSupply γ.boundaryCompletedResolvedGraph).ForestIdx) :
    phi4EdgeCompleteLocalLeftFactor γ hCD (Sum.inr B) = B.1.toResolvedPhi4HopfH := rfl

/-- **body-625 (Step 2) — the promoted component's ROOT-direct key.**  In the target
`(selectedOuter s).toResolvedPhi4HopfH`, a promoted component `rootRelativeInner γ δ` contributes the
generator whose class is `(rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass` — the ROOT
direct completion of the lift, NOT the nested completion of `δ`.  Comparing this key against Step 2's local
key is the per-occurrence coherence question settled in Step 3. -/
theorem phi4WTriplePrime_promotedComponent_key {G : ResolvedFeynmanGraph}
    (γ : ResolvedFeynmanSubgraph G) (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hCD : ∃ hWF : (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget hWF)) :
    ((rootRelativeInner γ δ).toResolvedPhi4HopfGenBoundaryCompleted hCD).val
      = (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass := rfl

/-! ## Step 3 — the class-level NO-GO (mirror of body-596, which is NOT in this import chain) -/

/-- **body-625 (Step 3) — the resolved leg-ID profile.**  The multiset of a resolved graph's external-leg
`legId`s.  Family-native re-derivation of body-596's `resolvedLegIdProfile` (that body is outside this import
chain, so its clean version is mirrored, not consumed). -/
def phi4WTriplePrime_legIdProfile (K : ResolvedFeynmanGraph) : Multiset ResolvedLegId :=
  K.externalLegs.map ResolvedExternalLeg.legId

/-- **body-625 (Step 3) — the leg-ID profile is `mapPerm`-invariant.**  `ResolvedExternalLeg.map σ` keeps
every `legId`, so relabeling leaves the profile unchanged — and resolved class equality is exactly
`∃ σ, · = ·.mapPerm σ`, so equal classes force equal profiles. -/
@[simp] theorem phi4WTriplePrime_legIdProfile_mapPerm (K : ResolvedFeynmanGraph) (σ : Equiv.Perm VertexId) :
    phi4WTriplePrime_legIdProfile (K.mapPerm σ) = phi4WTriplePrime_legIdProfile K := by
  unfold phi4WTriplePrime_legIdProfile
  show (K.externalLegs.map (ResolvedExternalLeg.map σ)).map ResolvedExternalLeg.legId
    = K.externalLegs.map ResolvedExternalLeg.legId
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun ℓ _ => rfl)

/-- **body-625 (Step 3) — the odd inherited value lands in the ROOT profile.**  An inherited outer edge `e`
is a root boundary edge of `R := rootRelativeInner γ δ` (body-597), so `R.boundaryExternalLeg e` is a leg of
`R.boundaryCompletedResolvedGraph` with `legId = boundaryLegId e = 2e+1`. -/
theorem phi4WTriplePrime_boundaryLegId_mem_rootProfile
    (γ : ResolvedFeynmanSubgraph G) (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    {e : ResolvedFeynmanEdge} (he : e ∈ inheritedOuter γ δ) :
    boundaryLegId e
      ∈ phi4WTriplePrime_legIdProfile (rootRelativeInner γ δ).boundaryCompletedResolvedGraph := by
  have heR : e ∈ (rootRelativeInner γ δ).resolvedBoundaryEdges :=
    Multiset.mem_of_le (inheritedOuter_le_R_resolvedBoundaryEdges γ δ) he
  unfold phi4WTriplePrime_legIdProfile
  rw [boundaryCompletedResolvedGraph_externalLegs,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs, Multiset.map_add]
  refine Multiset.mem_add.mpr (Or.inr ?_)
  rw [Multiset.map_map]
  exact Multiset.mem_map.mpr ⟨e, heR, rfl⟩

/-- **body-625 (Step 3, CRUX) — the odd inherited value is ABSENT from the LOCAL profile.**  In
`δ.boundaryCompletedResolvedGraph` every leg is either an EVEN re-encoded existing leg (`existingLegId`, never
`2e+1` by parity) or the ODD boundary leg of a `δ`-boundary edge `e'` (`boundaryLegId e' = 2e'+1`).  If
`2e'+1 = 2e+1` then `EdgeIdsUnique` forces `e' = e`; but `e'` lies in `γ.internalEdges` (both endpoints inside
`γ`) whereas the inherited `e` is a `γ`-boundary edge (one endpoint outside) — contradiction.  This is the
`EdgeIdsUnique`-driven exclusion of an accidental proxy by another edge. -/
theorem phi4WTriplePrime_boundaryLegId_not_mem_localProfile (hEdge : G.EdgeIdsUnique)
    (γ : ResolvedFeynmanSubgraph G) (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    {e : ResolvedFeynmanEdge} (he : e ∈ inheritedOuter γ δ) :
    boundaryLegId e ∉ phi4WTriplePrime_legIdProfile δ.boundaryCompletedResolvedGraph := by
  -- unpack `e`: a `γ`-boundary edge of `G`
  unfold inheritedOuter at he
  rw [Multiset.mem_filter] at he
  obtain ⟨heBdE, _⟩ := he
  obtain ⟨heG, heBd⟩ := resolvedBoundaryEdges_mem.mp heBdE
  intro hmem
  unfold phi4WTriplePrime_legIdProfile at hmem
  rw [boundaryCompletedResolvedGraph_externalLegs,
    ResolvedFeynmanSubgraph.boundaryCompletedResolvedExternalLegs, Multiset.map_add] at hmem
  rcases Multiset.mem_add.mp hmem with hEven | hOdd
  · -- EVEN part: `existingLegId ℓ = boundaryLegId e` is a parity contradiction
    rw [Multiset.map_map] at hEven
    obtain ⟨ℓ, _, hval⟩ := Multiset.mem_map.mp hEven
    exact existingLegId_ne_boundaryLegId ℓ e hval
  · -- ODD part: another `δ`-boundary edge `e'` with `boundaryLegId e' = boundaryLegId e`
    rw [Multiset.map_map] at hOdd
    obtain ⟨e', he', hval⟩ := Multiset.mem_map.mp hOdd
    have hvale : boundaryLegId e' = boundaryLegId e := hval
    -- `e' ∈ δ.resolvedBoundaryEdges ⊆ (γ.bcrg).internalEdges = γ.internalEdges ⊆ G.internalEdges`
    obtain ⟨he'H, _⟩ := resolvedBoundaryEdges_mem.mp he'
    have he'γ : e' ∈ γ.internalEdges := by
      rwa [boundaryCompletedResolvedGraph_internalEdges] at he'H
    have he'G : e' ∈ G.internalEdges := Multiset.mem_of_le γ.internalEdges_le he'γ
    have hee : e' = e := boundaryLegId_injOn_of_edgeIdUnique hEdge he'G heG hvale
    -- so `e ∈ γ.internalEdges`: both endpoints inside `γ`, contradicting the boundary predicate
    rw [hee] at he'γ
    obtain ⟨hsrc, htgt⟩ := γ.edges_supported e he'γ
    rcases heBd with ⟨_, htn⟩ | ⟨hsn, _⟩
    · exact htn htgt
    · exact hsn hsrc

/-- **body-625 (Step 3, HEADLINE — the no-go).**  Whenever `δ` carries an inherited outer boundary edge
`e ∈ inheritedOuter γ δ`, the LOCAL nested completion `δ.boundaryCompletedResolvedGraph` and the ROOT direct
completion `(rootRelativeInner γ δ).boundaryCompletedResolvedGraph` have DIFFERENT resolved classes.  Equal
classes would give a relabeling `σ` with `R.bcrg = δ.bcrg.mapPerm σ`, hence equal `legId` profiles; but
`2e+1` is in the root profile and absent from the local profile.  `mapPerm` cannot absorb the difference, and
`EdgeIdsUnique` rules out an accidental proxy — a genuine second-order ID re-encoding obstruction, not a
vertex-relabeling artifact. -/
theorem phi4WTriplePrime_nestedLeft_class_ne_of_inheritedOuter (hEdge : G.EdgeIdsUnique)
    (γ : ResolvedFeynmanSubgraph G) (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    {e : ResolvedFeynmanEdge} (he : e ∈ inheritedOuter γ δ) :
    δ.boundaryCompletedResolvedGraph.toResolvedClass
      ≠ (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.toResolvedClass := by
  intro hclass
  have hiso : ResolvedFeynmanGraph.IsIso δ.boundaryCompletedResolvedGraph
      (rootRelativeInner γ δ).boundaryCompletedResolvedGraph := Quotient.exact hclass
  obtain ⟨π, hπ⟩ := hiso
  have hprof : phi4WTriplePrime_legIdProfile
        (rootRelativeInner γ δ).boundaryCompletedResolvedGraph
      = phi4WTriplePrime_legIdProfile δ.boundaryCompletedResolvedGraph := by
    rw [hπ, phi4WTriplePrime_legIdProfile_mapPerm]
  have hmemR := phi4WTriplePrime_boundaryLegId_mem_rootProfile γ δ he
  rw [hprof] at hmemR
  exact phi4WTriplePrime_boundaryLegId_not_mem_localProfile hEdge γ δ he hmemR

/-- **body-625 (Step 3, algebraic manifestation).**  The two per-occurrence left-factor generators are
UNEQUAL: `X(δ.boundaryCompletedResolvedGraph …) ≠ X((rootRelativeInner γ δ).boundaryCompletedResolvedGraph …)`
under an inherited boundary edge.  `MvPolynomial.X` is injective and the generator subtype is class-valued
(`toResolvedPhi4HopfGenBoundaryCompleted_val`), so generator equality would force class equality — refuted by
the headline.  This is exactly the per-occurrence factor mismatch that blocks the full left-factor product
identity: Branch B. -/
theorem phi4WTriplePrime_nestedLeft_gen_ne_of_inheritedOuter (hEdge : G.EdgeIdsUnique)
    (γ : ResolvedFeynmanSubgraph G) (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hCDloc : ∃ hWF : δ.boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent δ.boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily δ.boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self δ.boundaryCompletedResolvedGraph.forget hWF))
    (hCDroot : ∃ hWF : (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget.WellFormed,
      @FeynmanSubgraph.IsConnectedDivergent (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget
        (phi4DivergenceMeasureFamily (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget)
        (FeynmanSubgraph.self (rootRelativeInner γ δ).boundaryCompletedResolvedGraph.forget hWF))
    {e : ResolvedFeynmanEdge} (he : e ∈ inheritedOuter γ δ) :
    (MvPolynomial.X (δ.toResolvedPhi4HopfGenBoundaryCompleted hCDloc) : ResolvedPhi4HopfH)
      ≠ MvPolynomial.X ((rootRelativeInner γ δ).toResolvedPhi4HopfGenBoundaryCompleted hCDroot) := by
  intro hX
  have hgen := MvPolynomial.X_injective hX
  have hval := congrArg Subtype.val hgen
  rw [toResolvedPhi4HopfGenBoundaryCompleted_val, toResolvedPhi4HopfGenBoundaryCompleted_val] at hval
  exact phi4WTriplePrime_nestedLeft_class_ne_of_inheritedOuter hEdge γ δ he hval

end GaugeGeometry.QFT.Combinatorial
