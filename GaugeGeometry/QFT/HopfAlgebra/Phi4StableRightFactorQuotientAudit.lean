import GaugeGeometry.QFT.HopfAlgebra.Phi4StableSelectedOuterLeftFactor

/-!
# QFT-R1-body-633 — the STABLE local RIGHT factor + the stable algebraic root, and an OWNERSHIP AUDIT

Body-632 completed, on the STABLE carrier, the full LEFT-factor product `stableSelectedOuter_leftFactor_product`
that body-625's no-go DENIED on the old carrier.  The summand-agreement backbone needs THREE tensor factors:
the LEFT product (body-632 delivered it), the RIGHT product, and the OUTER RIGHT term (whose equality against
the two-stage quotient is the genuine Δᵣ-coassoc `quot_eq`).  This body delivers the **stable local right
factor** and re-emits body-624's **pure-tensor algebraic root** on the stable carrier — exposing EXACTLY those
three factors — then performs an honest **ownership audit** and a **`quot_eq` diagnostic**.

## Steps

* **Step 1 (MANDATORY) — the stable local right factor.**  `stableLocalRightFactor` mirrors body-624's
  `phi4EdgeCompleteLocalRightFactor` but on the STABLE carrier: `inl true ↦ 1`; `inl false ↦
  X (stableLocalBoundaryCompletedGraph γ)` (the inherited-verbatim stable generator); `inr B ↦
  stableForestRightTerm B.1 …` (the stable inner two-stage contraction term of body-629).  Three `[simp]`
  anchors.  NO bridge / cast to the frozen `phi4EdgeCompleteLocalRightFactor`.
* **Step 2 — the stable algebraic root.**  `StableResolvedPhi4HopfH3`; the pure-tensor
  `stableLocalChoiceTerm := LEFT ⊗ RIGHT`; the branch weight `stableSplitChoiceTerm`
  (`assoc ((∏γ localChoiceTerm) ⊗ outerRight)`); and the two pure-tensor factorizations
  `stableLocalChoiceTerm_factor` / `stableSplitChoiceTerm_factor` exposing LEFT PRODUCT / RIGHT PRODUCT /
  OUTER RIGHT.  A faithful stable-carrier mirror of body-624's `phi4WTriplePrime_splitChoiceTerm_factor`; the
  old-choice versions are NOT consumed.
* **Step 3 — ownership audit (in the docstring `AUDIT` block below).**
* **Step 4 — `quot_eq` diagnostic** (documented target; NOT proved here).
* **Step 5 — HONEST VERDICT: Branch B fired.**

## AUDIT (Step 3) — ownership of the stable RIGHT geometry

* **REUSABLE (stable-native, consumed here):** `stableForestRightTerm` (body-629 @455),
  `stableForestRightTerm_class_eq` (@466), `stableResolvedBoundaryIds_contractWithStars` (@419).  These are
  keyed purely on a `ResolvedAdmissibleSubgraph` over an arbitrary ambient + the stable certificate, so they
  apply to the stable inner ambient `stableLocalBoundaryCompletedGraph γ` and to `G` (outer) verbatim.
* **FROZEN-TYPE ONLY (FORBIDDEN to consume for the stable choice):**
  `phi4WTriplePrime_rightSurvivorForest` (603 @451), `phi4WTriplePrime_remnantForest` (605),
  `phi4WTriplePrime_quotientForest` (606 @94), `phi4WTriplePrime_remnant_rightTerm_eq` (605 @240).  Each is
  keyed on `s : Phi4EdgeCompleteFilteredCoassocSplitChoice G` (the OLD split choice) and lives in / is built
  from the OLD inner completion `γ.boundaryCompletedResolvedGraph` — e.g. the remnant's generator route runs
  `phi4WTriplePrimeCanonicalSupply.hCD o.γ.1.boundaryCompletedResolvedGraph o.B.1 o.B.2` (605 @58).  The stable
  choice's inner ambient is `stableLocalBoundaryCompletedGraph γ`, which is DEFINITIONALLY DIFFERENT from
  `γ.boundaryCompletedResolvedGraph`: it keeps the inherited legs VERBATIM (`γ.externalLegs +
  γ.resolvedBoundaryEdges.map γ.boundaryExternalLeg`) whereas the old one EVEN-re-encodes them
  (`encodeExistingLeg`).  The `legId` profile that separates them is exactly body-625's `mapPerm`-invariant
  no-go witness, so the two completions are NOT defeq — the frozen quotient geometry cannot be re-keyed onto
  the stable choice by unfolding.  Hence every 603-606 decl is frozen-TYPE-only for this body.
* **MISSING STABLE OWNERS (the named frontiers below):** `stableRightSurvivorForest`, `stableRemnantForest`,
  `stableQuotientForest`, and the stable two-stage contraction class equality.  None exist; none are fabricated.

## `quot_eq` diagnostic (Step 4) — the documented target, NOT proved here

The load-bearing OUTER-RIGHT identity is the two-stage contraction **class** equality
```
(stableSelectedOuter s).contractWithStars outerStar |>.toResolvedClass
  = (stableQuotientForest s).contractWithStars quotientStar |>.toResolvedClass
```
(with `stableQuotientForest` a FRONTIER, so this cannot even be stated yet).  Findings, recorded for body-637:
* **two-stage action.**  Vertices/internalEdges/externalLegs of both sides are read off `contractWithStars`
  (retarget of endpoints to the per-component star; complement edges retargeted; legs retargeted) — the two
  sides differ only in ambient (`G` vs the stable quotient ambient) and star assignment.
* **leg-ID profile.**  `stableResolvedBoundaryIds_contractWithStars` shows the contraction KEEPS every
  `edgeId`/`legId` (retarget touches endpoints only, never ids) and preserves the ODD-boundary disjointness.
  The stable carrier's whole reason to exist (body-629) is that inherited leg ids are NOT re-encoded, so the
  two-stage route inherits ids VERBATIM — the profile that broke the old carrier is stable here.
* **inherited-ID preservation.**  Confirmed: no re-encode on either stage (stable completion is verbatim;
  contraction is retarget-only).
* **correcting permutation.**  Only the vertex-COORDINATE difference (which star each surviving vertex maps to)
  is left after ids are matched; that difference is exactly what a correcting `Equiv.Perm VertexId` on the
  quotient ambient absorbs — a CLASS equality (`toResolvedClass`), never strict canonical-star equality.
* **local→global injectivity.**  The needed fact — that the per-component local star permutations bundle into a
  single global `σ` — does NOT exist stable-natively.  In the abstract arc it was the whole 511/519–529
  `contract_class_eq` campaign (three whole-graph field equalities + a globally assembled `σ`), every piece
  carrying forbidden abstract/divergence machinery.  No φ⁴ family-native, instance-free version exists, and the
  frozen witnesses are keyed on the OLD choice (see AUDIT).  This is the STOP.

## VERDICT — Branch B (EXPECTED)

The stable quotient geometry is NOT re-keyable instance-free from existing raw theorems: the 603-606 quotient
owners are frozen-TYPE-only (old choice + old ambient, not defeq to `stableLocalBoundaryCompletedGraph`), and
no stable two-stage class equality / local→global injectivity exists.  So Branch A is impossible without
fabrication.  We deliver Steps 1-2 (the stable right factor + the stable algebraic root, exposing the three
summand factors) and NAME the next frontiers, then STOP:
```
634 stable right-survivor forest ; 635 stable remnant + quotient forest ; 636 stable right-factor aggregate ;
637 stable two-stage quot_eq ; 638 summand agreement
```

## HALT / red lines
body-625's no-go and bodies 629-632 are UNEDITED; the OLD carrier / coproduct / split choice are FROZEN.  NO
cast / adapter to the old split choice; NO frozen generator equality consumed; the frozen-type-only 603-606
decls are NOT consumed as terms.  Right-factor AGGREGATE / `quot_eq` / summand agreement / `sum_bij` / alpha /
coassoc are NOT entered.  ZERO forbidden divergence classes in any declaration TYPE; ZERO new `class` /
permanent `instance` (one file-local `local instance` for the φ⁴ family); ZERO new `structure`; ZERO `sorry` /
`admit` / `native_decide`; NO public `HEq` / `cast` / graph-data `▸`; NO `toFinset` / dedup / orbit quotient.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped TensorProduct
open scoped Classical

open ResolvedFeynmanSubgraph

variable {G : ResolvedFeynmanGraph}

/-- The ONLY instance in this file: the concrete φ⁴ divergence measure family (mirrors body-629/632), so the
resolved admissible-subgraph / carrier plumbing elaborates against the φ⁴ family. -/
local instance instPhi4DivergenceMeasureFamily633 : ∀ H : FeynmanGraph, DivergenceMeasure H :=
  phi4DivergenceMeasureFamily

/-! ## Step 1 — the stable local RIGHT factor (MANDATORY) -/

/-- **body-633 (Step 1) — the stable local right factor.**  The stable-carrier mirror of body-624's
`phi4EdgeCompleteLocalRightFactor`: on `Sum.inl true` the unit `1`; on `Sum.inl false` the boundary-completed
stable generator; on `Sum.inr B` the stable inner two-stage contraction term `stableForestRightTerm` (body-629)
over the STABLE inner ambient `stableLocalBoundaryCompletedGraph γ`.  Lands in `StableResolvedPhi4HopfH`.  NO
cast / Equiv / bridge to the frozen `phi4EdgeCompleteLocalRightFactor`. -/
noncomputable def stableLocalRightFactor {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    (Bool ⊕ StableLocalForestIdx γ) → StableResolvedPhi4HopfH :=
  Sum.elim
    (fun b => bif b then (1 : StableResolvedPhi4HopfH)
      else MvPolynomial.X ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
        (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
        (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)))
    (fun B => stableForestRightTerm B.1
      (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph γ) B.1)
      (phi4WTriplePrimeCanonicalSupply.hCD (stableLocalBoundaryCompletedGraph γ) B.1 B.2)
      (stableResolvedBoundaryIds_contractWithStars B.1
        (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph γ) B.1)
        (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)))

/-- **body-633 (Step 1) — the LEFT-primitive branch value (`1`).** -/
@[simp] theorem stableLocalRightFactor_inl_true {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G) (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    stableLocalRightFactor hSt γ hCDγ (Sum.inl true) = (1 : StableResolvedPhi4HopfH) := rfl

/-- **body-633 (Step 1) — the RIGHT-primitive branch value** (the boundary-completed stable generator). -/
@[simp] theorem stableLocalRightFactor_inl_false {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G) (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget) :
    stableLocalRightFactor hSt γ hCDγ (Sum.inl false)
      = MvPolynomial.X ((stableLocalBoundaryCompletedGraph γ).toStableResolvedPhi4HopfGen
          (stableLocalBoundaryCompletedGraph_exists_self_isConnectedDivergent γ hCDγ)
          (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)) := rfl

/-- **body-633 (Step 1) — the FOREST branch value** (the stable inner two-stage contraction term). -/
@[simp] theorem stableLocalRightFactor_inr {G : ResolvedFeynmanGraph}
    (hSt : StableResolvedBoundaryIds G) (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget)
    (B : StableLocalForestIdx γ) :
    stableLocalRightFactor hSt γ hCDγ (Sum.inr B)
      = stableForestRightTerm B.1
          (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph γ) B.1)
          (phi4WTriplePrimeCanonicalSupply.hCD (stableLocalBoundaryCompletedGraph γ) B.1 B.2)
          (stableResolvedBoundaryIds_contractWithStars B.1
            (phi4WTriplePrimeCanonicalSupply.starOf (stableLocalBoundaryCompletedGraph γ) B.1)
            (stableResolvedBoundaryIds_stableLocalBoundaryCompletedGraph γ hSt)) := rfl

/-! ## Step 2 — the stable algebraic root (mirror of body-624's pure tensor algebra) -/

/-- **body-633 (Step 2) — the stable φ⁴ triple-tensor codomain.** -/
noncomputable abbrev StableResolvedPhi4HopfH3 : Type :=
  StableResolvedPhi4HopfH ⊗[ℚ] (StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH)

/-- **body-633 (Step 2) — the stable local choice term** as the pure tensor `LEFT ⊗ RIGHT` (LEFT via body-632's
`stableLocalLeftFactor`, RIGHT via Step 1's `stableLocalRightFactor`). -/
noncomputable def stableLocalChoiceTerm {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget)
    (c : Bool ⊕ StableLocalForestIdx γ) :
    StableResolvedPhi4HopfH ⊗[ℚ] StableResolvedPhi4HopfH :=
  stableLocalLeftFactor hSt γ hCDγ c ⊗ₜ[ℚ] stableLocalRightFactor hSt γ hCDγ c

/-- **body-633 (Step 2) — the stable local choice term IS the pure tensor of its two factors** (by definition;
the family-native mirror of body-624's `phi4EdgeCompleteLocalChoiceTerm_factor`). -/
theorem stableLocalChoiceTerm_factor {G : ResolvedFeynmanGraph} (hSt : StableResolvedBoundaryIds G)
    (γ : ResolvedFeynmanSubgraph G)
    (hCDγ : @FeynmanSubgraph.IsConnectedDivergent G.forget (phi4DivergenceMeasureFamily G.forget) γ.forget)
    (c : Bool ⊕ StableLocalForestIdx γ) :
    stableLocalChoiceTerm hSt γ hCDγ c
      = stableLocalLeftFactor hSt γ hCDγ c ⊗ₜ[ℚ] stableLocalRightFactor hSt γ hCDγ c := rfl

/-- **body-633 (Step 2) — product of pure tensors factors** (commutative tensor ring; the stable-carrier mirror
of body-624's `phi4_prod_tmul_factor`, re-proved because body-624 is NOT in this import branch). -/
theorem stable_prod_tmul_factor {ι : Type*} (s : Finset ι)
    (f g : ι → StableResolvedPhi4HopfH) :
    (∏ x ∈ s, (f x ⊗ₜ[ℚ] g x)) = (∏ x ∈ s, f x) ⊗ₜ[ℚ] (∏ x ∈ s, g x) := by
  classical
  induction s using Finset.induction with
  | empty => exact Algebra.TensorProduct.one_def
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

/-- **body-633 (Step 2) — the stable split-choice branch weight** in `StableResolvedPhi4HopfH3`.  The
associated `((∏γ stableLocalChoiceTerm) ⊗ outerRight)`, where the OUTER RIGHT term is the stable two-stage
outer contraction `stableForestRightTerm s.outer …` — the load-bearing `quot_eq` factor.  The stable-carrier
mirror of body-624's `phi4WTriplePrime_splitChoiceTerm`. -/
noncomputable def stableSplitChoiceTerm {G : ResolvedFeynmanGraph} {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) : StableResolvedPhi4HopfH3 :=
  (Algebra.TensorProduct.assoc ℚ ℚ ℚ StableResolvedPhi4HopfH StableResolvedPhi4HopfH
      StableResolvedPhi4HopfH).toAlgHom
    ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach,
        stableLocalChoiceTerm hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
          (s.choice γ (Finset.mem_attach _ γ)))
      ⊗ₜ[ℚ] stableForestRightTerm s.outer
        (phi4WTriplePrimeCanonicalSupply.starOf G s.outer)
        (phi4WTriplePrimeCanonicalSupply.hCD G s.outer s.outer_mem)
        (stableResolvedBoundaryIds_contractWithStars s.outer
          (phi4WTriplePrimeCanonicalSupply.starOf G s.outer) hSt))

/-- **body-633 (Step 2, HEADLINE) — the stable split-term tensor factorization.**  Exposes EXACTLY the three
summand factors: the LEFT PRODUCT `∏ stableLocalLeftFactor`, the RIGHT PRODUCT `∏ stableLocalRightFactor`, and
the OUTER RIGHT `stableForestRightTerm s.outer …` (the `quot_eq` target).  Pure algebra — the family-native
stable-carrier mirror of body-624's `phi4WTriplePrime_splitChoiceTerm_factor`. -/
theorem stableSplitChoiceTerm_factor {G : ResolvedFeynmanGraph} {hSt : StableResolvedBoundaryIds G}
    (s : StablePhi4ResolvedSplitChoice G hSt) :
    stableSplitChoiceTerm s
      = (∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach,
            stableLocalLeftFactor hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
              (s.choice γ (Finset.mem_attach _ γ)))
        ⊗ₜ[ℚ]
          ((∏ γ ∈ (@ResolvedAdmissibleSubgraph.elements phi4DivergenceMeasureFamily G s.outer).attach,
              stableLocalRightFactor hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
                (s.choice γ (Finset.mem_attach _ γ)))
            ⊗ₜ[ℚ] stableForestRightTerm s.outer
              (phi4WTriplePrimeCanonicalSupply.starOf G s.outer)
              (phi4WTriplePrimeCanonicalSupply.hCD G s.outer s.outer_mem)
              (stableResolvedBoundaryIds_contractWithStars s.outer
                (phi4WTriplePrimeCanonicalSupply.starOf G s.outer) hSt)) := by
  unfold stableSplitChoiceTerm
  rw [Finset.prod_congr rfl (fun γ _ =>
      stableLocalChoiceTerm_factor hSt γ.1 (s.outer.isConnectedDivergent γ.1 γ.2)
        (s.choice γ (Finset.mem_attach _ γ))),
    stable_prod_tmul_factor, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    Algebra.TensorProduct.assoc_tmul]

end GaugeGeometry.QFT.Combinatorial
