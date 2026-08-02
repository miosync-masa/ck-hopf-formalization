import GaugeGeometry.QFT.HopfAlgebra.Phi4WTriplePrimeEdgeCompleteCarrier

/-!
# QFT-R1-body-653a — the marginal root-relative defect criterion (generic core of the W‴ ⊊ W″ counterexample)

Body-599 measured, and body-600 discharged, the *hidden root boundary* deficit of the stable nested
root lift `R := rootRelativeInner γ δ`.  The load-bearing unconditional identity was

```text
ωφ4(R.forget) = ωφ4(δ.forget) − |hiddenRootBoundary γ δ|        (body-599, degree correction)
```

and the fifth axis `ResolvedInternalEdgeComplete γ` forces `hiddenRootBoundary γ δ = 0` (body-600).  The
finite fifth-axis index `phi4WTriplePrimeIndex` (W‴) is the W″ index `phi4WDoublePrimeIndex` FURTHER
filtered by forest-level internal-edge completeness.

This body extracts the **physics content** of that measured deficit as a clean, reusable criterion:

* **Step 1 (HEADLINE, generic).**  When the inner component is *marginal* (`ωφ4(δ.forget) = 0`, the
  logarithmically-divergent φ⁴ triangle), the root-relative reconstruction `R.forget` is divergent iff
  the lift is boundary-closed — equivalently iff the hidden root boundary vanishes:

  ```text
  R.forget.IsDivergent  ↔  RootRelativeBoundaryClosed γ δ  ↔  hiddenRootBoundary γ δ = 0.
  ```

  Under the φ⁴ family, `ωφ4(δ.forget) = 0` gives `ωφ4(R.forget) = −|hiddenRootBoundary γ δ|`, so a
  *single* hidden root edge already tips a marginal inner diagram into the convergent regime.  The W‴
  edge-completeness condition (body-600) is precisely what discharges the defect
  (`rootRelativeInner_isDivergent_of_marginal_edgeComplete`); a forest that omits a hidden root edge is
  exactly the excluded one (`..._not_isDivergent_of_marginal_of_hiddenRootBoundary_ne`).

* **General inclusion.**  `phi4WTriplePrimeIndex G ⊆ phi4WDoublePrimeIndex G` — W‴ only ever adds the
  edge-completeness conjunct on top of W″ (`Finset.filter_subset`).

## Figure 1 (the target concrete instance, realized in 653b)

> A marginal inner triangle has four visible boundary edges in the W″ ambient, while two omitted root
> edges remain invisible.  Root-relative reconstruction exposes six boundary edges, shifting the
> superficial degree from 0 to −2.  The W‴ edge-completeness condition excludes precisely this forest.

## HALT compliance

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only); ZERO forbidden divergence classes
(`IsPermInvariantDivergence` / `IsIsoInvariantDivergence` / `IsAmbientInvariantDivergence` /
`IsDivergencePreservedByContract` / `...ByAdmissibleForestContract` /
`IsDivergenceReflectedByAdmissibleForestContract`) in ANY declaration's type — the only
divergence-flavoured binders are the concrete φ⁴ family and the `ResolvedExternalLegSaturated` /
`RootRelativeBoundaryClosed` / `ResolvedInternalEdgeComplete` predicates.  Multiplicity-safe throughout
(`Multiset`, no `Finset`/dedup).  No coproduct / body-556 / evaluation map; no `HEq` / `cast` / graph
`▸`; no new `structure` / `class` (one file-local `local instance` providing the concrete φ⁴ measure per
graph so that `.IsDivergent` resolves — never registered globally).  W‴ is NOT claimed to equal the
defect-zero sector, and `defect = 0 → edge-complete` is NOT claimed; the criterion is a two-way iff about
`RootRelativeBoundaryClosed`, with edge-completeness only ever a *sufficient* discharge (body-600).

## SPLIT NOTE (honest partial)

653a delivers the GENERIC marginal criterion + the general W‴ ⊆ W″ inclusion (all fully proved,
axiom-clean).  The CONCRETE named 12-edge φ⁴ graph (`{a01,a12,a20,b34,b45,b53,c04,c15,c25,c23,h03,h14}`),
its exact `hiddenRootBoundary = {h03,h14}` computation, the four concrete degrees `ω(G)=4, ω(γ)=4,
ω(δ)=0, ω(R)=−2`, the topology (connected / 1PI), the live W″ membership, the W‴ edge-completeness
FAILURE at `h03`, and the strictness witness `exists_mem_wDoublePrime_not_mem_wTriplePrime` remain for
653b (which imports this file).  Two genuine reasons for the split: (a) the boundary multisets
(`resolvedBoundaryEdges` / `newRootBoundary` / `hiddenRootBoundary`) are `noncomputable` Classical
filters, so the concrete degree / hidden-multiset facts require per-edge `count_filter` reasoning rather
than `decide`; (b) W″ membership requires the full `ResolvedAdmissibleSubgraphFor` packaging plus a
connected-divergent-in-the-φ⁴-family proof for the concrete ambient.  Neither is faked here.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

open ResolvedFeynmanSubgraph

set_option linter.unusedVariables false

variable {G : ResolvedFeynmanGraph}

/-- **body-653a — file-local φ⁴ divergence-measure family instance.**  Makes `.IsDivergent` (which needs a
`DivergenceMeasure` instance) resolve to the concrete φ⁴ measure per graph, whose `degree` field is
`phi4SuperficialDegree`.  This is the same *value* used everywhere in the QFT-R1 development
(`phi4DivergenceMeasureFamily`); it is registered ONLY as a `local instance` in this file, never
globally, so instance resolution elsewhere is unaffected. -/
local instance instPhi4DivergenceMeasureFamily653 :
    (H : FeynmanGraph) → DivergenceMeasure H := phi4DivergenceMeasureFamily

/-! ## The φ⁴ divergence bridge -/

/-- **body-653a — φ⁴ divergence of a forgotten resolved subgraph is nonnegativity of its φ⁴ superficial
degree.**  Under the file-local φ⁴ measure the abstract Weinberg criterion `0 ≤ divergenceDegree` is
definitionally `0 ≤ phi4SuperficialDegree` (the measure's `degree` field IS `phi4SuperficialDegree`). -/
theorem phi4Forget_isDivergent_iff_degree_nonneg {H : ResolvedFeynmanGraph}
    (η : ResolvedFeynmanSubgraph H) :
    η.forget.IsDivergent ↔ 0 ≤ η.forget.phi4SuperficialDegree := Iff.rfl

/-! ## Step 1 — the generic marginal criterion (HEADLINE) -/

/-- **body-653a (Step 1, HEADLINE) — marginal root-relative divergence criterion.**  If the inner
component `δ` is externally-leg saturated and *marginal* (`ωφ4(δ.forget) = 0`), then the root-relative
reconstruction `R = rootRelativeInner γ δ` is φ⁴-divergent iff the nested lift is boundary-closed.
Derived from the body-599 UNCONDITIONAL degree correction `ωφ4(R.forget) = ωφ4(δ.forget) − |hidden|`:
with `ωφ4(δ.forget) = 0` the degree is exactly `−|hiddenRootBoundary γ δ|`, so nonnegativity forces the
hidden-boundary multiset to have card `0`, i.e. to vanish, i.e. `RootRelativeBoundaryClosed γ δ`. -/
theorem rootRelativeInner_isDivergent_iff_boundaryClosed_of_marginal
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hMarg : δ.forget.phi4SuperficialDegree = 0) :
    (rootRelativeInner γ δ).forget.IsDivergent ↔ RootRelativeBoundaryClosed γ δ := by
  rw [phi4Forget_isDivergent_iff_degree_nonneg,
    phi4SuperficialDegree_rootRelativeInner_eq γ δ hγsat hδsat, hMarg]
  have hcard : (0 ≤ (0 : Int) - ((hiddenRootBoundary γ δ).card : Int))
      ↔ (hiddenRootBoundary γ δ).card = 0 := by omega
  rw [hcard, Multiset.card_eq_zero]
  exact Iff.rfl

/-- **body-653a (Step 1, defect form) — the same criterion phrased on the hidden root boundary directly.**
`RootRelativeBoundaryClosed γ δ` unfolds to `hiddenRootBoundary γ δ = 0`, so this is the criterion in the
`|hidden|`-exposed form used by the Figure-1 defect. -/
theorem rootRelativeInner_isDivergent_iff_hiddenRootBoundary_zero
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hMarg : δ.forget.phi4SuperficialDegree = 0) :
    (rootRelativeInner γ δ).forget.IsDivergent ↔ hiddenRootBoundary γ δ = 0 :=
  rootRelativeInner_isDivergent_iff_boundaryClosed_of_marginal γ δ hγsat hδsat hMarg

/-! ## Step 1 corollaries — the fifth-axis discharge and the physics defect -/

/-- **body-653a (Step 1, discharge) — a marginal edge-complete lift reconstructs to a divergent graph.**
Internal-edge completeness of `γ` (the W‴ fifth axis) discharges the boundary-closed gate (body-600), so
a marginal inner triangle inside an edge-complete outer component reconstructs to a genuinely divergent
root graph. -/
theorem rootRelativeInner_isDivergent_of_marginal_edgeComplete
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hMarg : δ.forget.phi4SuperficialDegree = 0)
    (hEC : ResolvedInternalEdgeComplete γ) :
    (rootRelativeInner γ δ).forget.IsDivergent :=
  (rootRelativeInner_isDivergent_iff_boundaryClosed_of_marginal γ δ hγsat hδsat hMarg).mpr
    (rootRelativeBoundaryClosed_of_edgeComplete γ δ hEC)

/-- **body-653a (Step 1, DEFECT) — a marginal lift with a nonempty hidden root boundary is NOT
divergent.**  This is the Figure-1 physics defect in generic form: whenever the outer component omits
some root-crossing edge (`hiddenRootBoundary γ δ ≠ 0`) so that its endpoints become visible boundary
edges only at root coordinates, a marginal inner triangle reconstructs to a *convergent* root graph — the
superficial degree has dropped below zero.  A forest exhibiting this is exactly the one W‴
edge-completeness excludes. -/
theorem rootRelativeInner_not_isDivergent_of_marginal_of_hiddenRootBoundary_ne
    (γ : ResolvedFeynmanSubgraph G)
    (δ : ResolvedFeynmanSubgraph γ.boundaryCompletedResolvedGraph)
    (hγsat : ResolvedExternalLegSaturated G γ)
    (hδsat : ResolvedExternalLegSaturated γ.boundaryCompletedResolvedGraph δ)
    (hMarg : δ.forget.phi4SuperficialDegree = 0)
    (hHid : hiddenRootBoundary γ δ ≠ 0) :
    ¬ (rootRelativeInner γ δ).forget.IsDivergent := by
  rw [rootRelativeInner_isDivergent_iff_hiddenRootBoundary_zero γ δ hγsat hδsat hMarg]
  exact hHid

/-! ## General W‴ ⊆ W″ inclusion -/

/-- **body-653a — the general fifth-axis inclusion.**  The φ⁴ W‴ index is contained in the φ⁴ W″ index:
W‴ is by construction the W″ index further `filter`ed by forest-level internal-edge completeness, so
membership only ever ADDS the edge-completeness conjunct.  (The *strict* inclusion — a concrete forest in
W″ but not W‴ — is the 653b concrete witness.) -/
theorem phi4WTriplePrimeIndex_subset_wDoublePrime (G : ResolvedFeynmanGraph) :
    phi4WTriplePrimeIndex G ⊆ phi4WDoublePrimeIndex G := by
  unfold phi4WTriplePrimeIndex phi4WDoublePrimeIndex resolvedEdgeCompleteIndexFor
  exact Finset.filter_subset _ _

end GaugeGeometry.QFT.Combinatorial
