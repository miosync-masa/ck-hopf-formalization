import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocForgetUnion
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproductIndex
import GaugeGeometry.QFT.HopfAlgebra.ResolvedCoproduct

/-!
# R-6c-body-232 — canonical membership certificate + `cert_mem` adapter (PROVED)

Two-hundred-and-thirty-second genuine-body step — the reshaping adapter body-230's scout designed.  A constructed
resolved forest `A` lies in a canonical cover's carrier as soon as it carries a **membership certificate**: it is a
proper forest, and it is the *unique* proper forest with its forgetful image among the carrier members (the generic
form of the section / canonicality condition).  The adapter `cert_mem` is **proved** outright against the generic
`ResolvedProperForestFiniteCover` interface (`forget_complete` + `forget_injective`, `ResolvedCoproduct.lean:243`).

## The certificate

For a canonical cover `C : ResolvedProperForestFiniteCover G` and a constructed forest `A`:

```lean
structure ResolvedCanonicalMembershipCertificate (C) (A) where
  isProper     : A.IsProperForest
  recovered_eq : ∀ Ares ∈ C.index.carrier, Ares.forget = A.forget → Ares = A
```

* `isProper` — the five `IsProperForest` conjuncts (still open for `selectedOuterRawOf` / the region union, per body-230);
* `recovered_eq` — the **section condition** in generic form: `A` is the unique carrier member with its forget.  For
  the `ofForgetForest`-image carrier this is exactly `A = ofForgetForest A.forget` (body-230's `isCanonical`), phrased
  without naming `ofForgetForest` so it works against any cover.

## The adapter (proved)

`cert_mem` composes the cover interface: `isProper` puts `A.forget` in the flat index filter
(`forget_mem_properDisjoint_filter_complement`, `ResolvedCoproductIndex.lean:222`); `forget_complete` recovers *some*
carrier member `Ares` with `Ares.forget = A.forget`; `recovered_eq` identifies `Ares = A`; so `A ∈ carrier`.  This is
why the certificate needs `recovered_eq` and not just `isProper` — `forget_complete` gives existence, and `forget`
is not globally injective (body-230), so the identification must be supplied.

## What this settles

* **128 / 159 can now be supplied by one certificate each** — `selectedOuter_mem` (128) and `recovered_outer_mem`
  (159) become `cert_mem` applied to `selectedOuterRawOf s` / the region union, given a certificate for each.  The
  residual is exactly the two certificate fields: `isProper` (five conjuncts) and `recovered_eq` (the section).
* **`forget_union_elements` (body-231)** is the tool a later body uses to *build* those certificates: it computes
  `(A.union B).forget.elements`, needed both for `isProper`'s complement/internal-edge conjuncts and to match
  `recovered_eq`'s `Ares.forget = A.forget` on the constructed unions.

Per the HALT: no `selectedOuter` / `recoveredOuter`-specific proof, no `isProper` conjunct, no `recovered_eq` proof is
entered — only the generic schema and the `cert_mem` adapter, which is proved.  No facade, no flat term, no
`forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

variable [∀ G : FeynmanGraph, DivergenceMeasure G]
  [∀ G : FeynmanGraph, IsPermInvariantDivergence G]
  [∀ G : FeynmanGraph, IsIsoInvariantDivergence G]
  [∀ G : FeynmanGraph, Fintype (FeynmanSubgraph G)]
  [IsAmbientInvariantDivergence]
  [IsDivergencePreservedByContract]
  [IsDivergencePreservedByAdmissibleForestContract]

variable {G : ResolvedFeynmanGraph}

set_option linter.unusedSectionVars false

/-- **R-6c-body-232 — a canonical membership certificate for a constructed forest.**  `A` is a proper forest and the
unique carrier member with its forgetful image (the section / canonicality condition, generically phrased). -/
structure ResolvedCanonicalMembershipCertificate (C : ResolvedProperForestFiniteCover G)
    (A : ResolvedAdmissibleSubgraph G) where
  /-- `A` is a proper forest (the five `IsProperForest` conjuncts). -/
  isProper : A.IsProperForest
  /-- The section condition: `A` is the unique carrier member with its forgetful image. -/
  recovered_eq : ∀ Ares ∈ C.index.carrier, Ares.forget = A.forget → Ares = A

/-- **R-6c-body-232 — the membership adapter, PROVED.**  A certified constructed forest lies in the canonical carrier:
`forget_complete` recovers a carrier member sharing `A`'s forget, and `recovered_eq` identifies it with `A`. -/
theorem cert_mem {C : ResolvedProperForestFiniteCover G} {A : ResolvedAdmissibleSubgraph G}
    (cert : ResolvedCanonicalMembershipCertificate C A) : A ∈ C.index.carrier := by
  obtain ⟨Ares, hmem, hforget⟩ :=
    C.forget_complete A.forget
      (ResolvedAdmissibleSubgraph.forget_mem_properDisjoint_filter_complement A cert.isProper)
  have hEq : Ares = A := cert.recovered_eq Ares hmem hforget
  rw [← hEq]; exact hmem

/-- **R-6c-body-232 — certificate → membership**, the method form for supplying `selectedOuter_mem` (128) /
`recovered_outer_mem` (159) from a single certificate. -/
theorem ResolvedCanonicalMembershipCertificate.mem {C : ResolvedProperForestFiniteCover G}
    {A : ResolvedAdmissibleSubgraph G} (cert : ResolvedCanonicalMembershipCertificate C A) :
    A ∈ C.index.carrier :=
  cert_mem cert

end GaugeGeometry.QFT.Combinatorial
