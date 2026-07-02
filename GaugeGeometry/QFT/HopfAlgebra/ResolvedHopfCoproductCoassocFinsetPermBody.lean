import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocPermExtensionConcrete
import Mathlib.Logic.Equiv.Fintype

/-!
# R-6c-body-18 — a Finset-subtype equivalence extends to a global permutation

Eighteenth genuine-body step, discharging the one NON-local but purely combinatorial leaf: the generic
`FinsetSubtypePermExtensionSupply s t e` (leaf-35).  Given `e : {x // x ∈ s} ≃ {x // x ∈ t}`, we produce a
global `Equiv.Perm α` that restricts to `e.symm` on `t` and (via `perm.symm`) to `e` on `s`.

Mathlib's `Equiv.extendSubtype` extends a subtype equiv to a permutation, but only for a **finite** ambient
type; `α` here (`VertexId`) is infinite.  The fix: `s ∪ t` is a `Finset`, so its coercion `↥(s ∪ t)` IS finite.
We

1. reflect `e` onto the finite carrier `↥(s ∪ t)` as `e'' : {y // y.1 ∈ t} ≃ {y // y.1 ∈ s}` (via
   `Equiv.subtypeSubtypeEquivSubtype`, since `t, s ⊆ s ∪ t`), oriented so the perm acts as `e.symm` on `t`;
2. run `Equiv.extendSubtype` on the finite `↥(s ∪ t)` to get `φ : Perm ↥(s ∪ t)`;
3. lift `φ` to `Perm α` by the identity outside `s ∪ t` (`Equiv.Perm.subtypeCongr φ (Equiv.refl _)`).

`on_t` is the genuine content (unfold the three-step chain: `left_apply` → `extendSubtype_apply_of_mem` →
`subtypeSubtypeEquivSubtype` apply/symm_apply); `symm_on_s` then follows from `on_t` by injectivity —
`perm ((e ⟨v,hv⟩).1) = v` (since `(e ⟨v,hv⟩).1 ∈ t` and `e.symm (e ⟨v,hv⟩) = ⟨v,hv⟩`), so
`perm.symm v = (e ⟨v,hv⟩).1`.  No computation of `φ.symm` is needed.

Per the HALT, this is pure combinatorics (no geometry); `retarget` / `parent_inj` are untouched.

Landed:

* `finsetSubtypeExtensionPerm s t e : Equiv.Perm α` — the lifted permutation;
* `finsetSubtypePermExtension s t e : FinsetSubtypePermExtensionSupply s t e` — the supply (leaf-35 closed).

No facade, no flat term, no `forgetHopf`.
-/

namespace GaugeGeometry.QFT.Combinatorial

open Equiv

variable {α : Type*} [DecidableEq α]

/-- **R-6c-body-18 — the subtype equivalence `e` reflected onto the finite carrier `↥(s ∪ t)`**, oriented so
the extended permutation acts as `e.symm` on `t`. -/
noncomputable def finsetSubtypeCarrierEquiv (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) :
    {y : {x // x ∈ s ∪ t} // y.1 ∈ t} ≃ {y : {x // x ∈ s ∪ t} // y.1 ∈ s} :=
  (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ s ∪ t)) (q := (· ∈ t))
      (fun {_} hx => Finset.mem_union.mpr (Or.inr hx))).trans
    (e.symm.trans
      (Equiv.subtypeSubtypeEquivSubtype (p := (· ∈ s ∪ t)) (q := (· ∈ s))
        (fun {_} hx => Finset.mem_union.mpr (Or.inl hx))).symm)

/-- **R-6c-body-18 — the global permutation extending a Finset-subtype equivalence.**  Built on the finite
carrier `↥(s ∪ t)` via `Equiv.extendSubtype`, lifted to `α` by the identity outside `s ∪ t`. -/
noncomputable def finsetSubtypeExtensionPerm (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) : Equiv.Perm α :=
  Perm.subtypeCongr (finsetSubtypeCarrierEquiv s t e).extendSubtype (Equiv.refl _)

/-- **R-6c-body-18 — `finsetSubtypeExtensionPerm` restricts to `e.symm` on `t`. -/
theorem finsetSubtypeExtensionPerm_on_t (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) {v : α} (hv : v ∈ t) :
    finsetSubtypeExtensionPerm s t e v = (e.symm ⟨v, hv⟩).1 := by
  have hvU : v ∈ s ∪ t := Finset.mem_union.mpr (Or.inr hv)
  rw [finsetSubtypeExtensionPerm, Perm.subtypeCongr.left_apply _ _ hvU,
    Equiv.extendSubtype_apply_of_mem (finsetSubtypeCarrierEquiv s t e) ⟨v, hvU⟩ hv]
  rfl

/-- **R-6c-body-18 — the generic Finset-subtype permutation extension** (leaf-35 closed). -/
noncomputable def finsetSubtypePermExtension (s t : Finset α)
    (e : {x // x ∈ s} ≃ {x // x ∈ t}) :
    FinsetSubtypePermExtensionSupply s t e where
  perm := finsetSubtypeExtensionPerm s t e
  on_t := fun {v} hv => finsetSubtypeExtensionPerm_on_t s t e hv
  symm_on_s := fun {v} hv => by
    have hu : (e ⟨v, hv⟩).1 ∈ t := (e ⟨v, hv⟩).2
    have key : finsetSubtypeExtensionPerm s t e ((e ⟨v, hv⟩).1) = v := by
      rw [finsetSubtypeExtensionPerm_on_t s t e hu]
      have : (⟨(e ⟨v, hv⟩).1, hu⟩ : {x // x ∈ t}) = e ⟨v, hv⟩ := Subtype.ext rfl
      rw [this, e.symm_apply_apply]
    rw [Equiv.symm_apply_eq]
    exact key.symm

end GaugeGeometry.QFT.Combinatorial
