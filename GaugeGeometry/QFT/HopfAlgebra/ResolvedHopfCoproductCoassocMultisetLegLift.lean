import GaugeGeometry.QFT.HopfAlgebra.ResolvedHopfCoproductCoassocMultiStarValueCore

/-!
# R-6c-body-375 — bank-3a: the generic multiset lifting for the leg socket (PROVED)

Three-hundred-and-seventy-fifth genuine-body step — the reusable combinatorial core the `legLift` reduction turns on.
Mathlib has `map_le_map_iff` only for INJECTIVE `f`; the leg-lift `retargetExternalLeg` is not injective, so the
preimage lift `R ≤ S.map f → ∃ L ≤ S, L.map f = R` must be banked independently.

`multiset_exists_le_of_le_map` — proved by induction on `S` (cons / not-mem split).  It is exactly the "generic
multiset lifting" step 3 of the `legLift`-from-`touchedLegComplete` reduction: the residual legs `R` under the touched
retarget lift to an honest preimage `L ≤ S`.

Landed axiom-clean: `multiset_exists_le_of_le_map`.

Per the HALT: only the generic multiset lifting is banked here (the leg-socket's reusable core); the
`touchedLegLiftDatum_of_complete` construction (which consumes it) and the `valueCore_of_legComplete` are the next
step; no `Classical.choose` preimage is assumed to satisfy `touched_le`; `parentCD` stays an honest power-counting
input; no carrier / `innerRaw_mem`.  No facade, no flat term, no `forgetHopf`, no rep/perm, and NO `promote_collapse`
/ singleton / floor-297.
-/

namespace GaugeGeometry.QFT.Combinatorial

open scoped Classical

/-- **R-6c-body-375 — generic multiset preimage lift** (non-injective `f`).  A sub-multiset of `S.map f` is itself
the image of a sub-multiset of `S`. -/
theorem multiset_exists_le_of_le_map {α β : Type*} {f : α → β} :
    ∀ {S : Multiset α} {R : Multiset β}, R ≤ S.map f → ∃ L, L ≤ S ∧ L.map f = R := by
  intro S
  induction S using Multiset.induction with
  | empty =>
    intro R h
    rw [Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨0, le_refl _, by rw [h, Multiset.map_zero]⟩
  | cons b S' ih =>
    intro R h
    rw [Multiset.map_cons] at h
    by_cases hb : f b ∈ R
    · obtain ⟨R', rfl⟩ := Multiset.exists_cons_of_mem hb
      obtain ⟨L', hL', hLeq⟩ := ih ((Multiset.cons_le_cons_iff (f b)).mp h)
      exact ⟨b ::ₘ L', Multiset.cons_le_cons b hL', by rw [Multiset.map_cons, hLeq]⟩
    · obtain ⟨L', hL', hLeq⟩ := ih ((Multiset.le_cons_of_notMem hb).mp h)
      exact ⟨L', le_trans hL' (Multiset.le_cons_self S' b), hLeq⟩

end GaugeGeometry.QFT.Combinatorial
