import GaugeGeometry.QFT.HopfAlgebra.QuotientLift
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Free commutative algebra over connected Feynman-graph classes (Sprint B' scaffold)

This file builds `HopfH_temp`, the **scaffold** Hopf-algebra carrier
used during Sprint B'. Per the Plan-D Hybrid strategy
(`HOPF_DECOMPOSITION.md § H3`):

* `HopfH_temp := MvPolynomial HopfGenTemp ℚ`
  where `HopfGenTemp = { [Γ] : FeynmanGraphClass // [Γ].IsSupportConnected }`.

* In Sprint C, the strict Connes–Kreimer artifact `HopfH` over
  `IsConnectedDivergent` generators is built alongside this scaffold,
  with an algebra-embedding bridge `HopfH ↪ HopfH_temp`. The scaffold
  remains as internal infrastructure mirroring Sprint A's
  `contractWith → contract` alias pattern.

Mathlib supplies `CommRing` and `Algebra ℚ` automatically for
`MvPolynomial X ℚ` and for tensor products of such.

## Tag map (HOPF_DECOMPOSITION.md § H3 Sprint B' subtable)

* `[Def]` `HopfGenTemp` — H3.0
* `[Def]` `HopfH_temp` — H3.1
* `[Def]` `gen_temp` — H3.2
* `[Algebra]` `CommRing HopfH_temp`, `Algebra ℚ HopfH_temp` — H3.3 (Mathlib)
* `[Algebra]` `CommRing (HopfH_temp ⊗[ℚ] HopfH_temp)` — H3.4 (Mathlib)
* `[Algebra]` `Algebra ℚ (HopfH_temp ⊗[ℚ] HopfH_temp)` — H3.5 (Mathlib)
-/

open scoped TensorProduct

namespace GaugeGeometry.QFT.Combinatorial

/--
**H3.0** — Sprint B' scaffold generators set: classes of support-connected
Feynman graphs. The strict Connes–Kreimer requirement
(`IsConnectedDivergent`) is added in Sprint C as a sub-subtype.
-/
def HopfGenTemp : Type :=
  { c : FeynmanGraphClass // c.IsSupportConnected }

/--
**H3.1** — Sprint B' scaffold polynomial algebra over ℚ. Mathlib
provides the `CommRing` and `Algebra ℚ` instances automatically.

Marked `noncomputable` because `MvPolynomial.X` is `noncomputable`.
-/
noncomputable abbrev HopfH_temp : Type := MvPolynomial HopfGenTemp ℚ

/--
**H3.2** — The generator of `HopfH_temp` corresponding to a
support-connected graph class.
-/
noncomputable def gen_temp (c : HopfGenTemp) : HopfH_temp := MvPolynomial.X c

/-! ### H3.3 / H3.4 / H3.5 — instances supplied by Mathlib

`MvPolynomial HopfGenTemp ℚ` is automatically a `CommRing` and a
`ℚ`-algebra; the tensor product `HopfH_temp ⊗[ℚ] HopfH_temp` is
automatically a `CommRing` (the algebra is commutative) and a
`ℚ`-algebra. We assert these to fix the implicit-search results. -/

noncomputable example : CommRing HopfH_temp := inferInstance
noncomputable example : Algebra ℚ HopfH_temp := inferInstance
noncomputable example : CommRing (HopfH_temp ⊗[ℚ] HopfH_temp) := inferInstance
noncomputable example : Algebra ℚ (HopfH_temp ⊗[ℚ] HopfH_temp) := inferInstance

end GaugeGeometry.QFT.Combinatorial
