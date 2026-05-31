import GaugeGeometry.Core.MatterContent
import GaugeGeometry.QFT.Representation.CasimirData
import GaugeGeometry.QFT.Representation.DynkinIndex

namespace GaugeGeometry.Axioms

open GaugeGeometry.Core
open GaugeGeometry.QFT.Representation

/--
External matter-content choice.
Version 1 isolates the MSSM assumption as an explicit model axiom.
-/
axiom chosenMatterContent : MatterContent

/--
The chosen matter content is MSSM-like.
-/
axiom chosenMatterContent_isMSSM :
  chosenMatterContent.isMSSM

/--
Optional structural MSSM assumptions kept explicit at the boundary.
These can later be weakened or replaced if needed.
-/
axiom chosenMatterContent_generations_eq_three :
  chosenMatterContent.generations = 3

axiom chosenMatterContent_higgsDoublets_eq_two :
  chosenMatterContent.higgsDoublets = 2

axiom chosenMatterContent_hasSupersymmetry :
  chosenMatterContent.hasSupersymmetry = true

@[simp] theorem chosenMatterContent_tag :
    chosenMatterContent.tag = .MSSM := by
  simpa [MatterContent.isMSSM] using chosenMatterContent_isMSSM

@[simp] theorem chosenMatterContent_not_SM :
    ¬ chosenMatterContent.isSM := by
  simp [MatterContent.isSM, chosenMatterContent_tag]

/-!
### MSSM 1-loop β assembly inputs

The following axioms isolate the *numerical* representation-theoretic
inputs needed to assemble the MSSM 1-loop β coefficients from Casimir
and Dynkin-index data. These are empirical / group-theoretic data
specific to the MSSM matter content:

* `mssmAdjointCasimir` — Casimir of the adjoint (= quadratic Casimir
  of the gauge factor itself),
* `mssmMatterDynkin` — sum of Dynkin indices of the MSSM matter
  representations, sector by sector.

Concrete values (group-theoretic convention, SU(5)-normalized U(1)):

* SU(3): `C₂(G) = 3`, `T(matter) = 6`
* SU(2): `C₂(G) = 2`, `T(matter) = 7`
* U(1) : `C₂(G) = 0`, `T(matter) = 33/5`

These choices together with the SUSY assembly
`b_i = -3 · C₂(G_i) + T_i(matter)` reproduce the MSSM 1-loop β tuple
`(33/5, 1, -3)`.
-/

/--
MSSM adjoint-Casimir data `C₂(G_i)` for `i ∈ {U(1), SU(2), SU(3)}`.
Empirically/by convention:
  U(1) → 0, SU(2) → 2, SU(3) → 3.
-/
axiom mssmAdjointCasimir : AdjointCasimirData

axiom mssmAdjointCasimir_u1 :
  mssmAdjointCasimir.data.u1 = 0

axiom mssmAdjointCasimir_su2 :
  mssmAdjointCasimir.data.su2 = 2

axiom mssmAdjointCasimir_su3 :
  mssmAdjointCasimir.data.su3 = 3

/--
MSSM matter Dynkin-index sum `T_i(matter)` for `i ∈ {U(1), SU(2), SU(3)}`.
Under the MSSM matter content and SU(5)-normalized U(1):
  U(1) → 33/5, SU(2) → 7, SU(3) → 6.
-/
axiom mssmMatterDynkin : DynkinIndexData

axiom mssmMatterDynkin_u1 :
  mssmMatterDynkin.u1 = (33 : ℚ) / 5

axiom mssmMatterDynkin_su2 :
  mssmMatterDynkin.su2 = 7

axiom mssmMatterDynkin_su3 :
  mssmMatterDynkin.su3 = 6

end GaugeGeometry.Axioms
