import GaugeGeometry.QFT.Representation.GaugeProduct
import Mathlib.Data.Rat.Defs

namespace GaugeGeometry.QFT.Representation

/--
A minimal Dynkin-index assignment over the three canonical gauge channels.

Interpretation:
- `u1`  : U(1) contribution
- `su2` : SU(2) contribution
- `su3` : SU(3) contribution
-/
structure DynkinIndexData where
  u1 : ℚ
  su2 : ℚ
  su3 : ℚ

/--
Read Dynkin-index data through the canonical gauge index ordering.
-/
def DynkinIndexData.atIndex (d : DynkinIndexData) : GaugeIndex → ℚ
  | i =>
      if i = u1Index then d.u1
      else if i = su2Index then d.su2
      else d.su3

@[simp] theorem DynkinIndexData_at_u1 (d : DynkinIndexData) :
    d.atIndex u1Index = d.u1 := by
  simp [DynkinIndexData.atIndex, u1Index]

@[simp] theorem DynkinIndexData_at_su2 (d : DynkinIndexData) :
    d.atIndex su2Index = d.su2 := by
  simp [DynkinIndexData.atIndex, u1Index, su2Index]

@[simp] theorem DynkinIndexData_at_su3 (d : DynkinIndexData) :
    d.atIndex su3Index = d.su3 := by
  simp [DynkinIndexData.atIndex, u1Index, su2Index, su3Index]

/--
The trivial Dynkin-index assignment.
Useful as a neutral placeholder in early API design.
-/
def zeroDynkinIndexData : DynkinIndexData where
  u1 := 0
  su2 := 0
  su3 := 0

@[simp] theorem zeroDynkinIndexData_u1 :
    zeroDynkinIndexData.u1 = 0 := by
  rfl

@[simp] theorem zeroDynkinIndexData_su2 :
    zeroDynkinIndexData.su2 = 0 := by
  rfl

@[simp] theorem zeroDynkinIndexData_su3 :
    zeroDynkinIndexData.su3 = 0 := by
  rfl

@[simp] theorem DynkinIndexData_eta (d : DynkinIndexData) :
    DynkinIndexData.mk d.u1 d.su2 d.su3 = d := by
  cases d
  rfl

end GaugeGeometry.QFT.Representation
