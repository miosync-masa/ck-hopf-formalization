import GaugeGeometry.QFT.Representation.GaugeProduct
import Mathlib.Data.Rat.Defs

namespace GaugeGeometry.QFT.Representation

structure CasimirData where
  u1 : ℚ
  su2 : ℚ
  su3 : ℚ

def CasimirData.atIndex (c : CasimirData) : GaugeIndex → ℚ
  | i =>
      if i = u1Index then c.u1
      else if i = su2Index then c.su2
      else c.su3

@[simp] theorem CasimirData_at_u1 (c : CasimirData) :
    c.atIndex u1Index = c.u1 := by
  simp [CasimirData.atIndex, u1Index]

@[simp] theorem CasimirData_at_su2 (c : CasimirData) :
    c.atIndex su2Index = c.su2 := by
  have hne : su2Index ≠ u1Index := by decide
  simp [CasimirData.atIndex, u1Index, su2Index]

@[simp] theorem CasimirData_at_su3 (c : CasimirData) :
    c.atIndex su3Index = c.su3 := by
  have hne1 : su3Index ≠ u1Index := by decide
  have hne2 : su3Index ≠ su2Index := by decide
  simp [CasimirData.atIndex, u1Index, su2Index, su3Index]

def zeroCasimirData : CasimirData where
  u1 := 0
  su2 := 0
  su3 := 0

@[simp] theorem zeroCasimirData_u1 :
    zeroCasimirData.u1 = 0 := by
  rfl

@[simp] theorem zeroCasimirData_su2 :
    zeroCasimirData.su2 = 0 := by
  rfl

@[simp] theorem zeroCasimirData_su3 :
    zeroCasimirData.su3 = 0 := by
  rfl

structure AdjointCasimirData where
  data : CasimirData

structure MatterCasimirData where
  data : CasimirData

def AdjointCasimirData.atIndex (c : AdjointCasimirData) : GaugeIndex → ℚ :=
  c.data.atIndex

def MatterCasimirData.atIndex (c : MatterCasimirData) : GaugeIndex → ℚ :=
  c.data.atIndex

@[simp] theorem AdjointCasimirData_at_u1 (c : AdjointCasimirData) :
    c.atIndex u1Index = c.data.u1 := by
  simp [AdjointCasimirData.atIndex]

@[simp] theorem AdjointCasimirData_at_su2 (c : AdjointCasimirData) :
    c.atIndex su2Index = c.data.su2 := by
  simp [AdjointCasimirData.atIndex]

@[simp] theorem AdjointCasimirData_at_su3 (c : AdjointCasimirData) :
    c.atIndex su3Index = c.data.su3 := by
  simp [AdjointCasimirData.atIndex]

@[simp] theorem MatterCasimirData_at_u1 (c : MatterCasimirData) :
    c.atIndex u1Index = c.data.u1 := by
  simp [MatterCasimirData.atIndex]

@[simp] theorem MatterCasimirData_at_su2 (c : MatterCasimirData) :
    c.atIndex su2Index = c.data.su2 := by
  simp [MatterCasimirData.atIndex]

@[simp] theorem MatterCasimirData_at_su3 (c : MatterCasimirData) :
    c.atIndex su3Index = c.data.su3 := by
  simp [MatterCasimirData.atIndex]

def zeroAdjointCasimirData : AdjointCasimirData where
  data := zeroCasimirData

def zeroMatterCasimirData : MatterCasimirData where
  data := zeroCasimirData

@[simp] theorem zeroAdjointCasimirData_at_u1 :
    zeroAdjointCasimirData.atIndex u1Index = 0 := by
  simp [zeroAdjointCasimirData, AdjointCasimirData.atIndex]

@[simp] theorem zeroAdjointCasimirData_at_su2 :
    zeroAdjointCasimirData.atIndex su2Index = 0 := by
  simp [zeroAdjointCasimirData, AdjointCasimirData.atIndex]

@[simp] theorem zeroAdjointCasimirData_at_su3 :
    zeroAdjointCasimirData.atIndex su3Index = 0 := by
  simp [zeroAdjointCasimirData, AdjointCasimirData.atIndex]

@[simp] theorem zeroMatterCasimirData_at_u1 :
    zeroMatterCasimirData.atIndex u1Index = 0 := by
  simp [zeroMatterCasimirData, MatterCasimirData.atIndex]

@[simp] theorem zeroMatterCasimirData_at_su2 :
    zeroMatterCasimirData.atIndex su2Index = 0 := by
  simp [zeroMatterCasimirData, MatterCasimirData.atIndex]

@[simp] theorem zeroMatterCasimirData_at_su3 :
    zeroMatterCasimirData.atIndex su3Index = 0 := by
  simp [zeroMatterCasimirData, MatterCasimirData.atIndex]

@[simp] theorem CasimirData_eta (c : CasimirData) :
    CasimirData.mk c.u1 c.su2 c.su3 = c := by
  cases c
  rfl

@[simp] theorem AdjointCasimirData_eta (c : AdjointCasimirData) :
    AdjointCasimirData.mk c.data = c := by
  cases c
  rfl

@[simp] theorem MatterCasimirData_eta (c : MatterCasimirData) :
    MatterCasimirData.mk c.data = c := by
  cases c
  rfl

end GaugeGeometry.QFT.Representation
