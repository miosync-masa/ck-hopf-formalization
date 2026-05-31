import GaugeGeometry.Core.Sector
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Representation

abbrev GaugeSector := GaugeGeometry.Core.GaugeSector
abbrev SectorWeights := GaugeGeometry.Core.SectorWeights

/--
Canonical gauge-channel index:
0 ↦ U(1), 1 ↦ SU(2), 2 ↦ SU(3).
-/
abbrev GaugeIndex := Fin 3

/--
Canonical indices for the three gauge sectors.
-/
def u1Index : GaugeIndex := ⟨0, by decide⟩
def su2Index : GaugeIndex := ⟨1, by decide⟩
def su3Index : GaugeIndex := ⟨2, by decide⟩

/--
Convert the canonical gauge index into the corresponding sector label.
-/
def sectorOfIndex : GaugeIndex → GaugeSector
  | ⟨0, _⟩ => GaugeGeometry.Core.GaugeSector.hypercharge
  | ⟨1, _⟩ => GaugeGeometry.Core.GaugeSector.weak
  | ⟨2, _⟩ => GaugeGeometry.Core.GaugeSector.color

/--
Convert a sector label into its canonical gauge index.
-/
def indexOfSector : GaugeSector → GaugeIndex
  | GaugeGeometry.Core.GaugeSector.hypercharge => u1Index
  | GaugeGeometry.Core.GaugeSector.weak => su2Index
  | GaugeGeometry.Core.GaugeSector.color => su3Index

@[simp] theorem sectorOfIndex_u1 :
    sectorOfIndex u1Index = GaugeGeometry.Core.GaugeSector.hypercharge := by
  rfl

@[simp] theorem sectorOfIndex_su2 :
    sectorOfIndex su2Index = GaugeGeometry.Core.GaugeSector.weak := by
  rfl

@[simp] theorem sectorOfIndex_su3 :
    sectorOfIndex su3Index = GaugeGeometry.Core.GaugeSector.color := by
  rfl

@[simp] theorem indexOfSector_hypercharge :
    indexOfSector GaugeGeometry.Core.GaugeSector.hypercharge = u1Index := by
  rfl

@[simp] theorem indexOfSector_weak :
    indexOfSector GaugeGeometry.Core.GaugeSector.weak = su2Index := by
  rfl

@[simp] theorem indexOfSector_color :
    indexOfSector GaugeGeometry.Core.GaugeSector.color = su3Index := by
  rfl

@[simp] theorem sectorOfIndex_indexOfSector (s : GaugeSector) :
    sectorOfIndex (indexOfSector s) = s := by
  cases s <;> rfl

@[simp] theorem indexOfSector_sectorOfIndex (i : GaugeIndex) :
    indexOfSector (sectorOfIndex i) = i := by
  fin_cases i <;> rfl

/--
Read a sector weight through the canonical gauge index ordering.
-/
def sectorWeightAtIndex (w : SectorWeights) (i : GaugeIndex) : ℚ :=
  w.get (sectorOfIndex i)

@[simp] theorem sectorWeightAtIndex_u1 (w : SectorWeights) :
    sectorWeightAtIndex w u1Index = w.hypercharge := by
  simp [sectorWeightAtIndex, u1Index, sectorOfIndex]

@[simp] theorem sectorWeightAtIndex_su2 (w : SectorWeights) :
    sectorWeightAtIndex w su2Index = w.weak := by
  simp [sectorWeightAtIndex, su2Index, sectorOfIndex]

@[simp] theorem sectorWeightAtIndex_su3 (w : SectorWeights) :
    sectorWeightAtIndex w su3Index = w.color := by
  simp [sectorWeightAtIndex, su3Index, sectorOfIndex]

end GaugeGeometry.QFT.Representation
