namespace GaugeGeometry.Core

/--
Minimal tags for the matter-content choice.
This file is intentionally lightweight and upstream of QFT details.
-/
inductive MatterContentTag where
  | SM
  | MSSM
  deriving DecidableEq, Repr

/--
A minimal record for matter-content metadata.

This is not yet a full field-theory implementation.
It only stores the coarse structural choices needed by `ModelSpec`.
-/
structure MatterContent where
  tag : MatterContentTag
  generations : Nat
  higgsDoublets : Nat
  hasSupersymmetry : Bool

/--
Canonical Standard Model matter content.
-/
def standardModel : MatterContent where
  tag := .SM
  generations := 3
  higgsDoublets := 1
  hasSupersymmetry := false

/--
Canonical MSSM matter content.
-/
def mssm : MatterContent where
  tag := .MSSM
  generations := 3
  higgsDoublets := 2
  hasSupersymmetry := true

/--
Predicate: this matter content is tagged as SM.
-/
def MatterContent.isSM (m : MatterContent) : Prop :=
  m.tag = .SM

/--
Predicate: this matter content is tagged as MSSM.
-/
def MatterContent.isMSSM (m : MatterContent) : Prop :=
  m.tag = .MSSM

@[simp] theorem standardModel_tag :
    standardModel.tag = .SM := by
  rfl

@[simp] theorem standardModel_generations :
    standardModel.generations = 3 := by
  rfl

@[simp] theorem standardModel_higgsDoublets :
    standardModel.higgsDoublets = 1 := by
  rfl

@[simp] theorem standardModel_hasSupersymmetry :
    standardModel.hasSupersymmetry = false := by
  rfl

@[simp] theorem mssm_tag :
    mssm.tag = .MSSM := by
  rfl

@[simp] theorem mssm_generations :
    mssm.generations = 3 := by
  rfl

@[simp] theorem mssm_higgsDoublets :
    mssm.higgsDoublets = 2 := by
  rfl

@[simp] theorem mssm_hasSupersymmetry :
    mssm.hasSupersymmetry = true := by
  rfl

@[simp] theorem standardModel_isSM :
    standardModel.isSM := by
  rfl

@[simp] theorem mssm_isMSSM :
    mssm.isMSSM := by
  rfl

@[simp] theorem standardModel_not_MSSM :
    ¬ standardModel.isMSSM := by
  simp [MatterContent.isMSSM]

@[simp] theorem mssm_not_SM :
    ¬ mssm.isSM := by
  simp [MatterContent.isSM]

@[simp] theorem MatterContent_eta (m : MatterContent) :
    MatterContent.mk m.tag m.generations m.higgsDoublets m.hasSupersymmetry = m := by
  cases m
  rfl

end GaugeGeometry.Core
