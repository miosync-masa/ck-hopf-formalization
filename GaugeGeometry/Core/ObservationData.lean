import Mathlib.Data.Real.Basic

namespace GaugeGeometry.Core

/--
Quark flavors used by the observation layer.
-/
inductive QuarkFlavor where
  | up
  | down
  | strange
  | charm
  | bottom
  | top
  deriving DecidableEq

/--
A measured quantity with central value and uncertainty.
Version 1 is intentionally neutral and does not impose interpretation.
-/
structure MeasuredValue where
  centralValue : ℝ
  uncertainty : ℝ

/--
Measured quark-mass inputs.
-/
structure QuarkMassInputs where
  up : MeasuredValue
  down : MeasuredValue
  strange : MeasuredValue
  charm : MeasuredValue
  bottom : MeasuredValue
  top : MeasuredValue

/--
Access quark-mass data by flavor.
-/
def QuarkMassInputs.get (q : QuarkMassInputs) : QuarkFlavor → MeasuredValue
  | .up => q.up
  | .down => q.down
  | .strange => q.strange
  | .charm => q.charm
  | .bottom => q.bottom
  | .top => q.top

@[simp] theorem QuarkMassInputs.get_up (q : QuarkMassInputs) :
    q.get .up = q.up := by
  rfl

@[simp] theorem QuarkMassInputs.get_down (q : QuarkMassInputs) :
    q.get .down = q.down := by
  rfl

@[simp] theorem QuarkMassInputs.get_strange (q : QuarkMassInputs) :
    q.get .strange = q.strange := by
  rfl

@[simp] theorem QuarkMassInputs.get_charm (q : QuarkMassInputs) :
    q.get .charm = q.charm := by
  rfl

@[simp] theorem QuarkMassInputs.get_bottom (q : QuarkMassInputs) :
    q.get .bottom = q.bottom := by
  rfl

@[simp] theorem QuarkMassInputs.get_top (q : QuarkMassInputs) :
    q.get .top = q.top := by
  rfl

/--
Top-level observational inputs used downstream.

Version 1 keeps only:
- a reference scale,
- alpha_s measured at that reference scale,
- quark-mass inputs.
-/
structure ObservationData where
  referenceScale : ℝ
  alphaS : MeasuredValue
  quarkMasses : QuarkMassInputs

@[simp] theorem MeasuredValue_eta (x : MeasuredValue) :
    MeasuredValue.mk x.centralValue x.uncertainty = x := by
  cases x
  rfl

@[simp] theorem QuarkMassInputs_eta (q : QuarkMassInputs) :
    QuarkMassInputs.mk q.up q.down q.strange q.charm q.bottom q.top = q := by
  cases q
  rfl

@[simp] theorem ObservationData_eta (obs : ObservationData) :
    ObservationData.mk obs.referenceScale obs.alphaS obs.quarkMasses = obs := by
  cases obs
  rfl

end GaugeGeometry.Core
