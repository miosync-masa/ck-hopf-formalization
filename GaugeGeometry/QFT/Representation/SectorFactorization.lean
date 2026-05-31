import GaugeGeometry.Core.Sector
import GaugeGeometry.QFT.Representation.GaugeProduct
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace GaugeGeometry.QFT.Representation

/--
Bundle the SU(2) and U(1) contributions into a single electroweak factor.
This is the quantity that later plays the role of the "weak factor"
in the weak × color decomposition.
-/
def electroweakWeight (w : SectorWeights) : ℚ :=
  w.weak * w.hypercharge

/--
The total direct-product weight attached to the three gauge sectors.
Version 1 uses a purely multiplicative bookkeeping model.
-/
def fullWeight (w : SectorWeights) : ℚ :=
  electroweakWeight w * w.color

/--
Package form of Theorem 3.

Read this as:
for every sector assignment, the total weight factorizes into an
electroweak part and a color part.
-/
def DirectProductSectorFactorization : Prop :=
  ∀ w : SectorWeights, fullWeight w = electroweakWeight w * w.color

/--
Theorem 3: direct-product sector factorization.

This is intentionally structural and axiom-free in Version 1.
Its role is to provide the interface consumed later by
`MassRatioDecomposition.lean`.
-/
theorem direct_product_sector_factorization :
    DirectProductSectorFactorization := by
  intro w
  rfl

/--
Equivalent reordered form, often more convenient for downstream rewriting.
-/
theorem direct_product_sector_factorization_color_first (w : SectorWeights) :
    fullWeight w = w.color * electroweakWeight w := by
  unfold fullWeight electroweakWeight
  ring

/--
Expose the two-channel decomposition explicitly.
This is the bridge object for later application-level mass-ratio formulas.
-/
def weakColorDecomposition (w : SectorWeights) : ℚ × ℚ :=
  (electroweakWeight w, w.color)

/--
Repackage the total weight as "weak factor × color factor".
-/
theorem fullWeight_eq_weak_times_color (w : SectorWeights) :
    fullWeight w =
      (weakColorDecomposition w).1 * (weakColorDecomposition w).2 := by
  rfl

/--
A small normalization lemma that is often useful in later simplification:
if the hypercharge contribution is trivial, the electroweak sector reduces
to the SU(2) weight.
-/
theorem electroweakWeight_of_hypercharge_one
    (w : SectorWeights) (h : w.hypercharge = 1) :
    electroweakWeight w = w.weak := by
  unfold electroweakWeight
  rw [h]
  ring

/--
If the weak contribution is trivial, the electroweak factor vanishes.
-/
@[simp] theorem electroweakWeight_of_weak_zero
    (w : SectorWeights) (h : w.weak = 0) :
    electroweakWeight w = 0 := by
  unfold electroweakWeight
  rw [h]
  ring

/--
If the hypercharge contribution is trivial, the electroweak factor vanishes.
-/
@[simp] theorem electroweakWeight_of_hypercharge_zero
    (w : SectorWeights) (h : w.hypercharge = 0) :
    electroweakWeight w = 0 := by
  unfold electroweakWeight
  rw [h]
  ring

/--
If the color contribution is trivial, the full weight vanishes.
-/
@[simp] theorem fullWeight_of_color_zero
    (w : SectorWeights) (h : w.color = 0) :
    fullWeight w = 0 := by
  unfold fullWeight
  rw [h]
  ring

end GaugeGeometry.QFT.Representation
