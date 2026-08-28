import Wikipedia.HopfProblem.CuspCentralHomologyRadialCollar
import Wikipedia.HopfProblem.CuspCentralHomologyRadialCircle

/-!
# The actual radial annulus has the homotopy type of a circle

The displayed product homeomorphism retains the actual gauge radius. The
homotopy equivalence uses the explicit middle-radius section and the radial
interpolation already constructed for the literal annulus. Taking a product
with an arbitrary phase space leaves that phase coordinate unchanged.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

local notation "Plane" => CuspHoneycombTiling.Plane

/-- Explicit circle and gauge-radius coordinates on the literal annulus. -/
def annulusCircleProductHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    Annulus a ≃ₜ Circle × Ioo a 1 :=
  (annulusHomeomorph a ha).trans
    (frontierCellCircleHomeomorph.prodCongr (Homeomorph.refl (Ioo a 1)))

theorem annulusCircleProductHomeomorph_circle_coe (a : ℝ) (ha : 0 ≤ a)
    (x : Annulus a) :
    ((annulusCircleProductHomeomorph a ha x).1 : ℂ) =
      ‖circlePlaneComplexEquiv (x : Plane)‖⁻¹ • circlePlaneComplexEquiv (x : Plane) := by
  change NormedSpace.normalize (circlePlaneComplexEquiv ((cellGauge x)⁻¹ • (x : Plane))) =
    NormedSpace.normalize (circlePlaneComplexEquiv (x : Plane))
  rw [map_smul, NormedSpace.normalize_smul_of_pos (inv_pos.mpr (ha.trans_lt x.2.1))]

@[simp] theorem annulusCircleProductHomeomorph_radius (a : ℝ) (ha : 0 ≤ a)
    (x : Annulus a) :
    ((annulusCircleProductHomeomorph a ha x).2 : ℝ) = cellGauge x := rfl

theorem annulusCircleProductHomeomorph_symm_coe (a : ℝ) (ha : 0 ≤ a)
    (p : Circle × Ioo a 1) :
    ((annulusCircleProductHomeomorph a ha).symm p : Plane) =
      (p.2 : ℝ) • (frontierCellCircleHomeomorph.symm p.1 : Plane) := rfl

/-- The actual open annulus is homotopy equivalent to the standard circle. Its
inverse lands at the midpoint radius `(a + 1) / 2`. -/
def annulusCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ Circle :=
  (annulusFrontierHomotopyEquiv a ha ha1).trans
    frontierCellCircleHomeomorph.toHomotopyEquiv

theorem annulusCircleHomotopyEquiv_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : Annulus a) :
    (annulusCircleHomotopyEquiv a ha ha1 x : ℂ) =
      ‖circlePlaneComplexEquiv (x : Plane)‖⁻¹ • circlePlaneComplexEquiv (x : Plane) := by
  exact annulusCircleProductHomeomorph_circle_coe a ha x

theorem annulusCircleHomotopyEquiv_symm_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (z : Circle) :
    ((annulusCircleHomotopyEquiv a ha ha1).symm z : Plane) =
      ((a + 1) / 2) • (frontierCellCircleHomeomorph.symm z : Plane) := rfl

/-- The annulus homotopy equivalence with an arbitrary unchanged phase space. -/
def phaseAnnulusHomotopyEquiv (X : Type*) [TopologicalSpace X]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) : (X × Annulus a) ≃ₕ X × Circle :=
  (ContinuousMap.HomotopyEquiv.refl X).prodCongr (annulusCircleHomotopyEquiv a ha ha1)

@[simp] theorem phaseAnnulusHomotopyEquiv_apply (X : Type*) [TopologicalSpace X]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : X × Annulus a) :
    phaseAnnulusHomotopyEquiv X a ha ha1 p =
      (p.1, annulusCircleHomotopyEquiv a ha ha1 p.2) := rfl

@[simp] theorem phaseAnnulusHomotopyEquiv_symm_apply (X : Type*) [TopologicalSpace X]
    (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : X × Circle) :
    (phaseAnnulusHomotopyEquiv X a ha ha1).symm p =
      (p.1, (annulusCircleHomotopyEquiv a ha ha1).symm p.2) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.Radial
