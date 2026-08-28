import Wikipedia.HopfProblem.SpecialPeriodsMuTorsorCore
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Cyclic equivariance of affine sections

For the actual geometric triangle action and an affine cocycle, the group
elements preserving a given section form a subgroup. Consequently one
global generator equation implies the section equation for every integral
power and every element of the cyclic subgroup it generates. These are
identities of the actual affine fibre maps.
-/

noncomputable section

open UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.AffineCocycle

variable (c : AffineCocycle) (f : ℍ → ℂ)

/-- The stabilizer of an actual section under the affine action. No
holomorphicity or equivariance outside this subgroup is assumed. -/
def sectionStabilizer : Subgroup TriangleGroup where
  carrier := {g | ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z)}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, c.fibreMap_one]
  mul_mem' := by
    intro g h hg hh z
    calc
      f (triangleGeometricRepresentation (g * h) z) =
          f (triangleGeometricRepresentation g (triangleGeometricRepresentation h z)) := by
        rw [map_mul, Equiv.Perm.mul_apply]
      _ = c.fibreMap g (triangleGeometricRepresentation h z)
          (f (triangleGeometricRepresentation h z)) := hg _
      _ = c.fibreMap g (triangleGeometricRepresentation h z) (c.fibreMap h z (f z)) := by
        rw [hh z]
      _ = c.fibreMap (g * h) z (f z) := (c.fibreMap_mul g h z (f z)).symm
  inv_mem' := by
    intro g hg z
    apply c.fibreMap_injective g (triangleGeometricRepresentation g⁻¹ z)
    have hbase : triangleGeometricRepresentation g (triangleGeometricRepresentation g⁻¹ z) = z := by
      rw [map_inv, Equiv.Perm.inv_def]
      exact (triangleGeometricRepresentation g).apply_symm_apply z
    calc
      c.fibreMap g (triangleGeometricRepresentation g⁻¹ z)
          (f (triangleGeometricRepresentation g⁻¹ z)) =
          f (triangleGeometricRepresentation g (triangleGeometricRepresentation g⁻¹ z)) :=
        (hg _).symm
      _ = f z := congrArg f hbase
      _ = c.fibreMap g (triangleGeometricRepresentation g⁻¹ z) (c.fibreMap g⁻¹ z (f z)) := by
        simpa only [inv_inv] using (c.fibreMap_inv g⁻¹ z (f z)).symm

@[simp] theorem mem_sectionStabilizer (g : TriangleGroup) :
    g ∈ c.sectionStabilizer f ↔
      ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z) := Iff.rfl

/-- One generator equation implies the equation for every integer power,
including negative powers. -/
theorem equivariant_zpow (g : TriangleGroup)
    (hg : ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z))
    (n : ℤ) (z : ℍ) :
    f (triangleGeometricRepresentation (g ^ n) z) = c.fibreMap (g ^ n) z (f z) :=
  (c.sectionStabilizer f).zpow_mem hg n z

theorem zpowers_le_sectionStabilizer (g : TriangleGroup)
    (hg : ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z)) :
    Subgroup.zpowers g ≤ c.sectionStabilizer f := Subgroup.zpowers_le.mpr hg

/-- The generator equation extends to every member of its actual cyclic
subgroup, without choosing a power representative. -/
theorem equivariant_of_mem_zpowers (g : TriangleGroup)
    (hg : ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z))
    {h : TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    f (triangleGeometricRepresentation h z) = c.fibreMap h z (f z) :=
  c.zpowers_le_sectionStabilizer f g hg hh z

/-- The subtype form is directly usable for local-seed stabilizer laws. -/
theorem equivariant_zpowers (g : TriangleGroup)
    (hg : ∀ z, f (triangleGeometricRepresentation g z) = c.fibreMap g z (f z))
    (h : Subgroup.zpowers g) (z : ℍ) :
    f (triangleGeometricRepresentation (h : TriangleGroup) z) =
      c.fibreMap (h : TriangleGroup) z (f z) :=
  c.equivariant_of_mem_zpowers f g hg h.property z

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.AffineCocycle
