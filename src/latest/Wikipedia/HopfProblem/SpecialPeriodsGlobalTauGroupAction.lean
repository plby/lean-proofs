import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness
import Wikipedia.HopfProblem.SpecialPeriodsTriangleModularRepresentation

/-!
# The generator equations give the actual full triangle action

The two source covariance equations extend to every element of the actual
free-product triangle group.  The target action is the already constructed
projective integral representation, not a separately supplied action.
The distinguished cusp equation and all its integer powers follow.
-/

noncomputable section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

namespace TauEquivariance

/-- Elements for which a map intertwines two permutation actions form
an actual subgroup, without any injectivity assumption on the map. -/
def intertwiningSubgroup {G X Y : Type*} [Group G]
    (α : G →* Equiv.Perm X) (β : G →* Equiv.Perm Y) (f : X → Y) : Subgroup G where
  carrier := {g | ∀ x, f (α g x) = β g (f x)}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    simpa only [map_mul, Equiv.Perm.coe_mul, Function.comp_apply] using
      (hg (α h x)).trans (congrArg (β g) (hh x))
  inv_mem' := by
    intro g hg x
    apply (β g).injective
    have h := hg (α g⁻¹ x)
    simpa using h.symm

end TauEquivariance

/-- The source's two generator laws imply covariance for the constructed
modular representation on every actual triangle element. -/
theorem tau_covariant_triangle_action {τ : ℍ → ℍ} (hτ : TauCovariant τ)
    (g : TriangleGroup) (z : ℍ) :
    τ (triangleGeometricRepresentation g z) = triangleModularAction g (τ z) := by
  let H := TauEquivariance.intertwiningSubgroup
    triangleGeometricRepresentation triangleModularAction τ
  have hgen : ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) ⊆ H := by
    intro h hh
    rcases Set.mem_insert_iff.mp hh with rfl | hh
    · intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₁_apply,
        triangleModularAction_generator₁_coe]
      exact hτ.1 x
    · have he : h = triangleGenerator₂ := Set.mem_singleton_iff.mp hh
      subst h
      intro x
      apply UpperHalfPlane.ext
      rw [triangleGeometricRepresentation_generator₂_apply,
        triangleModularAction_generator₂_coe]
      exact hτ.2 x
  have htop : (⊤ : Subgroup TriangleGroup) ≤ H := by
    rw [← triangle_generators_generate]
    exact (Subgroup.closure_le _).mpr hgen
  exact htop (Subgroup.mem_top g) z

theorem tau_covariant_cusp {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (triangleGeometricRepresentation triangleCuspGenerator z) = (-1 : ℝ) +ᵥ τ z := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_apply]

theorem tau_covariant_cusp_coe {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    (τ (triangleGeometricRepresentation triangleCuspGenerator z) : ℂ) = (τ z : ℂ) - 1 := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_coe]

theorem tau_covariant_cusp_zpow {τ : ℍ → ℍ} (hτ : TauCovariant τ) (n : ℤ) (z : ℍ) :
    (τ (triangleGeometricRepresentation (triangleCuspGenerator ^ n) z) : ℂ) =
      (τ z : ℂ) - (n : ℂ) := by
  rw [tau_covariant_triangle_action hτ, triangleModularAction_cusp_zpow_coe]

end Wikipedia.HopfProblem.SpecialPeriods
