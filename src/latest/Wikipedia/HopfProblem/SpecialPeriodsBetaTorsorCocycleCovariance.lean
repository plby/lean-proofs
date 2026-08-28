import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycle

/-!
# Covariance under the additive beta cocycle

For an additive cocycle over the actual triangle action, the elements
under which a given function has the prescribed covariance form a
subgroup.  Consequently, covariance under a single element propagates
to its entire cyclic subgroup, and covariance under the two triangle
generators propagates to the whole triangle group.
-/

noncomputable section

open Set UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

section AdditiveCocycle

variable (b : TriangleGroup → ℍ → ℂ)
    (hone : ∀ z, b 1 z = 0)
    (hmul : ∀ g h z,
      b (g * h) z = b g (triangleGeometricRepresentation h z) + b h z)
    (hinv : ∀ g z, b g⁻¹ z = -b g (triangleGeometricRepresentation g⁻¹ z))
    (β : ℍ → ℂ)

/-- The actual subgroup of elements under which `β` has the covariance
specified by the additive cocycle `b`. -/
def covarianceSubgroup : Subgroup TriangleGroup where
  carrier := {g | ∀ z, β (triangleGeometricRepresentation g z) = β z + b g z}
  one_mem' := by
    intro z
    simp only [map_one, Equiv.Perm.one_apply, hone, add_zero]
  mul_mem' := by
    intro g h hg hh z
    rw [map_mul, Equiv.Perm.mul_apply, hg, hh, hmul]
    abel
  inv_mem' := by
    intro g hg z
    have he := hg (triangleGeometricRepresentation g⁻¹ z)
    have hc : triangleGeometricRepresentation g
        (triangleGeometricRepresentation g⁻¹ z) = z := by
      rw [map_inv]
      exact (triangleGeometricRepresentation g).apply_symm_apply z
    rw [hc] at he
    rw [hinv, he]
    abel

@[simp] theorem mem_covarianceSubgroup (g : TriangleGroup) :
    g ∈ covarianceSubgroup b hone hmul hinv β ↔
      ∀ z, β (triangleGeometricRepresentation g z) = β z + b g z := Iff.rfl

include hone hmul hinv

/-- Covariance under every element of a generating set propagates to the
subgroup it generates. -/
theorem covariance_of_mem_closure (s : Set TriangleGroup)
    (hs : ∀ g ∈ s, ∀ z,
      β (triangleGeometricRepresentation g z) = β z + b g z)
    {g : TriangleGroup} (hg : g ∈ Subgroup.closure s) (z : ℍ) :
    β (triangleGeometricRepresentation g z) = β z + b g z := by
  have hle : Subgroup.closure s ≤ covarianceSubgroup b hone hmul hinv β :=
    (Subgroup.closure_le _).mpr hs
  exact hle hg z

/-- A single covariance equation implies covariance under all integer
powers, including negative powers. -/
theorem covariance_zpow (g : TriangleGroup)
    (hg : ∀ z, β (triangleGeometricRepresentation g z) = β z + b g z)
    (n : ℤ) (z : ℍ) :
    β (triangleGeometricRepresentation (g ^ n) z) = β z + b (g ^ n) z :=
  (covarianceSubgroup b hone hmul hinv β).zpow_mem hg n z

/-- Covariance under one element is enough on its actual cyclic subgroup. -/
theorem covariance_zpowers (g : TriangleGroup)
    (hg : ∀ z, β (triangleGeometricRepresentation g z) = β z + b g z)
    {h : TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (triangleGeometricRepresentation h z) = β z + b h z :=
  (Subgroup.zpowers_le.mpr
    (show g ∈ covarianceSubgroup b hone hmul hinv β from hg)) hh z

/-- The two generator equations imply covariance under every word in the
actual `(3,4,∞)` triangle group. -/
theorem covariance_all_of_generators
    (h₁ : ∀ z, β (triangleGeometricRepresentation triangleGenerator₁ z) =
      β z + b triangleGenerator₁ z)
    (h₂ : ∀ z, β (triangleGeometricRepresentation triangleGenerator₂ z) =
      β z + b triangleGenerator₂ z)
    (g : TriangleGroup) (z : ℍ) :
    β (triangleGeometricRepresentation g z) = β z + b g z := by
  apply covariance_of_mem_closure b hone hmul hinv β
    ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup)
  · intro h hh
    rcases hh with rfl | rfl
    · exact h₁
    · exact h₂
  · rw [triangle_generators_generate]
    exact Subgroup.mem_top g

/-- The subgroup criterion is exactly the pair of generator equations. -/
theorem covarianceSubgroup_eq_top_iff :
    covarianceSubgroup b hone hmul hinv β = ⊤ ↔
      (∀ z, β (triangleGeometricRepresentation triangleGenerator₁ z) =
        β z + b triangleGenerator₁ z) ∧
      (∀ z, β (triangleGeometricRepresentation triangleGenerator₂ z) =
        β z + b triangleGenerator₂ z) := by
  constructor
  · intro h
    constructor
    · have hm : triangleGenerator₁ ∈ covarianceSubgroup b hone hmul hinv β := by
        rw [h]
        exact Subgroup.mem_top _
      exact hm
    · have hm : triangleGenerator₂ ∈ covarianceSubgroup b hone hmul hinv β := by
        rw [h]
        exact Subgroup.mem_top _
      exact hm
  · rintro ⟨h₁, h₂⟩
    apply top_unique
    intro g _
    exact covariance_all_of_generators b hone hmul hinv β h₁ h₂ g

end AdditiveCocycle

section TriangleCocycle

variable (φ₁ φ₂ : ℍ → ℂ)
    (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((Triangle.generatorOnePerm ^ k) z)) = 0)
    (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((Triangle.generatorTwoPerm ^ k) z)) = 0)
    (β : ℍ → ℂ)

local notation "shift" => triangleAdditiveShift φ₁ φ₂ h₁ h₂

/-- For the constructed beta cocycle, the two native generator equations
imply the required covariance under every triangle-group element. -/
theorem triangleAdditiveShift_covariance_of_generators
    (hβ₁ : ∀ z, β (Triangle.generatorOnePerm z) = β z + φ₁ z)
    (hβ₂ : ∀ z, β (Triangle.generatorTwoPerm z) = β z + φ₂ z)
    (g : TriangleGroup) (z : ℍ) :
    β (triangleGeometricRepresentation g z) = β z + shift g z := by
  apply covariance_all_of_generators shift
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) β
  · intro w
    simpa only [triangleGeometricRepresentation_generator₁,
      triangleAdditiveShift_generator₁] using hβ₁ w
  · intro w
    simpa only [triangleGeometricRepresentation_generator₂,
      triangleAdditiveShift_generator₂] using hβ₂ w

/-- The global covariance equations for the actual additive shift are
equivalent to the two equations with the prescribed generator shifts. -/
theorem triangleAdditiveShift_covariance_iff :
    (∀ g z, β (triangleGeometricRepresentation g z) = β z + shift g z) ↔
      (∀ z, β (Triangle.generatorOnePerm z) = β z + φ₁ z) ∧
      (∀ z, β (Triangle.generatorTwoPerm z) = β z + φ₂ z) := by
  constructor
  · intro h
    constructor
    · intro z
      simpa only [triangleGeometricRepresentation_generator₁,
        triangleAdditiveShift_generator₁] using h triangleGenerator₁ z
    · intro z
      simpa only [triangleGeometricRepresentation_generator₂,
        triangleAdditiveShift_generator₂] using h triangleGenerator₂ z
  · rintro ⟨hβ₁, hβ₂⟩
    exact triangleAdditiveShift_covariance_of_generators φ₁ φ₂ h₁ h₂ β hβ₁ hβ₂

/-- The covariance equation for one element and the constructed shift
implies the corresponding equations for all of its integer powers. -/
theorem triangleAdditiveShift_covariance_zpow (g : TriangleGroup)
    (hg : ∀ z, β (triangleGeometricRepresentation g z) = β z + shift g z)
    (n : ℤ) (z : ℍ) :
    β (triangleGeometricRepresentation (g ^ n) z) = β z + shift (g ^ n) z :=
  covariance_zpow shift
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) β g hg n z

/-- The covariance equation for one element implies covariance under
every element of its actual cyclic subgroup. -/
theorem triangleAdditiveShift_covariance_zpowers (g : TriangleGroup)
    (hg : ∀ z, β (triangleGeometricRepresentation g z) = β z + shift g z)
    {h : TriangleGroup} (hh : h ∈ Subgroup.zpowers g) (z : ℍ) :
    β (triangleGeometricRepresentation h z) = β z + shift h z :=
  covariance_zpowers shift
    (triangleAdditiveShift_one φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂)
    (triangleAdditiveShift_inv φ₁ φ₂ h₁ h₂) β g hg hh z

/-- The first native generator equation propagates to every integer
power of the actual order-three geometric permutation. -/
theorem triangleAdditiveShift_generator₁_covariance_zpow
    (hβ₁ : ∀ z, β (Triangle.generatorOnePerm z) = β z + φ₁ z)
    (n : ℤ) (z : ℍ) :
    β ((Triangle.generatorOnePerm ^ n) z) = β z + shift (triangleGenerator₁ ^ n) z := by
  have hg : ∀ w, β (triangleGeometricRepresentation triangleGenerator₁ w) =
      β w + shift triangleGenerator₁ w := by
    intro w
    simpa only [triangleGeometricRepresentation_generator₁,
      triangleAdditiveShift_generator₁] using hβ₁ w
  simpa only [map_zpow, triangleGeometricRepresentation_generator₁] using
    triangleAdditiveShift_covariance_zpow φ₁ φ₂ h₁ h₂ β triangleGenerator₁ hg n z

/-- The second native generator equation propagates to every integer
power of the actual order-four geometric permutation. -/
theorem triangleAdditiveShift_generator₂_covariance_zpow
    (hβ₂ : ∀ z, β (Triangle.generatorTwoPerm z) = β z + φ₂ z)
    (n : ℤ) (z : ℍ) :
    β ((Triangle.generatorTwoPerm ^ n) z) = β z + shift (triangleGenerator₂ ^ n) z := by
  have hg : ∀ w, β (triangleGeometricRepresentation triangleGenerator₂ w) =
      β w + shift triangleGenerator₂ w := by
    intro w
    simpa only [triangleGeometricRepresentation_generator₂,
      triangleAdditiveShift_generator₂] using hβ₂ w
  simpa only [map_zpow, triangleGeometricRepresentation_generator₂] using
    triangleAdditiveShift_covariance_zpow φ₁ φ₂ h₁ h₂ β triangleGenerator₂ hg n z

end TriangleCocycle

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
