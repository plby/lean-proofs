import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCocycleSkew

/-!
# The all-word additive shift for the beta torsor

The two actual skew permutations satisfy the triangle relations by the
cyclic-sum identities. The universal property therefore constructs their
action for every group word. Its second component defines the additive
shift, and the cocycle law follows from composition of these permutations.
-/

noncomputable section

open Function Set UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

variable (φ₁ φ₂ : ℍ → ℂ)
variable (h₁ : ∀ z, (∑ k ∈ Finset.range 3, φ₁ ((Triangle.generatorOnePerm ^ k) z)) = 0)
variable (h₂ : ∀ z, (∑ k ∈ Finset.range 4, φ₂ ((Triangle.generatorTwoPerm ^ k) z)) = 0)

/-- The actual skew-permutation representation determined by the two
generator functions and their proved cyclic-sum identities. -/
def triangleAdditiveRepresentation : TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  triangleLift (skewPerm Triangle.generatorOnePerm φ₁) (skewPerm Triangle.generatorTwoPerm φ₂)
    (skewPerm_pow_eq_one _ _ _ Triangle.generatorOnePerm_cube h₁)
    (skewPerm_pow_eq_one _ _ _ Triangle.generatorTwoPerm_fourth h₂)

@[simp] theorem triangleAdditiveRepresentation_generator₁ :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ triangleGenerator₁ =
      skewPerm Triangle.generatorOnePerm φ₁ :=
  triangleLift_generator₁ ..

@[simp] theorem triangleAdditiveRepresentation_generator₂ :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ triangleGenerator₂ =
      skewPerm Triangle.generatorTwoPerm φ₂ :=
  triangleLift_generator₂ ..

/-- Every word acts additively over the actual geometric triangle action. -/
theorem triangleAdditiveRepresentation_isAdditiveSkewOver (g : TriangleGroup) :
    IsAdditiveSkewOver (triangleGeometricRepresentation g)
      (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g) := by
  let H : Subgroup TriangleGroup :=
    { carrier := {g | IsAdditiveSkewOver (triangleGeometricRepresentation g)
        (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g)}
      one_mem' := by
        change IsAdditiveSkewOver (triangleGeometricRepresentation 1)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ 1)
        simpa only [map_one] using (isAdditiveSkewOver_one (X := ℍ))
      mul_mem' := by
        intro g h hg hh
        change IsAdditiveSkewOver (triangleGeometricRepresentation (g * h))
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h))
        simpa only [map_mul] using (IsAdditiveSkewOver.mul hg hh)
      inv_mem' := by
        intro g hg
        change IsAdditiveSkewOver (triangleGeometricRepresentation g⁻¹)
          (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g⁻¹)
        simpa only [map_inv] using (IsAdditiveSkewOver.inv hg) }
  have hgen : ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) ⊆ H := by
    intro g hg
    rcases hg with rfl | rfl
    · change IsAdditiveSkewOver (triangleGeometricRepresentation triangleGenerator₁)
        (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ triangleGenerator₁)
      rw [triangleGeometricRepresentation_generator₁, triangleAdditiveRepresentation_generator₁]
      exact isAdditiveSkewOver_skewPerm _ _
    · change IsAdditiveSkewOver (triangleGeometricRepresentation triangleGenerator₂)
        (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ triangleGenerator₂)
      rw [triangleGeometricRepresentation_generator₂, triangleAdditiveRepresentation_generator₂]
      exact isAdditiveSkewOver_skewPerm _ _
  have hclosure : Subgroup.closure ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup)
      ≤ H := (Subgroup.closure_le H).mpr hgen
  apply hclosure
  rw [triangle_generators_generate]
  exact Subgroup.mem_top g

/-- The genuine all-word additive shift, obtained by acting on the zero section. -/
def triangleAdditiveShift (g : TriangleGroup) (z : ℍ) : ℂ :=
  (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, 0)).2

/-- The representation covers the given geometry and translates each fibre
by its actual all-word shift. -/
theorem triangleAdditiveRepresentation_apply (g : TriangleGroup) (z : ℍ) (b : ℂ) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b) =
      (triangleGeometricRepresentation g z, b + triangleAdditiveShift φ₁ φ₂ h₁ h₂ g z) :=
  triangleAdditiveRepresentation_isAdditiveSkewOver φ₁ φ₂ h₁ h₂ g z b

theorem triangleAdditiveRepresentation_fst (g : TriangleGroup) (z : ℍ) (b : ℂ) :
    (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b)).1 =
      triangleGeometricRepresentation g z := by
  rw [triangleAdditiveRepresentation_apply]

/-- Every actual word action commutes with translation in the complex fibre. -/
theorem triangleAdditiveRepresentation_translate (g : TriangleGroup)
    (z : ℍ) (b c : ℂ) :
    triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b + c) =
      ((triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b)).1,
        (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ g (z, b)).2 + c) := by
  simp only [triangleAdditiveRepresentation_apply,
    add_assoc, add_comm, add_left_comm]

@[simp] theorem triangleAdditiveShift_one (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ 1 z = 0 := by
  simp only [triangleAdditiveShift, map_one, Equiv.Perm.one_apply]

/-- The cocycle identity is proved by composing the actual permutations. -/
theorem triangleAdditiveShift_mul (g h : TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ (g * h) z =
      triangleAdditiveShift φ₁ φ₂ h₁ h₂ g (triangleGeometricRepresentation h z) +
        triangleAdditiveShift φ₁ φ₂ h₁ h₂ h z := by
  change (triangleAdditiveRepresentation φ₁ φ₂ h₁ h₂ (g * h) (z, 0)).2 = _
  rw [map_mul, Equiv.Perm.mul_apply, triangleAdditiveRepresentation_apply,
    triangleAdditiveRepresentation_apply]
  simp only [zero_add, add_comm]

theorem triangleAdditiveShift_inv (g : TriangleGroup) (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ g⁻¹ z =
      -triangleAdditiveShift φ₁ φ₂ h₁ h₂ g (triangleGeometricRepresentation g⁻¹ z) := by
  have h := triangleAdditiveShift_mul φ₁ φ₂ h₁ h₂ g g⁻¹ z
  rw [mul_inv_cancel, triangleAdditiveShift_one] at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

@[simp] theorem triangleAdditiveShift_generator₁ (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ triangleGenerator₁ z = φ₁ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₁,
    skewPerm_apply, zero_add]

@[simp] theorem triangleAdditiveShift_generator₂ (z : ℍ) :
    triangleAdditiveShift φ₁ φ₂ h₁ h₂ triangleGenerator₂ z = φ₂ z := by
  simp only [triangleAdditiveShift, triangleAdditiveRepresentation_generator₂,
    skewPerm_apply, zero_add]

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
