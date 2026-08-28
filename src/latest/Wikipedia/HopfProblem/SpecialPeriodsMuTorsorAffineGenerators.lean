import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauUniqueness
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# The actual affine generators of the special μ torsor

The two maps on `ℍ × ℂ` are genuine permutations. The covariance laws of
the supplied upper-half-plane map imply their order-three and order-four
relations, so the free-product universal property gives an actual group
representation. Their product leaves the fibre coordinate unchanged.
-/

noncomputable section

open Set UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor

/-- An invertible affine map on each fibre over a base permutation. -/
def affinePermutation {B : Type*} (e : Equiv.Perm B) (a : B → ℂˣ) (b : B → ℂ) :
    Equiv.Perm (B × ℂ) where
  toFun p := (e p.1, (a p.1 : ℂ) * p.2 + b p.1)
  invFun p := (e.symm p.1, (a (e.symm p.1) : ℂ)⁻¹ * (p.2 - b (e.symm p.1)))
  left_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.symm_apply_apply z
    · simp only [Equiv.symm_apply_apply]
      rw [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ (a z).ne_zero, one_mul]
  right_inv := by
    rintro ⟨z, u⟩
    apply Prod.ext
    · exact e.apply_symm_apply z
    · dsimp
      rw [← mul_assoc, mul_inv_cancel₀ (a (e.symm z)).ne_zero, one_mul, sub_add_cancel]

@[simp] theorem affinePermutation_apply {B : Type*}
    (e : Equiv.Perm B) (a : B → ℂˣ) (b : B → ℂ) (z : B) (u : ℂ) :
    affinePermutation e a b (z, u) = (e z, (a z : ℂ) * u + b z) := rfl

variable (τ : ℍ → ℍ)

def generatorOneScale (z : ℍ) : ℂˣ :=
  Units.mk0 (-1 / (τ z : ℂ)) (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (τ z).ne_zero)

def generatorTwoScale (z : ℍ) : ℂˣ :=
  Units.mk0 (1 / (τ z : ℂ)) (div_ne_zero one_ne_zero (τ z).ne_zero)

def generatorOneShift (z : ℍ) : ℂ := 1 / (τ z : ℂ)

def generatorTwoShift (_z : ℍ) : ℂ := 1

@[simp] theorem generatorOneScale_val (z : ℍ) :
    (generatorOneScale τ z : ℂ) = -1 / (τ z : ℂ) := rfl

@[simp] theorem generatorTwoScale_val (z : ℍ) :
    (generatorTwoScale τ z : ℂ) = 1 / (τ z : ℂ) := rfl

def generatorOne : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation Triangle.generatorOnePerm (generatorOneScale τ) (generatorOneShift τ)

def generatorTwo : Equiv.Perm (ℍ × ℂ) :=
  affinePermutation Triangle.generatorTwoPerm (generatorTwoScale τ) generatorTwoShift

@[simp] theorem generatorOne_apply (z : ℍ) (u : ℂ) :
    generatorOne τ (z, u) = (Triangle.generatorOneSL • z, (1 - u) / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (-1 / (τ z : ℂ)) * u + 1 / (τ z : ℂ) = _
    ring

@[simp] theorem generatorTwo_apply (z : ℍ) (u : ℂ) :
    generatorTwo τ (z, u) = (Triangle.generatorTwoSL • z, 1 + u / (τ z : ℂ)) := by
  apply Prod.ext
  · rfl
  · change (1 / (τ z : ℂ)) * u + 1 = _
    ring

variable {τ} (hτ : TauCovariant τ)

include hτ

theorem generatorOne_cube : generatorOne τ ^ 3 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorOne τ (generatorOne τ (generatorOne τ (z, u))) = (z, u)
  simp only [generatorOne_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) Triangle.generatorOnePerm_cube
  · dsimp
    rw [hτ.1 (Triangle.generatorOneSL • z), hτ.1 z]
    have ht : (τ z : ℂ) ≠ 0 := (τ z).ne_zero
    have ht1 : (τ z : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr
      (by simpa only [Int.cast_one] using (τ z).ne_intCast 1)
    field_simp [ht, ht1]
    ring

theorem generatorTwo_fourth : generatorTwo τ ^ 4 = 1 := by
  apply Equiv.ext
  rintro ⟨z, u⟩
  change generatorTwo τ (generatorTwo τ (generatorTwo τ (generatorTwo τ (z, u)))) = (z, u)
  simp only [generatorTwo_apply]
  apply Prod.ext
  · exact congrArg (fun e : Equiv.Perm ℍ => e z) Triangle.generatorTwoPerm_fourth
  · dsimp
    rw [hτ.2 (Triangle.generatorTwoSL • (Triangle.generatorTwoSL • z)),
      hτ.2 (Triangle.generatorTwoSL • z), hτ.2 z]
    field_simp [(τ z).ne_zero]
    ring

/-- The generator relations have been proved before applying the actual
free-product universal property. -/
def representation : TriangleGroup →* Equiv.Perm (ℍ × ℂ) :=
  triangleLift (generatorOne τ) (generatorTwo τ) (generatorOne_cube hτ) (generatorTwo_fourth hτ)

@[simp] theorem representation_generator₁ : representation hτ triangleGenerator₁ = generatorOne τ :=
  triangleLift_generator₁ ..

@[simp] theorem representation_generator₂ : representation hτ triangleGenerator₂ = generatorTwo τ :=
  triangleLift_generator₂ ..

theorem generatorOne_mul_generatorTwo_apply (z : ℍ) (u : ℂ) :
    (generatorOne τ * generatorTwo τ) (z, u) =
      (Triangle.generatorOneSL • (Triangle.generatorTwoSL • z), u) := by
  change generatorOne τ (generatorTwo τ (z, u)) = _
  rw [generatorTwo_apply, generatorOne_apply, hτ.2 z]
  congr 1
  field_simp [(τ z).ne_zero]
  ring

/-- The inverse product is the actual cusp element, and it also fixes the
fibre coordinate. No separate cusp cocycle is assumed. -/
theorem representation_cusp_snd (z : ℍ) (u : ℂ) :
    (representation hτ triangleCuspGenerator (z, u)).2 = u := by
  rw [representation, triangleLift_cusp]
  have he := (generatorOne τ * generatorTwo τ).apply_symm_apply (z, u)
  have hc := congrArg Prod.snd he
  rw [generatorOne_mul_generatorTwo_apply hτ] at hc
  exact hc

section Holomorphic

omit hτ

variable (hτa : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)

include hτa

theorem generatorOneScale_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorOneScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

theorem generatorTwoScale_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (generatorTwoScale τ z : ℂ)) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

theorem generatorOneShift_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (generatorOneShift τ) :=
  contMDiff_const.div₀ (UpperHalfPlane.contMDiff_coe.comp hτa) (fun z => (τ z).ne_zero)

omit hτa in
theorem generatorTwoShift_holomorphic :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω generatorTwoShift := contMDiff_const

end Holomorphic

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor
