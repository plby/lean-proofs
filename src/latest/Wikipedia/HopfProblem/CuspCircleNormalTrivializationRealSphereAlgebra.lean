import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Explicit conformal stereographic coordinates on the real unit two-sphere

The two complex-line parametrizations below use a real linear isometry into
the equatorial hyperplane. Their transition is exactly complex inversion.
This avoids the arbitrary linear map in a merely topological one-point
compactification comparison.
-/

noncomputable section

open Set Metric Submodule
open scoped ContDiff ComplexConjugate

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere

abbrev SphereAmbient := EuclideanSpace ℝ (Fin 3)
abbrev UnitTwoSphere := sphere (0 : SphereAmbient) 1

local instance ambientFinrank : Fact (Module.finrank ℝ SphereAmbient = 2 + 1) :=
  ⟨by simp⟩

/-- A fixed genuine north pole of the Euclidean unit sphere. -/
def northVector : SphereAmbient := EuclideanSpace.single 0 1

@[simp] theorem norm_northVector : ‖northVector‖ = 1 := by
  simp [northVector]

theorem northVector_ne_zero : northVector ≠ 0 := by
  intro h
  simpa [h] using norm_northVector

/-- The corresponding point of the actual sphere. -/
def north : UnitTwoSphere := ⟨northVector, by simp⟩

/-- An isometric identification with the actual equatorial hyperplane. -/
def equatorEquiv : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ northVector)ᗮ :=
  Complex.orthonormalBasisOneI.repr.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton 2 northVector_ne_zero).repr.symm

/-- The finite stereographic chart, with the normalization giving reciprocal overlap. -/
def left (z : ℂ) : UnitTwoSphere :=
  stereoInvFun norm_northVector ((2 : ℝ) • equatorEquiv z)

/-- The other chart is the antipodal image after reflected complex conjugation. -/
def right (z : ℂ) : UnitTwoSphere := -left (-conj z)

/-- The usual rational stereographic expression in the ambient real vector space. -/
theorem left_coe (z : ℂ) :
    (left z : SphereAmbient) =
      (2 / (Complex.normSq z + 1)) • (equatorEquiv z : SphereAmbient) +
      ((Complex.normSq z - 1) / (Complex.normSq z + 1)) • northVector := by
  have hd : Complex.normSq z + 1 ≠ 0 := by
    have := Complex.normSq_nonneg z
    positivity
  have hd4 : (2 : ℝ) ^ 2 * Complex.normSq z + 4 ≠ 0 := by
    have := Complex.normSq_nonneg z
    positivity
  change (stereoInvFun norm_northVector ((2 : ℝ) • equatorEquiv z) : SphereAmbient) = _
  rw [stereoInvFun_apply]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    LinearIsometryEquiv.norm_map, Submodule.coe_smul, mul_pow,
    ← Complex.normSq_eq_norm_sq, smul_add, smul_smul]
  congr 1 <;> congr 1 <;> field_simp [hd, hd4] <;> ring

@[simp] theorem left_zero : left 0 = -north := by
  apply Subtype.ext
  simp [left_coe, north]

@[simp] theorem right_zero : right 0 = north := by
  simp [right]

theorem left_ne_north (z : ℂ) : left z ≠ north :=
  stereoInvFun_ne_north_pole norm_northVector _

theorem left_continuous : Continuous left :=
  (continuous_stereoInvFun norm_northVector).comp
    (equatorEquiv.continuous.const_smul (2 : ℝ))

theorem left_injective : Function.Injective left := by
  intro z w h
  have he := congrArg (stereographic norm_northVector) h
  change stereographic norm_northVector
      ((stereographic norm_northVector).symm ((2 : ℝ) • equatorEquiv z)) =
    stereographic norm_northVector
      ((stereographic norm_northVector).symm ((2 : ℝ) • equatorEquiv w)) at he
  rw [(stereographic norm_northVector).right_inv (mem_univ _),
    (stereographic norm_northVector).right_inv (mem_univ _)] at he
  exact equatorEquiv.injective ((smul_right_injective _ (by norm_num : (2 : ℝ) ≠ 0)) he)

theorem right_continuous : Continuous right :=
  left_continuous.comp (Complex.continuous_conj.neg) |>.neg

theorem right_injective : Function.Injective right := by
  intro z w h
  apply Complex.conjLIE.injective
  exact neg_injective (left_injective (neg_injective h))

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealSphere
