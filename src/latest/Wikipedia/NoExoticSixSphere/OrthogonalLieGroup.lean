import Wikipedia.NoExoticSixSphere.OrthogonalSmoothness
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# The orthogonal operators form a Lie group

The group operations are the previously verified composition and inverse, and
smoothness is checked in the original ambient operator space using the Cayley
atlas. No abstract group is substituted for the orthogonal operator space.
-/

open scoped Manifold ContDiff

namespace NoExoticSixSphere.OrthogonalLieGroup

open GLOrthonormalization OrthogonalPaths CayleyTransform OrthogonalSmoothness

noncomputable instance group (n : ℕ) : Group (OrthogonalOperators n) where
  one := identity n
  mul := OrthogonalPaths.mul
  inv := inverse
  mul_assoc := OrthogonalPaths.mul_assoc
  one_mul := identity_mul
  mul_one := mul_identity
  inv_mul_cancel := inverse_mul

variable {n : ℕ}

theorem contMDiff_multiplication :
    ContMDiff (𝓘(ℝ, SkewOperators n).prod 𝓘(ℝ, SkewOperators n))
      𝓘(ℝ, SkewOperators n) ∞
      (fun p : OrthogonalOperators n × OrthogonalOperators n ↦ p.1 * p.2) := by
  apply contMDiff_iff_operator.mpr
  exact (OrthogonalSmoothness.contMDiff_operator.comp contMDiff_fst).clm_comp
    (OrthogonalSmoothness.contMDiff_operator.comp contMDiff_snd)

theorem contMDiff_inversion :
    ContMDiff 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, SkewOperators n) ∞
      (fun a : OrthogonalOperators n ↦ a⁻¹) := by
  apply contMDiff_iff_operator.mpr
  intro a
  have hi : ContMDiffAt 𝓘(ℝ, Vector n →L[ℝ] Vector n)
      𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ ContinuousLinearMap.inverse a.1.1 :=
    a.1.2.contDiffAt_map_inverse.contMDiffAt
  have hs := hi.comp a OrthogonalSmoothness.contMDiff_operator.contMDiffAt
  convert hs using 1
  funext b
  exact inverse_operator b

noncomputable instance lieGroup (n : ℕ) :
    LieGroup 𝓘(ℝ, SkewOperators n) ∞ (OrthogonalOperators n) where
  contMDiff_mul := contMDiff_multiplication
  contMDiff_inv := contMDiff_inversion

instance topologicalGroup (n : ℕ) : IsTopologicalGroup (OrthogonalOperators n) :=
  topologicalGroup_of_lieGroup (I := 𝓘(ℝ, SkewOperators n)) (n := ∞)

end NoExoticSixSphere.OrthogonalLieGroup
