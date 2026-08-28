import Wikipedia.HopfProblem.DegreeCollapseCubicCoordinateDiffeomorph
import Wikipedia.HopfProblem.DegreeCollapseSupportedCuspModel

/-!
# Actual global coordinates straightening the embedded cusp model

The negative-parameter cusp is a graph over its first, second, and sixth
coordinates. Its source coordinate uses the constructed cubic inverse.
Subtracting the graph gives an explicit smooth ambient diffeomorphism.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization

def sourceMap (x : Vector 3) : Vector 3 := WithLp.toLp 2 ![x 0, x 1, cubic (x 2)]

def sourceInverse (x : Vector 3) : Vector 3 := WithLp.toLp 2 ![x 0, x 1, cubicInverse (x 2)]

theorem contDiff_sourceMap : ContDiff ℝ ∞ sourceMap := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_piLp_apply 2
  · exact contDiff_piLp_apply 2
  · exact contDiff_cubic.comp (contDiff_piLp_apply 2)

theorem contDiff_sourceInverse : ContDiff ℝ ∞ sourceInverse := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact contDiff_piLp_apply 2
  · exact contDiff_piLp_apply 2
  · exact contDiff_cubicInverse.comp (contDiff_piLp_apply 2)

def sourceDiffeomorph : Vector 3 ≃ₘ[ℝ] Vector 3 where
  toFun := sourceMap
  invFun := sourceInverse
  left_inv x := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact cubicInverse_cubic (x 2)
  right_inv x := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact cubic_cubicInverse (x 2)
  contMDiff_toFun := contDiff_sourceMap.contMDiff
  contMDiff_invFun := contDiff_sourceInverse.contMDiff

def targetMap (x : Vector 6) : Vector 6 :=
  WithLp.toLp 2 ![x 0, x 1, x 5, x 2 - cubicInverse (x 5) ^ 2,
    x 3 - x 0 * cubicInverse (x 5), x 4 - x 1 * cubicInverse (x 5)]

def targetInverse (x : Vector 6) : Vector 6 :=
  WithLp.toLp 2 ![x 0, x 1, x 3 + cubicInverse (x 2) ^ 2,
    x 4 + x 0 * cubicInverse (x 2), x 5 + x 1 * cubicInverse (x 2), x 2]

theorem contDiff_targetMap : ContDiff ℝ ∞ targetMap := by
  have hc (i : Fin 6) : ContDiff ℝ ∞ (fun x : Vector 6 ↦ x i) := contDiff_piLp_apply 2
  have hζ : ContDiff ℝ ∞ (fun x : Vector 6 ↦ cubicInverse (x 5)) :=
    contDiff_cubicInverse.comp (hc 5)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 5
  · exact (hc 2).sub (hζ.pow 2)
  · exact (hc 3).sub ((hc 0).mul hζ)
  · exact (hc 4).sub ((hc 1).mul hζ)

theorem contDiff_targetInverse : ContDiff ℝ ∞ targetInverse := by
  have hc (i : Fin 6) : ContDiff ℝ ∞ (fun x : Vector 6 ↦ x i) := contDiff_piLp_apply 2
  have hζ : ContDiff ℝ ∞ (fun x : Vector 6 ↦ cubicInverse (x 2)) :=
    contDiff_cubicInverse.comp (hc 2)
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · exact hc 0
  · exact hc 1
  · exact (hc 3).add (hζ.pow 2)
  · exact (hc 4).add ((hc 0).mul hζ)
  · exact (hc 5).add ((hc 1).mul hζ)
  · exact hc 2

def targetDiffeomorph : Vector 6 ≃ₘ[ℝ] Vector 6 where
  toFun := targetMap
  invFun := targetInverse
  left_inv x := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change x 2 - cubicInverse (x 5) ^ 2 + cubicInverse (x 5) ^ 2 = x 2
      ring
    · change x 3 - x 0 * cubicInverse (x 5) + x 0 * cubicInverse (x 5) = x 3
      ring
    · change x 4 - x 1 * cubicInverse (x 5) + x 1 * cubicInverse (x 5) = x 4
      ring
    · rfl
  right_inv x := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change x 3 + cubicInverse (x 2) ^ 2 - cubicInverse (x 2) ^ 2 = x 3
      ring
    · change x 4 + x 0 * cubicInverse (x 2) - x 0 * cubicInverse (x 2) = x 4
      ring
    · change x 5 + x 1 * cubicInverse (x 2) - x 1 * cubicInverse (x 2) = x 5
      ring
  contMDiff_toFun := contDiff_targetMap.contMDiff
  contMDiff_invFun := contDiff_targetInverse.contMDiff

def plane (x : Vector 3) : Vector 6 := WithLp.toLp 2 ![x 0, x 1, x 2, 0, 0, 0]

theorem straighten_base (x : Vector 3) :
    targetDiffeomorph (WhitneyCusp.map (-1) x) = plane (sourceDiffeomorph x) := by
  have hc : x 2 ^ 3 - (-1) * x 2 = cubic (x 2) := by dsimp [cubic]; ring
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hc
  · change x 2 ^ 2 - cubicInverse (x 2 ^ 3 - (-1) * x 2) ^ 2 = 0
    rw [hc, cubicInverse_cubic, sub_self]
  · change x 0 * x 2 - x 0 * cubicInverse (x 2 ^ 3 - (-1) * x 2) = 0
    rw [hc, cubicInverse_cubic, sub_self]
  · change x 1 * x 2 - x 1 * cubicInverse (x 2 ^ 3 - (-1) * x 2) = 0
    rw [hc, cubicInverse_cubic, sub_self]

end Wikipedia.HopfProblem.DegreeCollapse.SupportedCusp
