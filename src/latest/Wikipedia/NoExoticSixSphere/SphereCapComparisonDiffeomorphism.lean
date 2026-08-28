import Wikipedia.NoExoticSixSphere.SphereCapComparisonIsometry
import Wikipedia.NoExoticSixSphere.SphereCapComparisonScaleHomotopy

/-!
# All positive-scale cap comparison maps are native diffeomorphisms

The axial dilations compose by multiplication and have the reciprocal
scale as inverse. Combining their native smooth inverses with the actual
fixed linear isometry proves smoothness of both directions of the original
compactification-defined homeomorphism.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem axisDilation_mul {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (x : Sphere 3) :
    axisDilation c (axisDilation d x) = axisDilation (c * d) x := by
  by_cases hx : x = antipode pinchPole
  · subst x
    rw [axisDilation_base hd, axisDilation_base hc, axisDilation_base (mul_pos hc hd)]
  · have ht : x ∈ pinchFiniteChart.target := by
      rw [pinchFiniteChart_target]
      exact hx
    obtain ⟨v, rfl⟩ : ∃ v, pinchFiniteChart v = x :=
      ⟨pinchFiniteChart.symm x, pinchFiniteChart.right_inv ht⟩
    rw [axisDilation_finite hd, axisDilation_finite hc,
      axisDilation_finite (mul_pos hc hd), smul_smul, mul_inv]

def axisDilationDiffeomorph (c : ℝ) (hc : 0 < c) :
    Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ where
  toFun := axisDilation c
  invFun := axisDilation c⁻¹
  left_inv x := by
    rw [axisDilation_mul (inv_pos.mpr hc) hc, inv_mul_cancel₀ hc.ne', axisDilation_one]
  right_inv x := by
    rw [axisDilation_mul hc (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne', axisDilation_one]
  contMDiff_toFun := contMDiff_axisDilation hc
  contMDiff_invFun := contMDiff_axisDilation (inv_pos.mpr hc)

def capPinchDiffeomorph (ε : ℝ) (hε : 0 < ε) :
    Diffeomorph (𝓡 3) (𝓡 3) (Sphere 3) (Sphere 3) ∞ :=
  (axisDilationDiffeomorph (ε / 2) (div_pos hε (by norm_num))).trans capComparisonDiffeomorph

theorem capPinchDiffeomorph_apply (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    capPinchDiffeomorph ε hε x = capPinchComparison ε hε.ne' x := by
  change capComparisonDiffeomorph (axisDilation (ε / 2) x) = _
  rw [capComparisonDiffeomorph_apply]
  exact (capPinchComparison_scale hε (by norm_num) x).symm

theorem capPinchDiffeomorph_symm_apply (ε : ℝ) (hε : 0 < ε) (x : Sphere 3) :
    (capPinchDiffeomorph ε hε).symm x = (capPinchComparison ε hε.ne').symm x := by
  apply (capPinchComparison ε hε.ne').injective
  rw [← capPinchDiffeomorph_apply ε hε, Diffeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

theorem contMDiff_capPinchComparison {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (capPinchComparison ε hε.ne') := by
  have he : (capPinchComparison ε hε.ne' : Sphere 3 → Sphere 3) =
      capPinchDiffeomorph ε hε := funext fun x ↦ (capPinchDiffeomorph_apply ε hε x).symm
  rw [he]
  exact (capPinchDiffeomorph ε hε).contMDiff_toFun

theorem contMDiff_capPinchComparison_symm {ε : ℝ} (hε : 0 < ε) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (capPinchComparison ε hε.ne').symm := by
  have he : ((capPinchComparison ε hε.ne').symm : Sphere 3 → Sphere 3) =
      (capPinchDiffeomorph ε hε).symm :=
    funext fun x ↦ (capPinchDiffeomorph_symm_apply ε hε x).symm
  rw [he]
  exact (capPinchDiffeomorph ε hε).contMDiff_invFun

end NoExoticSixSphere.SphereSumNeck
