import ErdosProblems.Erdos421.BuchstabExtension
import Mathlib.Analysis.Calculus.MeanValue

/-! # A uniform Lipschitz bound for the upper Buchstab branch -/

namespace Erdos421

theorem finiteBuchstab_upper_lipschitz (n : ℕ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    |finiteBuchstab (n + 1) v - finiteBuchstab (n + 1) u| ≤ |v - u| := by
  have hd : ∀ t ∈ Set.Ici (2 : ℝ), DifferentiableAt ℝ (buchstabExtension n) t := by
    intro t ht
    have ht2 : 2 ≤ t := ht
    exact (buchstabExtension_hasDerivAt n (by linarith : t ≠ 0)).differentiableAt
  have hb : ∀ t ∈ Set.Ici (2 : ℝ), ‖deriv (buchstabExtension n) t‖ ≤ 1 := by
    intro t ht
    have ht2 : 2 ≤ t := ht
    rw [Real.norm_eq_abs]
    exact (buchstabExtension_deriv_abs_le n ht2).trans
      ((div_le_one (by linarith : 0 < t)).mpr ht2)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) hd hb
    (convex_Ici (2 : ℝ)) hu hv
  simpa only [buchstabExtension_eq n hu, buchstabExtension_eq n hv,
    Real.norm_eq_abs, one_mul] using h

end Erdos421
