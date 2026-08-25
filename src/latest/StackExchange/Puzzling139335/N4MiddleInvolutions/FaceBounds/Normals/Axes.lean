import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Normals.Defs

/-! A strict-height strip cannot carry a vertical supporting unit segment. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

theorem not_mem_unitSupportingNormals_of_snd_eq_zero {K : Set Plane}
    {nx ny l h : ℝ} (hstrip : ∀ p ∈ K, l ≤ p 1 ∧ p 1 ≤ h)
    (hheight : h - l < 1) (hny : ny = 0) :
    (nx, ny) ∉ unitSupportingNormals K := by
  rintro ⟨hnorm, a, b, hface, hlen⟩
  change nx ^ 2 + ny ^ 2 = 1 at hnorm
  have hnx : nx ≠ 0 := by
    intro hz
    norm_num [hz, hny] at hnorm
  have hlevel := hface.level_eq
  simp only [supportValue, hny, zero_mul, add_zero] at hlevel
  have hx : a 0 = b 0 := mul_left_cancel₀ hnx hlevel
  have hd : dist a b = |a 1 - b 1| := by
    apply (sq_eq_sq₀ dist_nonneg (abs_nonneg _)).mp
    simpa [hx, sq_abs] using plane_dist_sq a b
  have ha := hstrip a hface.left_mem
  have hb := hstrip b hface.right_mem
  have hspan : |a 1 - b 1| ≤ h - l := by
    rw [abs_le]
    constructor <;> linarith
  rw [hd] at hlen
  linarith

end Puzzling139335.N4MiddleInvolutions.FaceBounds
