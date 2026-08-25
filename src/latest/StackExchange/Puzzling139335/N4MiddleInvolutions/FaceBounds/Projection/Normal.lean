import StackExchange.Puzzling139335.N4MiddleInvolutions.FaceBounds.Defs

/-! Uniqueness of a unit normal on a specified side of a nonvertical tangent. -/

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- Unit normals perpendicular to the same nonvertical direction agree when
their vertical coordinates have the same sign. -/
theorem unit_normal_eq_of_tangent_of_same_sign
    {nx ny mx my dx dy : ℝ}
    (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hsign : 0 < ny * my) (hdx : dx ≠ 0)
    (htn : nx * dx + ny * dy = 0) (htm : mx * dx + my * dy = 0) :
    nx = mx ∧ ny = my := by
  have hproduct : (nx * my - mx * ny) * dx = 0 := by
    linear_combination my * htn - ny * htm
  have hdet : nx * my = mx * ny := by
    have hzero := (mul_eq_zero.mp hproduct).resolve_right hdx
    linarith
  have hsquare : ny ^ 2 = my ^ 2 := by
    linear_combination my ^ 2 * hn - ny ^ 2 * hm - (nx * my + mx * ny) * hdet
  have hy : ny = my := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with heq | heq
    · exact heq
    · rw [heq] at hsign
      nlinarith [sq_nonneg my]
  have hmy : my ≠ 0 := by
    intro hzero
    simp [hzero] at hsign
  rw [hy] at hdet
  exact ⟨mul_right_cancel₀ hmy hdet, hy⟩

/-- In particular, two upward unit normals to a nonvertical tangent agree. -/
theorem unit_normal_eq_of_tangent_of_pos
    {nx ny mx my dx dy : ℝ}
    (hn : nx ^ 2 + ny ^ 2 = 1) (hm : mx ^ 2 + my ^ 2 = 1)
    (hny : 0 < ny) (hmy : 0 < my) (hdx : dx ≠ 0)
    (htn : nx * dx + ny * dy = 0) (htm : mx * dx + my * dy = 0) :
    nx = mx ∧ ny = my :=
  unit_normal_eq_of_tangent_of_same_sign hn hm (mul_pos hny hmy) hdx htn htm

end Puzzling139335.N4MiddleInvolutions.FaceBounds
