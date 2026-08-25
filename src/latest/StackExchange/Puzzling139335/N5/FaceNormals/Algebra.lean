import StackExchange.Puzzling139335.N5.FaceNormals.Defs

/-!
# The scalar complement of the three excluded normal cones
-/

namespace Puzzling139335.N5

/-- A unit normal outside the three open cones belongs to one of the three
remaining families.  The circle equation for `c, s` is retained for the
geometric interface; only their strict ordering is needed in this step. -/
theorem allowedNormal_of_excluded_cones {c s nx ny : ℝ}
    (_hcs : c ^ 2 + s ^ 2 = 1) (hs : 0 < s) (hsc : s < c)
    (hn : nx ^ 2 + ny ^ 2 = 1)
    (hA : ¬ (nx < 0 ∧ nx + ny < 0))
    (hB : ¬ (0 < nx ∧ ny < 0))
    (hC : ¬ (0 < c * nx + s * ny ∧ 0 < -s * nx + c * ny)) :
    AllowedNormal c s nx ny := by
  have hc : 0 < c := lt_trans hs hsc
  unfold AllowedNormal
  rcases lt_trichotomy nx 0 with hnx | hnx | hnx
  · have hsum : 0 ≤ nx + ny := by
      by_contra h
      exact hA ⟨hnx, by linarith⟩
    have hny : 0 < ny := by linarith only [hnx, hsum]
    have hbeta : 0 < -s * nx + c * ny := by
      nlinarith only [mul_pos hs (neg_pos.mpr hnx), mul_pos hc hny]
    have halpha : c * nx + s * ny ≤ 0 := by
      by_contra h
      exact hC ⟨by linarith, hbeta⟩
    exact Or.inr (Or.inr ⟨hnx, hny, halpha, hsum⟩)
  · subst nx
    have hny : ny = 1 ∨ ny = -1 :=
      sq_eq_one_iff.mp (by simpa using hn)
    rcases hny with hny | hny
    · exfalso
      exact hC ⟨by simpa [hny] using hs, by simpa [hny] using hc⟩
    · exact Or.inl ⟨rfl, hny⟩
  · have hny : 0 ≤ ny := by
      by_contra h
      exact hB ⟨hnx, by linarith⟩
    have halpha : 0 < c * nx + s * ny :=
      add_pos_of_pos_of_nonneg (mul_pos hc hnx) (mul_nonneg hs.le hny)
    have hbeta : -s * nx + c * ny ≤ 0 := by
      by_contra h
      exact hC ⟨halpha, by linarith⟩
    exact Or.inr (Or.inl ⟨hnx, hny, by nlinarith only [hbeta]⟩)

end Puzzling139335.N5
