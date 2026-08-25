import StackExchange.Puzzling139335.N5.FaceNormals.Defs
import StackExchange.Puzzling139335.N5.StrictFrame.Algebra
import StackExchange.Puzzling139335.N5Facet.Trigonometry

/-!
# Angle cases for the allowed non-axis unit normals

The angles are constructed from the actual unit coordinates.  The support
determinants determine their order relative to the corner-frame angle.
-/

open Set

namespace Puzzling139335.N5

/-- Every allowed unit normal with two nonzero coordinates is a frame
normal, the terminal diagonal normal, or belongs to one of the two strict
intermediate angle ranges. -/
theorem allowedNormal_angle_cases {θ nx ny : ℝ}
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.pi / 4))
    (hnorm : nx ^ 2 + ny ^ 2 = 1) (hnx : nx ≠ 0) (hny : ny ≠ 0)
    (hallowed : AllowedNormal (Real.cos θ) (Real.sin θ) nx ny) :
    (nx = Real.cos θ ∧ ny = Real.sin θ) ∨
    (nx = -Real.sin θ ∧ ny = Real.cos θ) ∨
    (∃ r : ℝ, 0 < r ∧ nx = -r ∧ ny = r) ∨
    (∃ φ : ℝ, 0 < φ ∧ φ < θ ∧ nx = Real.cos φ ∧ ny = Real.sin φ) ∨
    (∃ ψ : ℝ, θ < ψ ∧ ψ < Real.pi / 4 ∧ nx = -Real.sin ψ ∧ ny = Real.cos ψ) := by
  have hcθ := (N5Facet.acute_trig_pos hθ.1 hθ.2).1
  have hscθ := N5Facet.sin_lt_cos hθ.1 hθ.2
  rcases hallowed with hdown | hfirst | hsecond
  · exact (hnx hdown.1).elim
  · obtain ⟨hx, hy₀, hdet⟩ := hfirst
    have hy : 0 < ny := by
      by_contra h
      exact hny (le_antisymm (le_of_not_gt h) hy₀)
    have hyx : ny < nx := by
      by_contra h
      have hmul := mul_le_mul_of_nonneg_left (le_of_not_gt h) hcθ.le
      have hstrict := mul_lt_mul_of_pos_right hscθ hx
      linarith only [hmul, hdet, hstrict]
    obtain ⟨φ, hφ, hcos, hsin⟩ := StrictFrame.exists_angle_of_strict_frame hnorm hy hyx
    have hφθ : φ ≤ θ := by
      by_contra h
      have hdelta := N5Facet.sin_sub_pos hθ.1 (lt_of_not_ge h) hφ.2
      rw [Real.sin_sub, hcos, hsin] at hdelta
      nlinarith only [hdelta, hdet]
    rcases hφθ.eq_or_lt with hEq | hlt
    · left
      constructor
      · simpa only [hEq] using hcos.symm
      · simpa only [hEq] using hsin.symm
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨φ, hφ.1, hlt, hcos.symm, hsin.symm⟩)))
  · obtain ⟨hx, hy, hdet, hsum⟩ := hsecond
    rcases hsum.eq_or_lt with hzero | hpositive
    · exact Or.inr (Or.inr (Or.inl ⟨ny, hy, by linarith only [hzero], rfl⟩))
    · have hnorm' : ny ^ 2 + (-nx) ^ 2 = 1 := by nlinarith only [hnorm]
      have horder : -nx < ny := by linarith only [hpositive]
      obtain ⟨ψ, hψ, hcos, hsin⟩ := StrictFrame.exists_angle_of_strict_frame
        hnorm' (neg_pos.mpr hx) horder
      have hnxform : nx = -Real.sin ψ := by linarith only [hsin]
      have hθψ : θ ≤ ψ := by
        by_contra h
        have hdelta := N5Facet.sin_sub_pos hψ.1 (lt_of_not_ge h) hθ.2
        rw [Real.sin_sub, hcos, hsin] at hdelta
        nlinarith only [hdelta, hdet]
      rcases hθψ.eq_or_lt with hEq | hlt
      · refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · simpa only [hEq] using hnxform
        · simpa only [hEq] using hcos.symm
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ, hlt, hψ.2, hnxform, hcos.symm⟩)))

end Puzzling139335.N5
