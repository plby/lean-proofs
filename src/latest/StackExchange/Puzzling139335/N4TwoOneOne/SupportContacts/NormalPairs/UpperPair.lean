import StackExchange.Puzzling139335.N4TwoOneOne.Defs
import Mathlib.Tactic

/-!
# Equality of the upper pair of supporting normals

Two orthogonal unit normals in the upper half-plane are forced to be the
prescribed pair by the two adjacent support inequalities.
-/

namespace Puzzling139335.N4TwoOneOne.SupportContacts

private theorem positive_unit_pair_eq {x y u v : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hxy : x ^ 2 + y ^ 2 = 1) (huv : u ^ 2 + v ^ 2 = 1)
    (hcross : x * v - y * u = 0) : x = u ∧ y = v := by
  have hdot_pos : 0 < x * u + y * v :=
    add_pos (mul_pos hx hu) (mul_pos hy hv)
  have hdot_sq : (x * u + y * v) ^ 2 = 1 := by
    calc
      (x * u + y * v) ^ 2 =
          (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) -
            (x * v - y * u) ^ 2 := by ring
      _ = 1 := by rw [hxy, huv, hcross]; norm_num
  have hdot : x * u + y * v = 1 := by nlinarith
  have hdiff : (x - u) ^ 2 + (y - v) ^ 2 = 0 := by
    nlinarith [hxy, huv, hdot]
  have hxzero : (x - u) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - u), sq_nonneg (y - v)]
  have hyzero : (y - v) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - u), sq_nonneg (y - v)]
  exact ⟨sub_eq_zero.mp (sq_eq_zero_iff.mp hxzero),
    sub_eq_zero.mp (sq_eq_zero_iff.mp hyzero)⟩

/-- An orthogonal upper pair squeezed between the two prescribed support
directions equals that pair. -/
theorem upper_pair_eq {c s a b d e : ℝ}
    (hc : 0 < c) (hs : 0 < s) (hcs : c ^ 2 + s ^ 2 = 1)
    (ha : 0 < a) (hb : 0 < b) (hd : d < 0) (he : 0 < e)
    (hab : a ^ 2 + b ^ 2 = 1) (hde : d ^ 2 + e ^ 2 = 1)
    (horth : a * d + b * e = 0)
    (hfirst : b * c ≤ a * s) (hsecond : e * s ≤ (-d) * c) :
    a = c ∧ b = s ∧ d = -s ∧ e = c := by
  have henorm : e ^ 2 + (-d) ^ 2 = 1 := by nlinarith [hde]
  have hecross : a * (-d) - b * e = 0 := by nlinarith [horth]
  obtain ⟨hae, hbd⟩ :=
    positive_unit_pair_eq ha hb he (neg_pos.mpr hd) hab henorm hecross
  have hsecond' : a * s ≤ b * c := by
    simpa only [← hae, ← hbd] using hsecond
  have hcross : a * s - b * c = 0 := by linarith
  obtain ⟨hac, hbs⟩ := positive_unit_pair_eq ha hb hc hs hab hcs hcross
  refine ⟨hac, hbs, ?_, hae.symm.trans hac⟩
  linarith

end Puzzling139335.N4TwoOneOne.SupportContacts
