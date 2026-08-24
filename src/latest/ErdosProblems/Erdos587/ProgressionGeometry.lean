import ErdosProblems.Erdos587.WideRectangle

/-!
# Integer root windows in primitive progressions

The inner rectangle is chosen with `0 <= x < floor(H/4)`. Its root
window runs from `sqrt(t+u*floor(H/4))+1` through `sqrt(t+v*J)`.
Every congruence solution in this rectangle lifts inside the progression.
-/

namespace Erdos587

lemma nat_root_window_width_bound {a b T : ℕ} (hab : a ≤ b) (hbT : b ≤ T) :
    b - a < 2 * (Nat.sqrt T + 1) * (Nat.sqrt b - Nat.sqrt a + 1) := by
  have hsw : Nat.sqrt a ≤ Nat.sqrt b := Nat.sqrt_le_sqrt hab
  have hwT : Nat.sqrt b ≤ Nat.sqrt T := Nat.sqrt_le_sqrt hbT
  have ha := Nat.sqrt_le' a
  have hb := Nat.lt_succ_sqrt b
  have hd := Nat.sub_add_cancel hsw
  have hba := Nat.sub_add_cancel hab
  have hsum : Nat.sqrt b + 1 + Nat.sqrt a ≤ 2 * (Nat.sqrt T + 1) := by omega
  have hmul := Nat.mul_le_mul_left (Nat.sqrt b - Nat.sqrt a + 1) hsum
  nlinarith

lemma primitive_progression_root_rectangle
    {t u v H J x z : ℕ} (hx : x < H / 4)
    (hzlo : Nat.sqrt (t + u * (H / 4)) + 1 ≤ z)
    (hzhi : z ≤ Nat.sqrt (t + v * J)) :
    0 < z ∧ t + u * x ≤ z ^ 2 ∧ z ^ 2 ≤ t + u * x + v * J := by
  have hlow := Nat.lt_succ_sqrt (t + u * (H / 4))
  have hhigh := Nat.sqrt_le' (t + v * J)
  have hzx := Nat.pow_le_pow_left hzlo 2
  have hzy := Nat.pow_le_pow_left hzhi 2
  have hux : u * x ≤ u * (H / 4) := Nat.mul_le_mul_left u hx.le
  refine ⟨by omega, ?_, ?_⟩ <;> nlinarith

lemma primitive_root_window_span {t u v H J T : ℕ}
    (hambient : t + u * H + v * J ≤ T) (horient : u * H ≤ v * J) :
    v * J < 4 * (Nat.sqrt T + 1) *
      (Nat.sqrt (t + v * J) - Nat.sqrt (t + u * (H / 4)) + 1) := by
  have hdiv : 4 * (H / 4) ≤ H := by omega
  have hquarter : 4 * (u * (H / 4)) ≤ v * J := by
    calc
      _ = u * (4 * (H / 4)) := by ring
      _ ≤ u * H := Nat.mul_le_mul_left u hdiv
      _ ≤ v * J := horient
  have hab : t + u * (H / 4) ≤ t + v * J := by omega
  have hwidth := nat_root_window_width_bound hab (by omega : t + v * J ≤ T)
  have hdiff := Nat.sub_add_cancel hab
  nlinarith

lemma primitive_root_window_real_lower {t u v H J T : ℕ} {C : ℝ}
    (hC : 0 < C) (hT : 0 < T)
    (hambient : t + u * H + v * J ≤ T) (horient : u * H ≤ v * J)
    (hspan : (T : ℝ) ≤ C * ((u * H + v * J : ℕ) : ℝ))
    (hlarge : 32 * C ≤ Real.sqrt T) :
    (1 / (32 * C)) * Real.sqrt T ≤
      ((Nat.sqrt (t + v * J) - Nat.sqrt (t + u * (H / 4)) : ℕ) : ℝ) := by
  let L := Nat.sqrt (t + v * J) - Nat.sqrt (t + u * (H / 4))
  have hroot : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hT)
  have hroot1 : 1 ≤ Real.sqrt (T : ℝ) := by
    have hh := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ T by exact_mod_cast hT)
    simpa only [Real.sqrt_one] using hh
  have hsqrt : ((Nat.sqrt T + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt T := by
    have hh := Real.nat_sqrt_le_real_sqrt (a := T)
    push_cast
    linarith
  have hspan' : (T : ℝ) ≤ 2 * C * ((v * J : ℕ) : ℝ) := by
    apply hspan.trans
    have hh : ((u * H : ℕ) : ℝ) ≤ ((v * J : ℕ) : ℝ) := by exact_mod_cast horient
    push_cast at *
    nlinarith
  have hwidth : ((v * J : ℕ) : ℝ) < 4 * ((Nat.sqrt T + 1 : ℕ) : ℝ) * (L + 1) := by
    exact_mod_cast primitive_root_window_span hambient horient
  have hTbound : (T : ℝ) < 16 * C * Real.sqrt T * (L + 1) := by
    calc
      _ ≤ 2 * C * ((v * J : ℕ) : ℝ) := hspan'
      _ < 2 * C * (4 * ((Nat.sqrt T + 1 : ℕ) : ℝ) * (L + 1)) :=
        mul_lt_mul_of_pos_left hwidth (by positivity)
      _ ≤ 2 * C * (4 * (2 * Real.sqrt T) * (L + 1)) := by gcongr
      _ = _ := by ring
  have hcancel : Real.sqrt T < 16 * C * ((L : ℝ) + 1) := by
    apply (mul_lt_mul_iff_left₀ hroot).mp
    calc
      Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (Nat.cast_nonneg T)
      _ < 16 * C * Real.sqrt T * (L + 1) := hTbound
      _ = (16 * C * (L + 1)) * Real.sqrt T := by ring
  change (1 / (32 * C)) * Real.sqrt T ≤ (L : ℝ)
  rw [one_div, mul_comm, ← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * C)).mpr
  nlinarith

lemma exists_positive_square_in_progression_of_root_rectangle
    {t u v H J x z : ℕ} (hv : 0 < v) (hx : x < H / 4)
    (hzlo : Nat.sqrt (t + u * (H / 4)) + 1 ≤ z)
    (hzhi : z ≤ Nat.sqrt (t + v * J))
    (hcong : z ^ 2 ≡ t + u * x [MOD v]) :
    ∃ x ≤ H, ∃ y ≤ J, ∃ z : ℕ, 0 < z ∧ z ^ 2 = t + u * x + v * y := by
  obtain ⟨hzpos, hlo, hhi⟩ := primitive_progression_root_rectangle hx hzlo hzhi
  obtain ⟨y, hy, heq⟩ := exists_progression_coordinate_of_square_congruence hv hcong hlo hhi
  exact ⟨x, hx.le.trans (Nat.div_le_self H 4), y, hy, z, hzpos, heq⟩

end Erdos587
