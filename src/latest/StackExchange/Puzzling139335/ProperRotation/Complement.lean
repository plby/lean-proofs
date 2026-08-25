import Mathlib

/-!
# Complementary scalar inequalities for proper rotations

All hypotheses below are inequalities on finitely many real coordinates.
No geometric or topological conclusion is assumed.
-/

namespace Puzzling139335.ProperRotation

/-- The first complementary numerator has a uniform positive lower bound in
the ordered acute-sum configuration. -/
theorem nt_lower_bound_of_coarse_bounds
    (c s d q a b u v w z : ℝ)
    (hc : 0 < c) (hc_lt : c < 3 / 10)
    (hs : 9 / 10 < s) (hs_lt : s < 1)
    (_hd : 0 < d) (hq : 0 < q)
    (ha : 2 / 9 < a) (hb : 0 ≤ b)
    (hdelta : s ≤ s * d + c * q)
    (hu : s * a ≤ u) (hw : d + q * b ≤ w)
    (hv : v ≤ 1 / 2 - s - c * b) (hz : z ≤ 1 / 2 - q) :
    3 / 20 < -s * (1 - u - w) - c * (v + z) := by
  have hs0 : 0 < s := by linarith only [hs]
  have ha0 : 0 < a := by linarith only [ha]
  have hsum : s * a + d + q * b - 1 ≤ u + w - 1 := by
    linarith only [hu, hw]
  have hvs : v + z ≤ 1 - s - c * b - q := by
    linarith only [hv, hz]
  have hmulU := mul_le_mul_of_nonneg_left hsum hs0.le
  have hmulV := mul_le_mul_of_nonneg_left hvs hc.le
  have hraw :
      s ^ 2 * a + (s * q + c ^ 2) * b +
          (s * d + c * q - s) - c * (1 - s) ≤
        -s * (1 - u - w) - c * (v + z) := by
    nlinarith only [hmulU, hmulV]
  have hcoef : 0 ≤ (s * q + c ^ 2) * b := by positivity
  have hmain :
      s ^ 2 * a - c * (1 - s) ≤
        -s * (1 - u - w) - c * (v + z) := by
    linarith only [hraw, hcoef, hdelta]
  have hsq : (81 / 100 : ℝ) < s ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hs) (show 0 < s + 9 / 10 by linarith only [hs])
    nlinarith only [hp]
  have hprod1 := mul_lt_mul_of_pos_right hsq ha0
  have hprod2 := mul_lt_mul_of_pos_left ha (show (0 : ℝ) < 81 / 100 by norm_num)
  have hprod : (9 / 50 : ℝ) < s ^ 2 * a := by
    nlinarith only [hprod1, hprod2]
  have hpenalty : c * (1 - s) ≤ (3 / 100 : ℝ) := by
    have hp := mul_le_mul hc_lt.le (show 1 - s ≤ (1 / 10 : ℝ) by linarith only [hs])
      (sub_nonneg.mpr hs_lt.le) (show (0 : ℝ) ≤ 3 / 10 by norm_num)
    norm_num at hp ⊢
    exact hp
  linarith only [hmain, hprod, hpenalty]

/-- The second complementary numerator is separated from the denominator
in the ordered acute-sum configuration. -/
theorem ns_upper_gap_of_coarse_bounds
    (c s d q a b u v w z : ℝ)
    (_hc : 0 < c) (hs : 9 / 10 < s)
    (hd : 9 / 10 < d) (hq : 0 < q)
    (ha : 2 / 9 < a) (hb : 0 ≤ b)
    (hsd : s ≤ d) (hsum : 1 < c + s)
    (hu : s * a ≤ u) (hw : d + q * b ≤ w)
    (hv : -(1 / 2 : ℝ) ≤ v) (hz : d * a - 1 / 2 ≤ z) :
    9 / 100 < (s * d + c * q) -
      (q * (1 - u - w) - d * (v + z)) := by
  have hs0 : 0 < s := by linarith only [hs]
  have hd0 : 0 < d := by linarith only [hd]
  have ha0 : 0 < a := by linarith only [ha]
  have hsumU : s * a + d + q * b ≤ u + w := by
    linarith only [hu, hw]
  have hsumV : d * a - 1 ≤ v + z := by
    linarith only [hv, hz]
  have hmulU := mul_le_mul_of_nonneg_left hsumU hq.le
  have hmulV := mul_le_mul_of_nonneg_left hsumV hd0.le
  have hraw :
      a * d ^ 2 - d * (1 - s) + q * (c + d - 1 + a * s) + q ^ 2 * b ≤
        (s * d + c * q) - (q * (1 - u - w) - d * (v + z)) := by
    nlinarith only [hmulU, hmulV]
  have has : 0 < a * s := mul_pos ha0 hs0
  have hinside : 0 < c + d - 1 + a * s := by
    linarith only [hsd, hsum, has]
  have hterm1 : 0 ≤ q * (c + d - 1 + a * s) := (mul_pos hq hinside).le
  have hterm2 : 0 ≤ q ^ 2 * b := mul_nonneg (sq_nonneg q) hb
  have hmain :
      d * (a * d - (1 - s)) ≤
        (s * d + c * q) - (q * (1 - u - w) - d * (v + z)) := by
    nlinarith only [hraw, hterm1, hterm2]
  have hp1 := mul_lt_mul_of_pos_right ha hd0
  have hp2 := mul_lt_mul_of_pos_left hd (show (0 : ℝ) < 2 / 9 by norm_num)
  have had : (1 / 5 : ℝ) < a * d := by
    nlinarith only [hp1, hp2]
  have hinner : (1 / 10 : ℝ) < a * d - (1 - s) := by
    linarith only [had, hs]
  have hp3 := mul_lt_mul_of_pos_left hinner hd0
  have hp4 := mul_lt_mul_of_pos_right hd (show (0 : ℝ) < 1 / 10 by norm_num)
  have hprod : (9 / 100 : ℝ) < d * (a * d - (1 - s)) := by
    nlinarith only [hp3, hp4]
  linarith only [hmain, hprod]

/-- A strict obtuse-sum supporting half-plane can meet the other source
quadrant only at its origin. This is the algebraic singleton step. -/
theorem nonneg_left_signed_iff
    (n Δ E x y : ℝ) (hn : n ≤ 0) (hΔ : 0 < Δ) (hE : E < 0)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ n - Δ * x + E * y ↔ n = 0 ∧ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    have hdx : 0 ≤ Δ * x := mul_nonneg hΔ.le hx
    have hey : E * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hE.le hy
    have hn0 : n = 0 := by linarith only [h, hn, hdx, hey]
    have hdx0 : Δ * x = 0 := by linarith only [h, hn, hdx, hey]
    have hey0 : E * y = 0 := by linarith only [h, hn, hdx, hey]
    exact ⟨hn0, (mul_eq_zero.mp hdx0).resolve_left (ne_of_gt hΔ),
      (mul_eq_zero.mp hey0).resolve_left (ne_of_lt hE)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- The corresponding strict supporting half-plane at the right endpoint
can meet the source strip only at (1,0). -/
theorem nonneg_right_signed_iff
    (n Δ E x y : ℝ) (hn : Δ ≤ n) (hΔ : 0 < Δ) (hE : E < 0)
    (hx : x ≤ 1) (hy : 0 ≤ y) :
    0 ≤ -n + Δ * x + E * y ↔ n = Δ ∧ x = 1 ∧ y = 0 := by
  have hbase := nonneg_left_signed_iff (Δ - n) Δ E (1 - x) y
    (sub_nonpos.mpr hn) hΔ hE (sub_nonneg.mpr hx) hy
  have heq : (Δ - n) - Δ * (1 - x) + E * y = -n + Δ * x + E * y := by ring
  rw [heq] at hbase
  constructor
  · intro h
    obtain ⟨h1, h2, h3⟩ := hbase.mp h
    exact ⟨by linarith only [h1], by linarith only [h2], h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-- Two distinct supported source points exclude a nonpositive first numerator. -/
theorem left_numerator_pos_of_two_contacts
    (n Δ E x₁ y₁ x₂ y₂ : ℝ) (hΔ : 0 < Δ) (hE : E < 0)
    (hx₁ : 0 ≤ x₁) (hy₁ : 0 ≤ y₁) (hx₂ : 0 ≤ x₂) (hy₂ : 0 ≤ y₂)
    (hne : (x₁, y₁) ≠ (x₂, y₂))
    (h₁ : 0 ≤ n - Δ * x₁ + E * y₁)
    (h₂ : 0 ≤ n - Δ * x₂ + E * y₂) : 0 < n := by
  by_contra! hn
  obtain ⟨_, h1x, h1y⟩ := (nonneg_left_signed_iff n Δ E x₁ y₁ hn hΔ hE hx₁ hy₁).mp h₁
  obtain ⟨_, h2x, h2y⟩ := (nonneg_left_signed_iff n Δ E x₂ y₂ hn hΔ hE hx₂ hy₂).mp h₂
  exact hne (Prod.ext (h1x.trans h2x.symm) (h1y.trans h2y.symm))

/-- Two distinct supported source points put the other numerator below the denominator. -/
theorem right_numerator_lt_of_two_contacts
    (n Δ E x₁ y₁ x₂ y₂ : ℝ) (hΔ : 0 < Δ) (hE : E < 0)
    (hx₁ : x₁ ≤ 1) (hy₁ : 0 ≤ y₁) (hx₂ : x₂ ≤ 1) (hy₂ : 0 ≤ y₂)
    (hne : (x₁, y₁) ≠ (x₂, y₂))
    (h₁ : 0 ≤ -n + Δ * x₁ + E * y₁)
    (h₂ : 0 ≤ -n + Δ * x₂ + E * y₂) : n < Δ := by
  by_contra! hn
  obtain ⟨_, h1x, h1y⟩ := (nonneg_right_signed_iff n Δ E x₁ y₁ hn hΔ hE hx₁ hy₁).mp h₁
  obtain ⟨_, h2x, h2y⟩ := (nonneg_right_signed_iff n Δ E x₂ y₂ hn hΔ hE hx₂ hy₂).mp h₂
  exact hne (Prod.ext (h1x.trans h2x.symm) (h1y.trans h2y.symm))

/-- Signed distance numerator from the first base to a point in the second
placement, written without geometric types. -/
theorem left_signed_identity (c s d q u v w z x y : ℝ) :
    c * ((1 / 2 - z - q * x + d * y) - (1 / 2 + v)) -
      s * ((1 - w + d * x + q * y) - u) =
    (-s * (1 - u - w) - c * (v + z)) -
      (s * d + c * q) * x + (c * d - s * q) * y := by
  ring

/-- The analogous signed numerator from the second base to a point in the
first placement. -/
theorem right_signed_identity (c s d q u v w z x y : ℝ) :
    d * ((1 / 2 + v + s * x + c * y) - (1 / 2 - z)) +
      q * ((u + c * x - s * y) - (1 - w)) =
    -(q * (1 - u - w) - d * (v + z)) +
      (s * d + c * q) * x + (c * d - s * q) * y := by
  ring

end Puzzling139335.ProperRotation
