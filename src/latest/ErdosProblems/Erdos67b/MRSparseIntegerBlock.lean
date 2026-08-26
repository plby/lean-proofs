import ErdosProblems.Erdos67b.LogSecondDerivativeReal

/-!
# Square-root cancellation in the critical integer range

This optimizes the proved real-start van der Corput estimate uniformly
over every prefix of a dyadic block. Taking the minimum with the prefix
length is essential: a short final prefix need not admit the full lag budget.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

open LogSecondDerivativeReal

theorem mrRealLogBlock_sq_le_of_lag
    {a U : ℝ} {P H : ℕ} (ha : 1 ≤ a) (hU : 0 < U) (hUa : U ≤ 8 * a)
    (hPU : (P : ℝ) ≤ U) (hH : 0 < H) (hHP : H ≤ P)
    (hscale : 8 * (H : ℝ) * a ≤ U ^ 2)
    (hlag : H = P ∨ U ^ 2 ≤ 512 * a * H) :
    ‖∑ n ∈ range P, realBlockPhase a U n‖ ^ 2 ≤
      148480 * a * (1 + Real.log (8 * a)) := by
  let S : ℝ := ‖∑ n ∈ range P, realBlockPhase a U n‖
  let L : ℝ := 1 + Real.log (8 * a)
  have ha0 : 0 < a := by linarith
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hHPR : (H : ℝ) ≤ P := by exact_mod_cast hHP
  have hL1 : 1 ≤ L := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 8 * a by linarith)
    dsimp only [L]
    linarith
  have hlog : 1 + Real.log (H : ℝ) ≤ L := by
    have hh := Real.log_le_log hHR ((hHPR.trans hPU).trans hUa)
    dsimp only [L]
    linarith
  have hratio : U ^ 2 / a ≤ 8 * U := by
    apply (div_le_iff₀ ha0).mpr
    nlinarith
  have hratio64 : U ^ 2 / a ≤ 64 * a := hratio.trans (by linarith)
  have hraw := norm_realLogBlock_sq_vanDerCorput hH hHP ha0 hU hPU hscale
  have hcancel : (H : ℝ) * S ^ 2 ≤
      ((P : ℝ) + H) * ((P : ℝ) + 18 * (U ^ 2 / a) * L) := by
    apply (mul_le_mul_iff_right₀ hHR).mp
    calc
      (H : ℝ) * ((H : ℝ) * S ^ 2) = (H : ℝ) ^ 2 * S ^ 2 := by ring
      _ ≤ ((P + H : ℕ) : ℝ) *
          ((H : ℝ) * P + 18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ))) := hraw
      _ ≤ ((P + H : ℕ) : ℝ) * ((H : ℝ) * P + 18 * H * (U ^ 2 / a) * L) := by gcongr
      _ = _ := by push_cast; ring
  change S ^ 2 ≤ 148480 * a * L
  rcases hlag with hlag | hlag
  · have hPH : (P : ℝ) = H := by exact_mod_cast hlag.symm
    have hcancel' : S ^ 2 ≤ 2 * (P : ℝ) + 36 * (U ^ 2 / a) * L := by
      apply (mul_le_mul_iff_right₀ hHR).mp
      calc
        (H : ℝ) * S ^ 2 ≤ ((P : ℝ) + H) * ((P : ℝ) + 18 * (U ^ 2 / a) * L) := hcancel
        _ = _ := by rw [hPH]; ring
    have hq := mul_le_mul_of_nonneg_right hratio64 (by linarith : 0 ≤ L)
    have hPa : (P : ℝ) ≤ 8 * a := hPU.trans hUa
    have haL : a ≤ a * L := by nlinarith
    nlinarith
  · have hinside : (P : ℝ) + 18 * (U ^ 2 / a) * L ≤ 145 * U * L := by
      have hq := mul_le_mul_of_nonneg_right hratio (by linarith : 0 ≤ L)
      have hUL : U ≤ U * L := by nlinarith
      nlinarith
    have houter : (P : ℝ) + H ≤ 2 * U := by linarith
    have hmain : (H : ℝ) * S ^ 2 ≤ 148480 * a * H * L := by
      calc
        _ ≤ ((P : ℝ) + H) * ((P : ℝ) + 18 * (U ^ 2 / a) * L) := hcancel
        _ ≤ (2 * U) * (145 * U * L) := mul_le_mul houter hinside (by positivity) (by positivity)
        _ = 290 * U ^ 2 * L := by ring
        _ ≤ 290 * (512 * a * H) * L := by gcongr
        _ = _ := by ring
    apply (mul_le_mul_iff_right₀ hHR).mp
    calc
      (H : ℝ) * S ^ 2 ≤ 148480 * a * H * L := hmain
      _ = _ := by ring

/-- Every real-start dyadic prefix in the critical range has the
square-root bound, including prefixes shorter than the natural lag size. -/
theorem mrRealLogBlock_le_sqrt
    {a U : ℝ} {P : ℕ} (ha : 1 ≤ a) (hU : 0 < U)
    (hUa : U ≤ 8 * a) (hPU : (P : ℝ) ≤ U) :
    ‖∑ n ∈ range P, realBlockPhase a U n‖ ≤
      400 * Real.sqrt a * (1 + Real.log (8 * a)) := by
  let L : ℝ := 1 + Real.log (8 * a)
  have ha0 : 0 < a := by linarith
  have hsqrt : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hsqrtsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha0.le
  have hL1 : 1 ≤ L := by
    have hh := Real.log_nonneg (show (1 : ℝ) ≤ 8 * a by linarith)
    dsimp only [L]
    linarith
  change _ ≤ 400 * Real.sqrt a * L
  by_cases hsmall : U ≤ 32 * Real.sqrt a
  · have htriv : ‖∑ n ∈ range P, realBlockPhase a U n‖ ≤ (P : ℝ) := by
      calc
        _ ≤ ∑ n ∈ range P, ‖realBlockPhase a U n‖ := norm_sum_le _ _
        _ = _ := by simp only [norm_realBlockPhase, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one]
    have hsqrtL : Real.sqrt a ≤ Real.sqrt a * L := by nlinarith
    nlinarith
  by_cases hP : P = 0
  · subst P
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hP0 : 0 < P := Nat.pos_of_ne_zero hP
  have hlarge : 1024 * a ≤ U ^ 2 := by
    have hh : 32 * Real.sqrt a < U := lt_of_not_ge hsmall
    nlinarith
  let z : ℝ := U ^ 2 / (256 * a)
  let H₀ : ℕ := ⌊z⌋₊
  let H : ℕ := min P H₀
  have hz4 : 4 ≤ z := by
    dsimp only [z]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * a)).mpr
    nlinarith
  have hH0 : 0 < H₀ := Nat.floor_pos.mpr (by linarith : 1 ≤ z)
  have hH : 0 < H := lt_min hP0 hH0
  have hHle : (H : ℝ) ≤ H₀ := by exact_mod_cast min_le_right P H₀
  have hH0z : (H₀ : ℝ) ≤ z := Nat.floor_le (by linarith : 0 ≤ z)
  have hscale : 8 * (H : ℝ) * a ≤ U ^ 2 := by
    have hHz := hHle.trans hH0z
    have hh : (H : ℝ) * (256 * a) ≤ U ^ 2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * a)).mp hHz
    nlinarith [show (0 : ℝ) ≤ H by positivity]
  have hlag : H = P ∨ U ^ 2 ≤ 512 * a * H := by
    rcases le_total P H₀ with hh | hh
    · exact Or.inl (min_eq_left hh)
    · right
      have hmin : H = H₀ := min_eq_right hh
      have hfloor : z < (H₀ : ℝ) + 1 := Nat.lt_floor_add_one z
      have hH01 : (1 : ℝ) ≤ H₀ := by exact_mod_cast hH0
      have hz : z ≤ 2 * H₀ := by linarith
      have hU2 : U ^ 2 ≤ (2 * (H₀ : ℝ)) * (256 * a) :=
        (div_le_iff₀ (by positivity : (0 : ℝ) < 256 * a)).mp hz
      rw [hmin]
      nlinarith
  have hsq := mrRealLogBlock_sq_le_of_lag ha hU hUa hPU hH (min_le_left P H₀) hscale hlag
  have hbound : (400 * Real.sqrt a * L) ^ 2 = 160000 * a * L ^ 2 := by
    rw [mul_pow, mul_pow, hsqrtsq]
    ring
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have haL := mul_le_mul_of_nonneg_left hLsq ha0.le
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 400 * Real.sqrt a * L)).mp
  rw [hbound]
  change _ ≤ 160000 * a * L ^ 2
  change _ ≤ 148480 * a * L at hsq
  nlinarith [show 0 ≤ a * L by positivity]

end Erdos67b
