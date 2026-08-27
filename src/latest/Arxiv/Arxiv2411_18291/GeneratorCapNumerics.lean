import Arxiv.Arxiv2411_18291.AsymptoticCliqueCount
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Polynomial face caps for modular generators

The integer cap is the floor of `n^(1-s)`. The gap `s+2*t<α`
makes the saturation criterion hold at error `n^(-t)` for any fixed
upper density constant. Rounding the cap costs at most a factor of two.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem half_le_nat_floor {x : ℝ} (hx : 2 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one x
  linarith

theorem generator_cap_scale {x : ℝ} (hx : 0 < x) (α s t : ℝ) :
    x ^ (1 - α) * x ^ (α - s - 2 * t) = x ^ (1 - s) * (x ^ (-t)) ^ 2 := by
  rw [pow_two, ← Real.rpow_add hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
  congr 1
  ring

theorem generator_cap_numerics_of_growth (q r N : ℕ) {n : ℕ} {b α s t : ℝ}
    (hn : 0 < n) (hlarge : 2 ≤ (n : ℝ) ^ (1 - s))
    (hmargin : 8 * (q.choose (r + 1) : ℝ) * q.choose r * N * b ≤
      (n : ℝ) ^ (α - s - 2 * t)) :
    0 < ⌊(n : ℝ) ^ (1 - s)⌋₊ ∧
      ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - s)⌋₊ <
        (2 ^ q * (n : ℝ) ^ (-s)) * n ∧
      ∀ d : ℝ, d ≤ b * (n : ℝ) ^ (-α) →
        4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n * d ≤
          (⌊(n : ℝ) ^ (1 - s)⌋₊ : ℝ) * ((n : ℝ) ^ (-t)) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 0 < (n : ℝ) ^ (1 - s) := Real.rpow_pos_of_pos hnpos _
  have hfloor : (⌊(n : ℝ) ^ (1 - s)⌋₊ : ℝ) ≤ (n : ℝ) ^ (1 - s) :=
    Nat.floor_le hpow.le
  have hhalf := half_le_nat_floor hlarge
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_⟩
  · have hq : ((q - r : ℕ) : ℝ) < 2 ^ q := by
      exact_mod_cast (Nat.sub_le q r).trans_lt Nat.lt_two_pow_self
    calc
      _ ≤ ((q - r : ℕ) : ℝ) * (n : ℝ) ^ (1 - s) :=
        mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
      _ < 2 ^ q * (n : ℝ) ^ (1 - s) := mul_lt_mul_of_pos_right hq hpow
      _ = _ := by
        rw [show 1 - s = -s + 1 by ring, Real.rpow_add hnpos, Real.rpow_one]
        ring
  · intro d hd
    have hA : 0 ≤ 4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n := by positivity
    calc
      _ ≤ 4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n *
          (b * (n : ℝ) ^ (-α)) := mul_le_mul_of_nonneg_left hd hA
      _ = (4 * (q.choose (r + 1) : ℝ) * q.choose r * N * b) *
          (n : ℝ) ^ (1 - α) := by
        rw [show 1 - α = 1 + -α by ring, Real.rpow_add hnpos, Real.rpow_one]
        ring
      _ ≤ ((n : ℝ) ^ (α - s - 2 * t) / 2) * (n : ℝ) ^ (1 - α) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hnpos.le _)
      _ = ((n : ℝ) ^ (1 - s) / 2) * ((n : ℝ) ^ (-t)) ^ 2 := by
        have he := generator_cap_scale hnpos α s t
        nlinarith only [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right hhalf (sq_nonneg _)

theorem eventually_generator_cap_numerics (q r N : ℕ) {b α s t : ℝ}
    (hs : s < 1) (hgap : s + 2 * t < α) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < ⌊(n : ℝ) ^ (1 - s)⌋₊ ∧
      ((q - r : ℕ) : ℝ) * ⌊(n : ℝ) ^ (1 - s)⌋₊ <
        (2 ^ q * (n : ℝ) ^ (-s)) * n ∧
      ∀ d : ℝ, d ≤ b * (n : ℝ) ^ (-α) →
        4 * (q.choose (r + 1) : ℝ) * q.choose r * N * n * d ≤
          (⌊(n : ℝ) ^ (1 - s)⌋₊ : ℝ) * ((n : ℝ) ^ (-t)) ^ 2 := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < 1 - s)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually (eventually_ge_atTop (2 : ℝ))
  have hmargin := ((tendsto_rpow_atTop (by linarith : 0 < α - s - 2 * t)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (8 * (q.choose (r + 1) : ℝ) * q.choose r * N * b))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge, hmargin] with n hn hln hmn
  exact ⟨by omega, generator_cap_numerics_of_growth q r N (by omega) hln hmn⟩

theorem eventually_generator_count_error (q : ℕ) {δ t : ℝ} (htδ : t < δ) :
    ∀ᶠ n : ℕ in atTop,
      (2 * (n : ℝ) ^ (-δ)) * q * 2 ^ q ≤ (n : ℝ) ^ (-t) / 2 := by
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < δ - t)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (4 * q * 2 ^ q : ℝ))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlarge] with n hn hln
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 := Real.rpow_nonneg hnpos.le (-δ)
  have hln' : (4 * q * 2 ^ q : ℝ) ≤ (n : ℝ) ^ (δ - t) := hln
  have hp : (n : ℝ) ^ (δ - t) * (n : ℝ) ^ (-δ) = (n : ℝ) ^ (-t) := by
    rw [← Real.rpow_add hnpos]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right hln' hc0
  rw [hp] at hm
  nlinarith only [hm]

end Arxiv2411_18291
