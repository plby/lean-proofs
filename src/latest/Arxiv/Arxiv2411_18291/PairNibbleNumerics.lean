import Arxiv.Arxiv2411_18291.AsymptoticNibbleParameters
import Arxiv.Arxiv2411_18291.NibbleTailDecay

/-! # Eventual sampling and leave bounds for the general pair nibble -/

open Filter
open scoped Topology

namespace Arxiv2411_18291

theorem eventually_pair_nibble_numerics {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      let c := (n : ℝ) ^ (-(ε / 2))
      0 < c ∧ c ≤ 1 / 4 ∧ (n : ℝ) ^ (-ε) ≤ c ∧
        9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n ∧
        ∀ D : ℝ, (n : ℝ) ^ (2 / 3 : ℝ) ≤ D →
          (n + 1 : ℝ) * (2 * Real.exp (-((D / 2) * c ^ 2 / (4 * (1 + 2 * c))))) < 1 := by
  let ν := ((2 / 3 : ℝ) - ε) / 2
  have hν : 0 < ν := by dsimp only [ν]; linarith only [hεhalf]
  have hνgap : ν < (2 / 3 : ℝ) - ε := by dsimp only [ν]; linarith only [hεhalf]
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    eventually_scaled_rpow_le 1 (by norm_num : (0 : ℝ) < 1 / 4)
      (show -(ε / 2) < (0 : ℝ) by linarith only [hε]),
    eventually_scaled_rpow_le 9 (by norm_num : (0 : ℝ) < 1)
      (show -(ε / 2) < -(ε / 6) by linarith only [hε]),
    eventually_scaled_rpow_le 2 (by norm_num : (0 : ℝ) < 1)
      (show (0 : ℝ) < 1 - ε / 6 by linarith only [hεhalf]),
    eventually_scaled_rpow_le 24 (by norm_num : (0 : ℝ) < 1) hνgap,
    eventually_nibble_tail_lt_one 0 hν] with n hn hsmall hdecay hconst hexponent htail
  simp only [Real.rpow_zero, mul_one, one_mul] at hsmall hdecay hconst hexponent
  let c := (n : ℝ) ^ (-(ε / 2))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : 0 < c := Real.rpow_pos_of_pos hn0 _
  have hc1 : c ≤ 1 := by change (n : ℝ) ^ (-(ε / 2)) ≤ 1; linarith only [hsmall]
  have herror : (n : ℝ) ^ (-ε) ≤ c :=
    Real.rpow_le_rpow_of_exponent_le hnR (by linarith only [hε])
  have hprod : (n : ℝ) ^ (-(ε / 6)) * n = (n : ℝ) ^ (1 - ε / 6) := by
    rw [show 1 - ε / 6 = -(ε / 6) + 1 by ring, Real.rpow_add hn0, Real.rpow_one]
  have hleave : 9 * c * n + 2 < 3 * (n : ℝ) ^ (-(ε / 6)) * n := by
    have h9 := mul_le_mul_of_nonneg_right hdecay hn0.le
    have h2 : (2 : ℝ) ≤ (n : ℝ) ^ (-(ε / 6)) * n := hconst.trans_eq hprod.symm
    have hp : (0 : ℝ) < (n : ℝ) ^ (-(ε / 6)) * n := by positivity
    dsimp only [c]
    nlinarith only [h9, h2, hp]
  refine ⟨hc, hsmall, herror, hleave, ?_⟩
  intro D hD
  have hid : (n : ℝ) ^ (2 / 3 : ℝ) * c ^ 2 = (n : ℝ) ^ ((2 / 3 : ℝ) - ε) := by
    dsimp only [c]
    rw [← Real.rpow_mul_natCast hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  have hDprod := mul_le_mul_of_nonneg_right hD (sq_nonneg c)
  rw [hid] at hDprod
  have hcν := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hn0.le ν)
  simp only [one_mul] at hcν
  have hmargin : (n : ℝ) ^ ν ≤ (D / 2) * c ^ 2 / (4 * (1 + 2 * c)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + 2 * c))).mpr
    nlinarith only [hDprod, hexponent, hcν]
  have hcount : 2 * (n + 1 : ℝ) ≤ 5 * (n : ℝ) ^ 2 := by
    nlinarith only [hnR, sq_nonneg ((n : ℝ) - 1)]
  have htail' : 5 * (n : ℝ) ^ 2 * Real.exp (-((n : ℝ) ^ ν)) < 1 := by
    simpa only [Nat.zero_add, Nat.mul_one] using htail
  calc
    _ ≤ (n + 1 : ℝ) * (2 * Real.exp (-((n : ℝ) ^ ν))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hmargin)) (by norm_num)) (by positivity)
    _ = (2 * (n + 1 : ℝ)) * Real.exp (-((n : ℝ) ^ ν)) := by ring
    _ ≤ (5 * (n : ℝ) ^ 2) * Real.exp (-((n : ℝ) ^ ν)) :=
      mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ < 1 := htail'

end Arxiv2411_18291
