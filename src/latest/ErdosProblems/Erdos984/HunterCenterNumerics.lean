/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterOrbitHitting

/-!
# Numerical estimates for the random center family
-/

namespace Erdos984

noncomputable section

def hunterGroupSize (D : ℕ) : ℕ := D ^ (15 * D)

lemma hunterY_mul_groupSize (D : ℕ) :
    hunterY D * hunterGroupSize D = hunterM D := by
  simp only [hunterY, hunterGroupSize, hunterM, ← pow_add]
  congr 1
  ring

lemma hunter_center_real_cost_lt_quarter (D : ℕ) (hD : 400 ≤ D) :
    (hunterM D : ℝ) ^ 3 * (8 * hunterRho D) ^ D < (1 : ℝ) / 4 := by
  have hDpos : (0 : ℝ) < D := by positivity
  have hbase : (32 : ℝ) < (D : ℝ) ^ 40 := by
    calc
      (32 : ℝ) < 400 ^ 40 := by norm_num
      _ ≤ (D : ℝ) ^ 40 := by
        gcongr
        exact_mod_cast hD
  simp only [hunterM, hunterRho, Nat.cast_pow]
  rw [← pow_mul, ← div_eq_mul_inv, div_pow, ← pow_mul]
  rw [show 20 * D * 3 = 60 * D by ring, ← mul_div_assoc]
  rw [div_lt_iff₀ (by positivity)]
  have hp : (32 : ℝ) ^ D < (D : ℝ) ^ (40 * D) := by
    simpa only [← pow_mul] using
      pow_lt_pow_left₀ hbase (by norm_num) (by omega : D ≠ 0)
  have hfourcost : 4 * ((D : ℝ) ^ (60 * D) * 8 ^ D) <
      (D : ℝ) ^ (100 * D) := by
    calc
    4 * ((D : ℝ) ^ (60 * D) * 8 ^ D) =
        (D : ℝ) ^ (60 * D) * (4 * 8 ^ D) := by ring
    _ ≤ (D : ℝ) ^ (60 * D) * (4 ^ D * 8 ^ D) := by
      gcongr
      calc
        (4 : ℝ) = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
    _ = (D : ℝ) ^ (60 * D) * 32 ^ D := by
      rw [← mul_pow]
      norm_num
    _ < (D : ℝ) ^ (60 * D) * (D : ℝ) ^ (40 * D) :=
      mul_lt_mul_of_pos_left hp (by positivity)
    _ = (D : ℝ) ^ (100 * D) := by rw [← pow_add]; congr 1; ring
  nlinarith

lemma hunter_center_cost_lt_quarter (D : ℕ) (hD : 400 ≤ D) :
    (hunterM D ^ 3 : ENNReal) *
      (ENNReal.ofReal (8 * hunterRho D)) ^ D <
        ENNReal.ofReal ((1 : ℝ) / 4) := by
  rw [← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_pow (Nat.cast_nonneg (hunterM D)),
    ← ENNReal.ofReal_pow
      (mul_nonneg (by norm_num) (hunterRho_pos (by omega)).le),
    ← ENNReal.ofReal_mul (by positivity)]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2
    (hunter_center_real_cost_lt_quarter D hD)

lemma hunter_hit_exponent (D : ℕ) (hD : 400 ≤ D) :
    Real.exp (-((D : ℝ) ^ (9 * D))) ≤
      (((D : ℝ) ^ (8 * D))⁻¹) ^ (D ^ 2) := by
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
  have hx : 0 < (D : ℝ) ^ (9 * D) := by positivity
  have hn : 0 < D ^ 2 := pow_pos (by omega) _
  have hexp := exp_neg_le_div_pow hx (D ^ 2) hn
  refine hexp.trans ?_
  apply pow_le_pow_left₀ (by positivity) ?_ _
  rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, div_le_one hx]
  have hexponents : 2 + 8 * D ≤ 9 * D := by omega
  calc
    ((D ^ 2 : ℕ) : ℝ) * (D : ℝ) ^ (8 * D) =
        (D : ℝ) ^ (2 + 8 * D) := by
      push_cast
      rw [pow_add]
    _ ≤ (D : ℝ) ^ (9 * D) :=
      pow_le_pow_right₀ hDreal hexponents

lemma hunter_hit_union_real_cost_lt_quarter (D : ℕ) (hD : 400 ≤ D) :
    ((hunterN D ^ 2 * hunterY D : ℕ) : ℝ) *
      Real.exp (-((D : ℝ) ^ (9 * D))) < (1 : ℝ) / 4 := by
  have hDreal : (1 : ℝ) < D := by exact_mod_cast (show 1 < D by omega)
  have hDpos : (0 : ℝ) < D := by linarith
  have hcount : ((hunterN D ^ 2 * hunterY D : ℕ) : ℝ) =
      (D : ℝ) ^ (2 * D ^ 2 + 5 * D) := by
    simp only [hunterN, hunterY, Nat.cast_mul, Nat.cast_pow]
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have hpow := hunter_hit_exponent D hD
  calc
    ((hunterN D ^ 2 * hunterY D : ℕ) : ℝ) *
        Real.exp (-((D : ℝ) ^ (9 * D))) ≤
      (D : ℝ) ^ (2 * D ^ 2 + 5 * D) *
        (((D : ℝ) ^ (8 * D))⁻¹) ^ (D ^ 2) := by
      rw [hcount]
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (D : ℝ) ^ (2 * D ^ 2 + 5 * D) /
        (D : ℝ) ^ (8 * D * D ^ 2) := by
      rw [inv_pow, ← pow_mul]
      rfl
    _ < (1 : ℝ) / 4 := by
      rw [div_lt_iff₀ (by positivity)]
      have hexponents : 2 * D ^ 2 + 5 * D + 1 < 8 * D * D ^ 2 := by
        nlinarith
      have hpowlt : (D : ℝ) ^ (2 * D ^ 2 + 5 * D + 1) <
          (D : ℝ) ^ (8 * D * D ^ 2) :=
        pow_lt_pow_right₀ hDreal hexponents
      have hfour : (4 : ℝ) ≤ D := by exact_mod_cast (show 4 ≤ D by omega)
      have hfourcost : 4 * (D : ℝ) ^ (2 * D ^ 2 + 5 * D) <
          (D : ℝ) ^ (8 * D * D ^ 2) := by
        calc
        4 * (D : ℝ) ^ (2 * D ^ 2 + 5 * D) ≤
            (D : ℝ) * (D : ℝ) ^ (2 * D ^ 2 + 5 * D) :=
          mul_le_mul_of_nonneg_right hfour (by positivity)
        _ = (D : ℝ) ^ (2 * D ^ 2 + 5 * D + 1) := by
          rw [pow_succ]
          ring
        _ < (D : ℝ) ^ (8 * D * D ^ 2) := hpowlt
      nlinarith

end

end Erdos984
