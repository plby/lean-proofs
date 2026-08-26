import ErdosProblems.Erdos1148.NaturalPairScale

/-! # Exponents in the cusp covering estimate at the natural pair scale -/

namespace Erdos1148.DukeArithmetic

lemma naturalPairScale_rpow_div_pow {d : ℝ} (hd : 0 < d) (ε : ℝ) (n : ℕ) :
    (d ^ (-(1 / 4 : ℝ))) ^ (3 - ε) / (d ^ (-(1 / 4 : ℝ))) ^ n =
      d ^ ((n - 3 + ε) / 4) := by
  rw [← Real.rpow_sub_natCast (Real.rpow_pos_of_pos hd _).ne', ← Real.rpow_mul hd.le]
  congr 1
  ring

lemma naturalCuspScale_coefficient_bound {d H A K : ℝ} (hd : 0 < d) (hH : 0 < H)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (ε : ℝ) {J : ℕ}
    (hJ : (J : ℝ) ≤ 4 * d ^ (1 / 8 : ℝ)) :
    (A * ((4 / 3) / ((d ^ (-(1 / 4 : ℝ)) / 5) ^ 3 * H ^ 2) +
      J / (d ^ (-(1 / 4 : ℝ)) / 5) ^ 2)) *
        (K * (d ^ (-(1 / 4 : ℝ))) ^ (3 - ε)) ≤
      (200 * A * K) * (d ^ (ε / 4) / H ^ 2 + d ^ (-1 / 8 + ε / 4)) := by
  let η : ℝ := d ^ (-(1 / 4 : ℝ))
  have hη : 0 < η := Real.rpow_pos_of_pos hd _
  have hp3 : η ^ (3 - ε) / η ^ 3 = d ^ (ε / 4) := by
    simpa only [Nat.cast_ofNat, sub_self, zero_add] using naturalPairScale_rpow_div_pow hd ε 3
  have hp2 : η ^ (3 - ε) / η ^ 2 = d ^ (-1 / 4 + ε / 4) := by
    convert naturalPairScale_rpow_div_pow hd ε 2 using 2 <;> norm_num <;> ring
  have hmul : d ^ (1 / 8 : ℝ) * d ^ (-1 / 4 + ε / 4) =
      d ^ (-1 / 8 + ε / 4) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  have hrewrite :
      (A * ((4 / 3) / ((η / 5) ^ 3 * H ^ 2) + J / (η / 5) ^ 2)) *
          (K * η ^ (3 - ε)) =
        A * K * ((500 / 3) * (η ^ (3 - ε) / η ^ 3) / H ^ 2 +
          25 * J * (η ^ (3 - ε) / η ^ 2)) := by
    field_simp
    <;> ring
  change (A * ((4 / 3) / ((η / 5) ^ 3 * H ^ 2) + J / (η / 5) ^ 2)) *
      (K * η ^ (3 - ε)) ≤ _
  rw [hrewrite, hp3, hp2]
  have hterm : 25 * J * d ^ (-1 / 4 + ε / 4) ≤ 100 * d ^ (-1 / 8 + ε / 4) := by
    rw [← hmul]
    nlinarith [mul_le_mul_of_nonneg_right hJ (Real.rpow_nonneg hd.le (-1 / 4 + ε / 4))]
  have hfirst : 0 ≤ d ^ (ε / 4) / H ^ 2 := by positivity
  have hsecond : 0 ≤ d ^ (-1 / 8 + ε / 4) := Real.rpow_nonneg hd.le _
  have hsum : (500 / 3) * d ^ (ε / 4) / H ^ 2 +
      25 * J * d ^ (-1 / 4 + ε / 4) ≤
        200 * (d ^ (ε / 4) / H ^ 2 + d ^ (-1 / 8 + ε / 4)) := by
    rw [mul_div_assoc]
    linarith
  calc
    _ ≤ A * K * (200 * (d ^ (ε / 4) / H ^ 2 + d ^ (-1 / 8 + ε / 4))) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hA hK)
    _ = _ := by ring

end Erdos1148.DukeArithmetic
