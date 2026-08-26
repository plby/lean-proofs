import ErdosProblems.Erdos941.LogScaleDecay

/-! # The mass and collision inequalities cannot coexist for large norms -/

namespace Erdos941.Analytic

theorem exists_no_mass_collision {Q : ℕ} (hQ : 1 < Q) {P δ c C D : ℝ}
    (hP : 0 ≤ P) (hδ : 0 < δ) (hgap : P * (Q : ℝ) ^ (6 * δ) < Q)
    (hc : 0 < c) (hC : 0 ≤ C) (hD : 0 < D) :
    ∃ N : ℕ, 0 < N ∧ ∀ (n : ℕ) (H : ℝ), N ≤ n →
      c * (n : ℝ) ^ (1 / 2 - δ) ≤ H →
      (∀ j : ℕ, H ^ 2 ≤ D * P ^ j *
        (2 * H + C * ((n : ℝ) / (Q : ℝ) ^ j) * (n : ℝ) ^ δ)) → False := by
  have hden : 0 < D * (2 * c + C) := mul_pos hD (by linarith)
  obtain ⟨N, hN, hdecay⟩ := exists_log_scale_decay hQ hP hδ hgap
    (div_pos (sq_pos_of_pos hc) hden)
  refine ⟨N, hN, ?_⟩
  intro n H hn hmass hcollision
  have hn0 : 0 < n := hN.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (zero_lt_one.trans hQ)
  let j := Nat.log (Q ^ 2) n
  let q : ℝ := (Q : ℝ) ^ j
  let x : ℝ := (n : ℝ) ^ δ
  let y : ℝ := (n : ℝ) ^ (1 / 2 : ℝ)
  have hq : 0 < q := pow_pos hQr _
  have hy : 0 < y := Real.rpow_pos_of_pos hnR _
  have hx : 1 ≤ x := Real.one_le_rpow (by exact_mod_cast hn0) hδ.le
  have hy2 : y ^ 2 = n := by
    dsimp [y]
    rw [← Real.rpow_mul_natCast hnR.le]
    norm_num
  have hq2 : q ^ 2 ≤ (n : ℝ) := by
    have h := Nat.pow_log_le_self (Q ^ 2) hn0.ne'
    have he : (Q ^ 2) ^ j = (Q ^ j) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 j]
    change (Q ^ 2) ^ j ≤ n at h
    rw [he] at h
    dsimp [q]
    exact_mod_cast h
  have hqy : q ≤ y := by nlinarith only [hq2, hy2, hq, hy]
  have hH : 0 < H := (mul_pos hc (Real.rpow_pos_of_pos hnR _)).trans_le hmass
  have hmass' : c * y ≤ H * x := by
    have he : (n : ℝ) ^ (1 / 2 - δ) * (n : ℝ) ^ δ = y := by
      rw [← Real.rpow_add hnR]
      congr 1
      ring
    calc
      c * y = (c * (n : ℝ) ^ (1 / 2 - δ)) * x := by dsimp [x]; rw [mul_assoc, he]
      _ ≤ H * x := mul_le_mul_of_nonneg_right hmass (by positivity)
  have hcollision' : H ^ 2 * q ≤ D * P ^ j * (2 * H * q + C * y ^ 2 * x) := by
    calc
      _ ≤ (D * P ^ j * (2 * H + C * ((n : ℝ) / q) * x)) * q :=
        mul_le_mul_of_nonneg_right (hcollision j) hq.le
      _ = _ := by rw [hy2]; field_simp
  have hnorm := normalized_collision_inequality hc hC hD.le (pow_nonneg hP j)
    hH hx hq hqy hmass' hcollision'
  have hsmall : D * (2 * c + C) * ((P ^ j / q) * x ^ 3) < c ^ 2 := by
    have h := mul_lt_mul_of_pos_left (hdecay n hn) hden
    rw [mul_div_cancel₀ _ hden.ne'] at h
    exact h
  have hsmallq := mul_lt_mul_of_pos_right hsmall hq
  have he : (D * (2 * c + C) * ((P ^ j / q) * x ^ 3)) * q =
      D * P ^ j * (2 * c + C) * x ^ 3 := by field_simp
  rw [he] at hsmallq
  exact (not_lt_of_ge hnorm) hsmallq

end Erdos941.Analytic
