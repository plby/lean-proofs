import ErdosProblems.Erdos1148.PacketFormExistence

/-! # Unconditional integral discriminant points in the fixed parity-safe ball -/

namespace Erdos1148

open DukeArithmetic
open scoped MatrixGroups

lemma not_isSquare_four_mul {n : ℤ} (hns : ¬IsSquare n) : ¬IsSquare (4 * n) := by
  rintro ⟨z, hz⟩
  have heven : z % 2 = 0 := even_middle_of_discriminant
    (n := n) (a := 0) (c := 0) (b := z) (by nlinarith only [hz])
  have hzhalf : z = 2 * (z / 2) := by omega
  apply hns
  refine ⟨z / 2, ?_⟩
  rw [hzhalf] at hz
  nlinarith only [hz]

lemma normalizeDisc_of_scaled_form {n : ℤ} (hn : 0 < n)
    {t : ℤ × ℤ × ℤ} {v : ℝ × ℝ × ℝ}
    (hscale : Real.sqrt (4 * (n : ℝ)) • v = mapCoeffs (Int.castRingHom ℝ) t) :
    normalizeDisc n t = v := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (4 * (n : ℝ)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have ha := congrArg Prod.fst hscale
  have hb := congrArg (fun x : ℝ × ℝ × ℝ => x.2.1) hscale
  have hc := congrArg (fun x : ℝ × ℝ × ℝ => x.2.2) hscale
  apply Prod.ext
  · change (t.1 : ℝ) / Real.sqrt (4 * (n : ℝ)) = v.1
    apply (div_eq_iff hs).mpr
    simpa [mapCoeffs, mul_comm] using ha.symm
  · apply Prod.ext
    · change (t.2.1 : ℝ) / Real.sqrt (4 * (n : ℝ)) = v.2.1
      apply (div_eq_iff hs).mpr
      simpa [mapCoeffs, mul_comm] using hb.symm
    · change (t.2.2 : ℝ) / Real.sqrt (4 * (n : ℝ)) = v.2.2
      apply (div_eq_iff hs).mpr
      simpa [mapCoeffs, mul_comm] using hc.symm

theorem unconditional_fixed_ball_existence_nat :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ¬IsSquare (n : ℤ) →
      ∃ t : ℤ × ℤ × ℤ, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n ∧
        normalizeDisc n t ∈ Metric.ball discCenter (1 / 100) := by
  obtain ⟨D, hD⟩ := eventually_integral_form_in_open
    (W := Metric.ball discCenter (1 / 100)) Metric.isOpen_ball
    ⟨discCenter, Metric.mem_ball_self (by norm_num), discCenter_discriminant⟩
  refine ⟨max D 1, ?_⟩
  intro n hn hns
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right _ _).trans hn)
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hnpos
  have hd : (0 : ℤ) < (4 * n : ℕ) := by positivity
  have hnsd : ¬IsSquare ((4 * n : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using not_isSquare_four_mul hns
  let base : IntegralDiscrForm ((4 * n : ℕ) : ℤ) :=
    ⟨(1, 0, -(n : ℤ)), by dsimp [discr]; push_cast; ring⟩
  obtain ⟨g, t, hlocal, hscale⟩ := hD (4 * n) (by omega) hd hnsd base
  refine ⟨t.1, ?_, ?_⟩
  · simpa only [discr, Nat.cast_mul, Nat.cast_ofNat] using t.2
  · have hscale' : Real.sqrt (4 * (n : ℝ)) • formAction g (splitForm ℝ) =
        mapCoeffs (Int.castRingHom ℝ) t.1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hscale
    rw [normalizeDisc_of_scaled_form hnZ hscale']
    exact hlocal

theorem unconditional_fixed_ball_existence :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → ¬IsSquare n →
      ∃ t : ℤ × ℤ × ℤ, t.2.1 ^ 2 - 4 * t.1 * t.2.2 = 4 * n ∧
        normalizeDisc n t ∈ Metric.ball discCenter (1 / 100) := by
  obtain ⟨N, hN⟩ := unconditional_fixed_ball_existence_nat
  refine ⟨N, ?_⟩
  intro n hn hns
  have hn0 : 0 ≤ n := (Int.natCast_nonneg N).trans hn
  have heq : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
  have hNle : N ≤ n.toNat := by exact_mod_cast (heq ▸ hn)
  obtain ⟨t, ht, hlocal⟩ := hN n.toNat hNle (by simpa only [heq] using hns)
  exact ⟨t, by simpa only [heq] using ht, by simpa only [heq] using hlocal⟩

end Erdos1148
