import ErdosProblems.Erdos633b.CornerAngleWeights
import ErdosProblems.Erdos633b.RationalCornerRows

/-! Positive common integer angle weights for a commensurable triangle,
transported through the actual corner counts of a geometric tiling. -/

namespace Erdos633b

theorem rational_positive_integer_weights (q : Fin 3 → ℚ) (hq : ∀ i, 0 < q i) :
    ∃ N : ℕ, 0 < N ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (q i : ℝ) = (w i : ℝ) / N := by
  let N : ℕ := ∏ i, (q i).den
  have hN : 0 < N := Finset.prod_pos (by intro i _; exact (q i).pos)
  have hd (i : Fin 3) : (q i).den ∣ N :=
    Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)
  choose k hk using hd
  let w : Fin 3 → ℕ := fun i => (q i).num.toNat * k i
  have hkpos (i : Fin 3) : 0 < k i := by
    have hh := hk i
    by_contra hn
    have hz : k i = 0 := by omega
    rw [hz, mul_zero] at hh
    omega
  have hnum (i : Fin 3) : 0 < (q i).num := Rat.num_pos.mpr (hq i)
  refine ⟨N, hN, w, ?_, ?_⟩
  · intro i
    exact Nat.mul_pos (by have hh := hnum i; omega) (hkpos i)
  · intro i
    have hden : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
    have hk' : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hw : (w i : ℝ) = ((q i).num : ℝ) * k i := by
      dsimp only [w]
      rw [Nat.cast_mul]
      congr 1
      exact_mod_cast Int.toNat_of_nonneg (hnum i).le
    rw [hw, hk i, Nat.cast_mul, Rat.cast_def]
    field_simp

namespace Triangle

theorem positive_integer_angle_weights (T : Triangle)
    (hrat : ∀ i, IsRational (T.angle i / Real.pi)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ w : Fin 3 → ℕ,
      (∀ i, T.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ ∑ i, w i = N := by
  choose q hq using hrat
  have hqpos (i : Fin 3) : 0 < q i := by
    have hreal : (0 : ℝ) < q i := by rw [hq i]; exact div_pos (T.angle_pos i) Real.pi_pos
    exact_mod_cast hreal
  obtain ⟨N, hN, w, hwpos, hw⟩ := rational_positive_integer_weights q hqpos
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hrow (i : Fin 3) : T.angle i = (w i : ℝ) * (Real.pi / N) := by
    have hh := hw i
    rw [hq i] at hh
    have he := (div_eq_div_iff Real.pi_ne_zero hNreal.ne').mp hh
    rw [← mul_div_assoc]
    exact (eq_div_iff hNreal.ne').mpr he
  have hsumreal : ((∑ i, w i : ℕ) : ℝ) = N := by
    apply mul_right_cancel₀ (div_ne_zero Real.pi_ne_zero hNreal.ne')
    calc
      _ = ∑ i, (w i : ℝ) * (Real.pi / N) := by rw [Nat.cast_sum, Finset.sum_mul]
      _ = Real.pi := by simp_rw [← hrow]; simpa only [Fin.sum_univ_three] using T.angle_sum
      _ = (N : ℝ) * (Real.pi / N) := by field_simp
  have hsum : ∑ i, w i = N := by exact_mod_cast hsumreal
  have hp0 := hwpos 0
  have hp1 := hwpos 1
  have hp2 := hwpos 2
  rw [Fin.sum_univ_three] at hsum
  refine ⟨N, by omega, w, hrow, ?_, by simpa only [Fin.sum_univ_three] using hsum⟩
  intro i
  refine ⟨hwpos i, ?_⟩
  fin_cases i
  · change w 0 < N; omega
  · change w 1 < N; omega
  · change w 2 < N; omega

end Triangle

namespace Tiling

theorem common_positive_integer_angle_weights {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) :
    ∃ N : ℕ, 3 ≤ N ∧ ∃ w a : Fin 3 → ℕ,
      (∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N)) ∧
      (∀ i, T.angle i = (a i : ℝ) * (Real.pi / N)) ∧
      (∀ i, 0 < w i ∧ w i < N) ∧ (∀ i, 0 < a i ∧ a i < N) ∧
      ∑ i, w i = N ∧ ∑ i, a i = N := by
  obtain ⟨N, hN, w, hw, hwp, hws⟩ := d.tile.positive_integer_angle_weights hrat
  obtain ⟨a, ha, hap, has⟩ := d.integer_corner_weights N (by omega) w hw
  refine ⟨N, hN, w, a, hw, ha, hwp, ?_, hws, has⟩
  have hp0 := hap 0
  have hp1 := hap 1
  have hp2 := hap 2
  rw [Fin.sum_univ_three] at has
  intro i
  refine ⟨hap i, ?_⟩
  fin_cases i
  · change a 0 < N; omega
  · change a 1 < N; omega
  · change a 2 < N; omega

end Tiling
end Erdos633b
