import ErdosProblems.Erdos587.SecondDerivativePartition

/-! The second-derivative test in discrete second-difference form. -/

open scoped BigOperators

namespace Erdos587

lemma monotone_increments_of_positive_second_difference (f : ℕ → ℝ) (N : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hstep : ∀ n, n + 1 < N → lam ≤ phaseIncrement f (n + 1) - phaseIncrement f n) :
    MonotoneOn (phaseIncrement f) (Set.Iio N) := by
  intro n hn m hm hnm
  have hh := increment_lower_separation (phaseIncrement f) N lam hstep hn hm hnm
  have hdiff : (0 : ℝ) ≤ (m : ℝ) - n := sub_nonneg.mpr (by exact_mod_cast hnm)
  linarith [mul_nonneg hlam hdiff]

lemma card_increment_integer_range (f : ℕ → ℝ) {N : ℕ} (hN : 0 < N) {D : ℝ}
    (hD : 0 ≤ D) (hd : MonotoneOn (phaseIncrement f) (Set.Iio N))
    (hstep : ∀ n, n + 1 < N → phaseIncrement f (n + 1) - phaseIncrement f n ≤ D) :
    ((Finset.Icc (Int.floor (phaseIncrement f 0))
      (Int.floor (phaseIncrement f (N - 1)))).card : ℝ) ≤ D * N + 2 := by
  have hends := hd hN (show N - 1 < N by omega) (Nat.zero_le _)
  have hfloor := Int.floor_mono hends
  have hcard := Int.card_Icc_of_le _ _ (show Int.floor (phaseIncrement f 0) ≤
      Int.floor (phaseIncrement f (N - 1)) + 1 by omega)
  have hcardR : ((Finset.Icc (Int.floor (phaseIncrement f 0))
      (Int.floor (phaseIncrement f (N - 1)))).card : ℝ) =
      (Int.floor (phaseIncrement f (N - 1)) : ℝ) + 1 - Int.floor (phaseIncrement f 0) := by
    exact_mod_cast hcard
  rw [hcardR]
  have hspan := increment_upper_separation (phaseIncrement f) N D hstep hN
    (show N - 1 < N by omega) (Nat.zero_le _)
  have hNM : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hupper := Int.floor_le (phaseIncrement f (N - 1))
  have hlower := Int.lt_floor_add_one (phaseIncrement f 0)
  norm_num only [Nat.cast_zero, sub_zero] at hspan
  nlinarith [mul_le_mul_of_nonneg_left hNM hD]

theorem norm_phase_sum_le_of_second_difference_parameters (f : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) {lam D δ : ℝ} (hlam : 0 < lam) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hlo : ∀ n, n + 1 < N → lam ≤ phaseIncrement f (n + 1) - phaseIncrement f n)
    (hhi : ∀ n, n + 1 < N → phaseIncrement f (n + 1) - phaseIncrement f n ≤ D) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤ (D * N + 2) * (1 / δ + 2 * δ / lam + 2) := by
  classical
  have hd := monotone_increments_of_positive_second_difference f N hlam.le hlo
  let I := Finset.Icc (Int.floor (phaseIncrement f 0)) (Int.floor (phaseIncrement f (N - 1)))
  have hmap : ∀ n ∈ Finset.range N, Int.floor (phaseIncrement f n) ∈ I := by
    intro n hn
    have hnN := Finset.mem_range.mp hn
    exact Finset.mem_Icc.mpr ⟨Int.floor_mono (hd hN hnN (Nat.zero_le n)),
      Int.floor_mono (hd hnN (show N - 1 < N by omega) (by omega))⟩
  have hsplit := Finset.sum_fiberwise_of_maps_to hmap (fun n => phase (f n))
  have hcard : (I.card : ℝ) ≤ D * N + 2 := card_increment_integer_range f hN hD hd hhi
  calc
    _ = ‖∑ k ∈ I, ∑ n ∈ incrementUnitFiber f N k, phase (f n)‖ := by
      change ‖∑ n ∈ Finset.range N, phase (f n)‖ =
        ‖∑ k ∈ I, ∑ n ∈ (Finset.range N).filter (fun n => Int.floor (phaseIncrement f n) = k),
          phase (f n)‖
      exact congrArg norm hsplit.symm
    _ ≤ ∑ k ∈ I, ‖∑ n ∈ incrementUnitFiber f N k, phase (f n)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ I, (1 / δ + 2 * δ / lam + 2) :=
      Finset.sum_le_sum (fun k hk => norm_phase_sum_on_increment_fiber f N k hδ hlam hd hlo)
    _ = (I.card : ℝ) * (1 / δ + 2 * δ / lam + 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

theorem norm_phase_sum_le_second_difference (f : ℕ → ℝ) (N : ℕ) {lam C : ℝ}
    (hlam : 0 < lam) (hC : 1 ≤ C)
    (hlo : ∀ n, n + 1 < N → lam ≤ phaseIncrement f (n + 1) - phaseIncrement f n)
    (hhi : ∀ n, n + 1 < N → phaseIncrement f (n + 1) - phaseIncrement f n ≤ C * lam) :
    ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤
      10 * C * ((N : ℝ) * Real.sqrt lam + (Real.sqrt lam)⁻¹) := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hCpos : 0 < C := by linarith
  have htrivial : ‖∑ n ∈ Finset.range N, phase (f n)‖ ≤ N := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖phase (f n)‖ := norm_sum_le _ _
      _ = N := by simp
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero, zero_mul, zero_add]
    positivity
  have hNpos : 0 < N := by omega
  by_cases hlam1 : lam ≤ 1
  · have hs1 : Real.sqrt lam ≤ 1 := Real.sqrt_le_one.mpr hlam1
    have hcoef : 1 / Real.sqrt lam + 2 * Real.sqrt lam / lam + 2 ≤ 5 / Real.sqrt lam := by
      have heq : 2 * Real.sqrt lam / lam = 2 / Real.sqrt lam := by
        field_simp
        nlinarith [Real.sq_sqrt hlam.le]
      rw [heq]
      apply (le_div_iff₀ hs).mpr
      field_simp
      nlinarith
    have hh := norm_phase_sum_le_of_second_difference_parameters f hNpos hlam
      (by positivity : 0 ≤ C * lam) hs hlo hhi
    calc
      _ ≤ (C * lam * N + 2) * (1 / Real.sqrt lam + 2 * Real.sqrt lam / lam + 2) := hh
      _ ≤ (C * lam * N + 2) * (5 / Real.sqrt lam) :=
        mul_le_mul_of_nonneg_left hcoef (by positivity)
      _ = 5 * C * N * Real.sqrt lam + 10 * (Real.sqrt lam)⁻¹ := by
        field_simp
        nlinarith [congrArg (fun t : ℝ => C * N * t) (Real.sq_sqrt hlam.le)]
      _ ≤ _ := by
        have hterm : 0 ≤ C * N * Real.sqrt lam := by positivity
        have hinv := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hs.le)
        nlinarith
  · have hs1 : 1 ≤ Real.sqrt lam := Real.one_le_sqrt.mpr (le_of_not_ge hlam1)
    apply htrivial.trans
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hNs := le_mul_of_one_le_right hN0 hs1
    have hbig : (N : ℝ) * Real.sqrt lam ≤ 10 * C * ((N : ℝ) * Real.sqrt lam) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    have hinv : 0 ≤ 10 * C * (Real.sqrt lam)⁻¹ := by positivity
    nlinarith

end Erdos587
