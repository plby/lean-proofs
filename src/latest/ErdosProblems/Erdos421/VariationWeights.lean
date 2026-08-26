import ErdosProblems.Erdos421.LargeValues
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Calculus.MeanValue

/-! # Partial-sum control under weights of bounded variation -/

namespace Erdos421

theorem oscillatoryPhase_lipschitz (ω x y : ℝ) :
    ‖oscillatoryPhase ω y - oscillatoryPhase ω x‖ ≤ |ω| * |y - x| := by
  have hd : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (oscillatoryPhase ω)
        ((Complex.I * (ω : ℂ)) * oscillatoryPhase ω t) Set.univ t :=
    fun t _ ↦ (oscillatoryPhase_hasDerivAt ω t).hasDerivWithinAt
  have hb : ∀ t ∈ (Set.univ : Set ℝ),
      ‖(Complex.I * (ω : ℂ)) * oscillatoryPhase ω t‖ ≤ |ω| := by
    intro t _
    simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      norm_oscillatoryPhase, one_mul, mul_one, le_refl]
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
      (Set.mem_univ x) (Set.mem_univ y)

theorem norm_sum_variation_weight_le (w u : ℕ → ℂ) (N : ℕ) {D B : ℝ}
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hw : ∀ n < N, ‖w n‖ ≤ 1)
    (hvar : ∀ n, n + 1 < N → ‖w (n + 1) - w n‖ ≤ D)
    (hsum : ∀ n ≤ N, ‖∑ i ∈ Finset.range n, u i‖ ≤ B) :
    ‖∑ i ∈ Finset.range N, w i * u i‖ ≤ (1 + (N : ℝ) * D) * B := by
  cases N with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty, norm_zero, Nat.cast_zero,
      zero_mul, add_zero, one_mul] using hB
  | succ N =>
    have hid : (∑ i ∈ Finset.range (N + 1), w i * u i) =
        w N * (∑ i ∈ Finset.range (N + 1), u i) -
          ∑ i ∈ Finset.range N, (w (i + 1) - w i) *
            ∑ j ∈ Finset.range (i + 1), u j := by
      simpa only [smul_eq_mul, Nat.succ_sub_one] using
        Finset.sum_range_by_parts w u (N + 1)
    have hlast : ‖w N * ∑ i ∈ Finset.range (N + 1), u i‖ ≤ B := by
      rw [norm_mul]
      exact (mul_le_mul (hw N (Nat.lt_succ_self N)) (hsum _ le_rfl)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul B)
    have hparts : ‖∑ i ∈ Finset.range N, (w (i + 1) - w i) *
        ∑ j ∈ Finset.range (i + 1), u j‖ ≤ (N : ℝ) * (D * B) := by
      calc
        _ ≤ ∑ i ∈ Finset.range N, ‖(w (i + 1) - w i) *
            ∑ j ∈ Finset.range (i + 1), u j‖ := norm_sum_le _ _
        _ ≤ ∑ _i ∈ Finset.range N, D * B := by
          apply Finset.sum_le_sum
          intro i hi
          have hiN := Finset.mem_range.mp hi
          rw [norm_mul]
          exact mul_le_mul (hvar i (by omega)) (hsum (i + 1) (by omega))
            (norm_nonneg _) hD
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hid]
    apply (norm_sub_le _ _).trans ((add_le_add hlast hparts).trans ?_)
    push_cast
    nlinarith

theorem norm_sum_variation_weight_power_le (w u : ℕ → ℂ) (N p : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hw : ∀ n < N, ‖w n‖ ≤ 1)
    (hvar : ∀ n, n + 1 < N → ‖w (n + 1) - w n‖ ≤ D) :
    ‖∑ i ∈ Finset.range N, w i * u i‖ ^ p ≤
      (1 + (N : ℝ) * D) ^ p *
        ∑ m ∈ Finset.range (N + 1), ‖∑ i ∈ Finset.range m, u i‖ ^ p := by
  obtain ⟨m, hm, hmax⟩ := (Finset.range (N + 1)).exists_max_image
    (fun m ↦ ‖∑ i ∈ Finset.range m, u i‖) (by exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩)
  have hb := norm_sum_variation_weight_le w u N hD (norm_nonneg _) hw hvar
    (fun n hn ↦ hmax n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))
  calc
    _ ≤ ((1 + (N : ℝ) * D) * ‖∑ i ∈ Finset.range m, u i‖) ^ p :=
      pow_le_pow_left₀ (norm_nonneg _) hb p
    _ = (1 + (N : ℝ) * D) ^ p * ‖∑ i ∈ Finset.range m, u i‖ ^ p := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun n : ℕ ↦ ‖∑ i ∈ Finset.range n, u i‖ ^ p)
        (fun n _ ↦ pow_nonneg (norm_nonneg _) p) hm) (by positivity)

theorem phase_sum_perturbation_power_le (P d : ℕ → ℝ) (N p : ℕ) {D : ℝ}
    (hD : 0 ≤ D) (hd : ∀ n, n + 1 < N → |d (n + 1) - d n| ≤ D) :
    ‖∑ i ∈ Finset.range N, oscillatoryPhase 1 (P i + d i)‖ ^ p ≤
      (1 + (N : ℝ) * D) ^ p *
        ∑ m ∈ Finset.range (N + 1),
          ‖∑ i ∈ Finset.range m, oscillatoryPhase 1 (P i)‖ ^ p := by
  have hprod (i : ℕ) : oscillatoryPhase 1 (d i) * oscillatoryPhase 1 (P i) =
      oscillatoryPhase 1 (P i + d i) := by
    unfold oscillatoryPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hvar : ∀ n, n + 1 < N →
      ‖oscillatoryPhase 1 (d (n + 1)) - oscillatoryPhase 1 (d n)‖ ≤ D := by
    intro n hn
    have h := oscillatoryPhase_lipschitz 1 (d n) (d (n + 1))
    simp only [abs_one, one_mul] at h
    exact h.trans (hd n hn)
  simpa only [hprod] using norm_sum_variation_weight_power_le
    (fun n ↦ oscillatoryPhase 1 (d n)) (fun n ↦ oscillatoryPhase 1 (P n)) N p hD
    (fun n _ ↦ (norm_oscillatoryPhase 1 (d n)).le) hvar

end Erdos421
