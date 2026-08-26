import ErdosProblems.Erdos421.ComplexPowerError
import Mathlib.Analysis.PSeries

/-! # An entire summand for the regularized zeta function -/

namespace Erdos421

/-- Multiplying the unit sum--integral error by `s - 1` removes its apparent
singularity at `s = 1` and gives this entire expression. -/
noncomputable def zetaErrorTerm (n : ℕ) (s : ℂ) : ℂ :=
  (s - 1) * ((n + 1 : ℕ) : ℂ) ^ (-s) +
    ((n + 2 : ℕ) : ℂ) ^ (1 - s) - ((n + 1 : ℕ) : ℂ) ^ (1 - s)

theorem zetaErrorTerm_one (n : ℕ) : zetaErrorTerm n 1 = 0 := by
  simp [zetaErrorTerm]

theorem zetaErrorTerm_eq_integral_error (n : ℕ) {s : ℂ} (hs : s ≠ 1) :
    zetaErrorTerm n s = (s - 1) *
      (((n + 1 : ℕ) : ℂ) ^ (-s) - ∫ x in (n + 1 : ℕ)..(n + 2 : ℕ), (x : ℂ) ^ (-s)) := by
  have hneg : -s ≠ -1 := fun h ↦ hs (neg_injective h)
  have hzero : (0 : ℝ) ∉ Set.uIcc ((n + 1 : ℕ) : ℝ) ((n + 2 : ℕ) : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))]
    simp only [Set.mem_Icc, not_and]
    intro h
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    linarith
  have hi := integral_cpow (a := ((n + 1 : ℕ) : ℝ)) (b := ((n + 2 : ℕ) : ℝ))
    (r := -s) (Or.inr ⟨hneg, hzero⟩)
  rw [hi]
  simp only [Complex.ofReal_natCast, show -s + 1 = 1 - s by ring]
  unfold zetaErrorTerm
  have hnz : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
  field_simp
  ring

theorem zetaErrorTerm_norm_le (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖zetaErrorTerm n s‖ ≤ ‖s - 1‖ * ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  by_cases hs1 : s = 1
  · subst s
    simp only [zetaErrorTerm_one, norm_zero, sub_self, zero_mul, le_refl]
  · rw [zetaErrorTerm_eq_integral_error n hs1, norm_mul]
    have he : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left
      (cpow_unit_sum_integral_error (by positivity : (0 : ℝ) < (n + 1 : ℕ)) s hs)
      (norm_nonneg (s - 1))
    simpa only [Complex.ofReal_natCast, mul_assoc] using hb

theorem differentiable_zetaErrorTerm (n : ℕ) : Differentiable ℂ (zetaErrorTerm n) := by
  have h₁ : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 1 ≠ 0 by omega)
  have h₂ : ((n + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show n + 2 ≠ 0 by omega)
  have hd : Differentiable ℂ (fun s : ℂ ↦ -s) := differentiable_id.neg
  have he : Differentiable ℂ (fun s : ℂ ↦ 1 - s) := (differentiable_const 1).sub differentiable_id
  exact ((differentiable_id.sub (differentiable_const 1)).mul (hd.const_cpow (Or.inl h₁))).add
    (he.const_cpow (Or.inl h₂)) |>.sub (he.const_cpow (Or.inl h₁))

theorem summable_zetaErrorTerm {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ ↦ zetaErrorTerm n s) := by
  have hp : Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    exact (summable_nat_add_iff 1 (f := fun n : ℕ ↦ (n : ℝ) ^ (-s.re - 1))).mpr
      (Real.summable_nat_rpow.mpr (by linarith))
  exact (hp.mul_left (‖s - 1‖ * ‖s‖)).of_norm_bounded (fun n ↦ zetaErrorTerm_norm_le n hs)

theorem sum_zetaErrorTerm (N : ℕ) (s : ℂ) :
    (∑ n ∈ Finset.range N, zetaErrorTerm n s) =
      (s - 1) * zetaBlock 1 N s + ((N + 1 : ℕ) : ℂ) ^ (1 - s) - 1 := by
  induction N with
  | zero => simp [zetaBlock]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    unfold zetaBlock zetaErrorTerm
    rw [Finset.sum_range_succ]
    simp only [Nat.add_assoc, Nat.add_comm 1 N]
    ring

end Erdos421
