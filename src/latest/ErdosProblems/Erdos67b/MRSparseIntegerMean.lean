import ErdosProblems.Erdos67b.MRSparseIntegerKernel

/-!
# Sparse integer mean values

One-separation makes the positive distance floors injective. Summing
their reciprocals controls the integer Gram rows, which the proved
finite duality transfers to arbitrary complex coefficients.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

/-- Harmonic summation over one-separated positive distances. -/
theorem mrSum_inv_separated_positive_le
    {ι : Type*} (S : Finset ι) (d : ι → ℝ) {W : ℝ} (hW : 0 ≤ W)
    (hlo : ∀ i ∈ S, 1 ≤ d i) (hhi : ∀ i ∈ S, d i ≤ W)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |d i - d j|) :
    (∑ i ∈ S, 1 / d i) ≤ 1 + Real.log (W + 1) := by
  classical
  let q : ι → ℕ := fun i ↦ ⌊d i⌋₊
  have hinj : ∀ i ∈ S, ∀ j ∈ S, q i = q j → i = j := by
    intro i hi j hj heq
    by_contra hne
    have hgap := hsep i hi j hj hne
    have hi0 : 0 ≤ d i := by linarith [hlo i hi]
    have hj0 : 0 ≤ d j := by linarith [hlo j hj]
    have hil : (q i : ℝ) ≤ d i := Nat.floor_le hi0
    have hjl : (q j : ℝ) ≤ d j := Nat.floor_le hj0
    have hiu : d i < (q i : ℝ) + 1 := Nat.lt_floor_add_one (d i)
    have hju : d j < (q j : ℝ) + 1 := Nat.lt_floor_add_one (d j)
    rw [heq] at hil hiu
    have habs : |d i - d j| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have hsub : S.image q ⊆ Finset.Ico 1 (⌊W⌋₊ + 1) := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    have hloi : 0 < q i := Nat.floor_pos.mpr (hlo i hi)
    have hhii : q i ≤ ⌊W⌋₊ := Nat.floor_mono (hhi i hi)
    exact Finset.mem_Ico.mpr ⟨hloi, by omega⟩
  have hcountlog : Real.log ((⌊W⌋₊ + 1 : ℕ) : ℝ) ≤ Real.log (W + 1) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith [Nat.floor_le hW]
  calc
    _ ≤ ∑ i ∈ S, 1 / (q i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hq : (0 : ℝ) < q i := by exact_mod_cast Nat.floor_pos.mpr (hlo i hi)
      exact one_div_le_one_div_of_le hq (Nat.floor_le (by linarith [hlo i hi]))
    _ = ∑ n ∈ S.image q, 1 / (n : ℝ) :=
      (Finset.sum_image (f := fun n : ℕ ↦ (1 : ℝ) / n) hinj).symm
    _ ≤ ∑ n ∈ Finset.Ico 1 (⌊W⌋₊ + 1), 1 / (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ 1 + Real.log ((⌊W⌋₊ + 1 : ℕ) : ℝ) :=
      LogSecondDerivative.sum_Ico_one_div_le_one_add_log (by omega)
    _ ≤ _ := by linarith

/-- Sum the reciprocal gaps on both sides of one selected sample. -/
theorem mrSeparated_reciprocal_gap_sum_le
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {s : ℝ} (hs : s ∈ S) :
    (∑ t ∈ S.erase s, 1 / |t - s|) ≤ 2 * (1 + Real.log (2 * T + 1)) := by
  classical
  let R : Finset ℝ := S.erase s
  let A : Finset ℝ := R.filter (fun t ↦ s < t)
  let B : Finset ℝ := R.filter (fun t ↦ ¬s < t)
  have hR (t : ℝ) (ht : t ∈ R) : t ∈ S ∧ t ≠ s := by
    have hh := Finset.mem_erase.mp ht
    exact ⟨hh.2, hh.1⟩
  have hgap (t : ℝ) (ht : t ∈ R) : 1 ≤ |t - s| := hsep t (hR t ht).1 s hs (hR t ht).2
  have hmax (t : ℝ) (ht : t ∈ R) : |t - s| ≤ 2 * T := by
    have hh := abs_sub_le t 0 s
    simp only [sub_zero, zero_sub, abs_neg] at hh
    linarith [hST t (hR t ht).1, hST s hs]
  have hApos (t : ℝ) (ht : t ∈ A) : s < t := (Finset.mem_filter.mp ht).2
  have hBneg (t : ℝ) (ht : t ∈ B) : t < s := by
    have hh := Finset.mem_filter.mp ht
    have hne := (hR t hh.1).2
    exact lt_of_le_of_ne (le_of_not_gt hh.2) hne
  have hA := mrSum_inv_separated_positive_le A (fun t ↦ t - s) (by positivity : 0 ≤ 2 * T)
    (fun t ht ↦ by simpa only [abs_of_pos (sub_pos.mpr (hApos t ht))] using hgap t (Finset.mem_filter.mp ht).1)
    (fun t ht ↦ by simpa only [abs_of_pos (sub_pos.mpr (hApos t ht))] using hmax t (Finset.mem_filter.mp ht).1)
    (fun t ht u hu hne ↦ by
      have hh := hsep t (hR t (Finset.mem_filter.mp ht).1).1 u (hR u (Finset.mem_filter.mp hu).1).1 hne
      simpa only [sub_sub_sub_cancel_right] using hh)
  have hB := mrSum_inv_separated_positive_le B (fun t ↦ s - t) (by positivity : 0 ≤ 2 * T)
    (fun t ht ↦ by
      have hh := hgap t (Finset.mem_filter.mp ht).1
      rw [abs_of_neg (sub_neg.mpr (hBneg t ht))] at hh
      linarith)
    (fun t ht ↦ by
      have hh := hmax t (Finset.mem_filter.mp ht).1
      rw [abs_of_neg (sub_neg.mpr (hBneg t ht))] at hh
      linarith)
    (fun t ht u hu hne ↦ by
      have hh := hsep u (hR u (Finset.mem_filter.mp hu).1).1 t (hR t (Finset.mem_filter.mp ht).1).1 hne.symm
      simpa only [sub_sub_sub_cancel_left] using hh)
  have hsplit : (∑ t ∈ R, 1 / |t - s|) =
      (∑ t ∈ A, 1 / (t - s)) + ∑ t ∈ B, 1 / (s - t) := by
    rw [← Finset.sum_filter_add_sum_filter_not R (fun t ↦ s < t)]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro t ht
      rw [abs_of_pos (sub_pos.mpr (hApos t ht))]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [abs_of_neg (sub_neg.mpr (hBneg t ht)), neg_sub]
  change (∑ t ∈ R, 1 / |t - s|) ≤ _
  rw [hsplit]
  linarith

/-- Explicit sparse integer energy constant; the sample count appears
next to `sqrt(2T)`, rather than the full time length. -/
def mrSparseIntegerEnergyBudget (N M : ℕ) (T : ℝ) : ℝ :=
  (N : ℝ) + 12 * Real.pi * N * (1 + Real.log (2 * T + 1)) +
    800 * M * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2

theorem mrSparseIntegerEnergyBudget_nonneg (N M : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    0 ≤ mrSparseIntegerEnergyBudget N M T := by
  have hlog : 0 ≤ Real.log (2 * T + 1) := Real.log_nonneg (by linarith)
  unfold mrSparseIntegerEnergyBudget
  positivity

/-- The arithmetic Gram row bound for a one-separated set of frequencies. -/
theorem mrSparse_integer_kernel_row_le
    (N : ℕ) (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    {s : ℝ} (hs : s ∈ S) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) (t - s)‖) ≤
      mrSparseIntegerEnergyBudget N S.card T := by
  classical
  let B : ℝ := 800 * Real.sqrt (2 * T) * (1 + Real.log (16 * T)) ^ 2
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpoint (t : ℝ) (ht : t ∈ S.erase s) :
      ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) (t - s)‖ ≤
        6 * Real.pi * N / |t - s| + B := by
    have hne := (Finset.mem_erase.mp ht).1
    have htS := (Finset.mem_erase.mp ht).2
    have hgap := hsep t htS s hs hne
    have hmax : |t - s| ≤ 2 * T := by
      have hh := abs_sub_le t 0 s
      simp only [sub_zero, zero_sub, abs_neg] at hh
      linarith [hST t htS, hST s hs]
    have hlog : 1 + Real.log (8 * |t - s|) ≤ 1 + Real.log (16 * T) := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 8 * |t - s|)
        (by linarith : 8 * |t - s| ≤ 16 * T)
      linarith
    have hlog0 : 0 ≤ 1 + Real.log (8 * |t - s|) := by
      have hh := Real.log_nonneg (show (1 : ℝ) ≤ 8 * |t - s| by linarith)
      linarith
    apply (mrLogarithmicIntegerKernel_le N hgap).trans
    apply add_le_add le_rfl
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmax) (by norm_num))
      (pow_le_pow_left₀ hlog0 hlog 2) (by positivity) (by positivity)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hfactor : (∑ t ∈ S.erase s, 6 * Real.pi * N / |t - s|) =
      6 * Real.pi * N * ∑ t ∈ S.erase s, 1 / |t - s| := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hfactor] at hsum
  have hrecip := mul_le_mul_of_nonneg_left
    (mrSeparated_reciprocal_gap_sum_le S (by linarith : 0 ≤ T) hST hsep hs)
    (show (0 : ℝ) ≤ 6 * Real.pi * N by positivity)
  have hcard : ((S.erase s).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (Finset.erase_subset s S)
  have hcardB := mul_le_mul_of_nonneg_right hcard hB
  have hdiag : ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) (fun _ ↦ 1) (s - s)‖ = N := by
    simp only [sub_self, logarithmicDirichletPolynomial, logarithmicPhase, zero_mul,
      Complex.ofReal_zero, Complex.exp_zero, mul_one, Finset.sum_const, nsmul_eq_mul,
      Nat.card_Icc, Nat.add_sub_cancel, Complex.norm_natCast]
  rw [← Finset.sum_erase_add _ _ hs, hdiag]
  unfold mrSparseIntegerEnergyBudget
  dsimp only [B] at hsum hcardB
  nlinarith

/-- Sparse integer Halász mean value with an explicit logarithmic budget.
This is unconditional for arbitrary complex coefficients. -/
theorem mrSparse_integer_meanValue_le
    (N : ℕ) (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial (Finset.Icc 1 N) a t‖ ^ 2) ≤
      mrSparseIntegerEnergyBudget N S.card T * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
  mrSparse_logarithmic_energy_le_of_kernel_rows (Finset.Icc 1 N) S
    (mrSparseIntegerEnergyBudget_nonneg N S.card hT)
    (fun _ hs ↦ mrSparse_integer_kernel_row_le N S hT hST hsep hs) a

/-- Arbitrary finite positive support version for the Ramaré cofactors. -/
theorem mrSparse_integer_meanValue_le_support
    {A : Finset ℕ} {N : ℕ} (hApos : ∀ n ∈ A, 0 < n) (hAN : ∀ n ∈ A, n ≤ N)
    (S : Finset ℝ) {T : ℝ} (hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (a : ℕ → ℂ) :
    (∑ t ∈ S, ‖logarithmicDirichletPolynomial A a t‖ ^ 2) ≤
      mrSparseIntegerEnergyBudget N S.card T * ∑ n ∈ A, ‖a n‖ ^ 2 := by
  classical
  let b : ℕ → ℂ := fun n ↦ if n ∈ A then a n else 0
  have hsub : A ⊆ Finset.Icc 1 N := fun n hn ↦ Finset.mem_Icc.mpr ⟨hApos n hn, hAN n hn⟩
  have hpoly (t : ℝ) : logarithmicDirichletPolynomial (Finset.Icc 1 N) b t =
      logarithmicDirichletPolynomial A a t := by
    unfold logarithmicDirichletPolynomial
    calc
      _ = ∑ n ∈ A, b n * logarithmicPhase n t :=
        (Finset.sum_subset hsub (fun n hn hnot ↦ by simp only [b, if_neg hnot, zero_mul])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [b, if_pos hn]
  have hmass : (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) = ∑ n ∈ A, ‖a n‖ ^ 2 := by
    calc
      _ = ∑ n ∈ A, ‖b n‖ ^ 2 :=
        (Finset.sum_subset hsub (fun n hn hnot ↦ by simp only [b, if_neg hnot, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow])).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro n hn
        simp only [b, if_pos hn]
  have hh := mrSparse_integer_meanValue_le N S hT hST hsep b
  simpa only [hpoly, hmass] using hh

end

end Erdos67b
