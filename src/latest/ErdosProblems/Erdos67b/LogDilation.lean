import ErdosProblems.Erdos67b.LogTranslation

/-!
# Dilation invariance of the actual logarithmic window

The exact lattice substitution is combined with an endpoint estimate.
The error is uniform in both window endpoints and is sufficient when
the dilation parameters are fixed before the harmonic mass grows.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

/-- A multiplicative boundary interval has bounded harmonic mass.
The deliberately coarse bound avoids rounding any real endpoints. -/
theorem norm_sum_harmonic_smul_le_of_mul_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M q : ℕ} (hM : 0 < M) (s : Finset ℕ)
    (hs : s ⊆ Icc 1 M) (hmul : ∀ n ∈ s, M ≤ q * n)
    (F : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ n ∈ s, ‖F n‖ ≤ B) :
    ‖∑ n ∈ s, (n : ℝ)⁻¹ • F n‖ ≤ q * B := by
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hweight (n : ℕ) (hn : n ∈ s) : (n : ℝ)⁻¹ ≤ (q : ℝ) / M := by
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (Finset.mem_Icc.mp (hs hn)).1
    rw [← one_div]
    apply (div_le_div_iff₀ hnpos hMr).mpr
    simpa only [one_mul, Nat.cast_mul] using (show (M : ℝ) ≤ (q * n : ℕ) by
      exact_mod_cast hmul n hn)
  have hcard : s.card ≤ M := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs
  calc
    ‖∑ n ∈ s, (n : ℝ)⁻¹ • F n‖ ≤ ∑ n ∈ s, ‖(n : ℝ)⁻¹ • F n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ s, ((q : ℝ) / M) * B := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
      exact mul_le_mul (hweight n hn) (hF n hn) (norm_nonneg _) (by positivity)
    _ = (s.card : ℝ) * ((q : ℝ) / M * B) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ℝ) * ((q : ℝ) / M * B) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = q * B := by field_simp

/-- Preimages in the original window under a positive dilation. -/
def logDilationPreimage (L U q : ℕ) : Finset ℕ :=
  (Icc 1 U).filter fun n ↦ L ≤ q * n ∧ q * n ≤ U

/-- Exact finite change of variables, with the normalization still absent. -/
theorem sum_logDilationPreimage
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {L U q : ℕ} (hL : 0 < L) (hq : 0 < q) (F : ℕ → E) :
    (∑ n ∈ logDilationPreimage L U q, (n : ℝ)⁻¹ • F (q * n)) =
      (q : ℝ) • ∑ m ∈ Icc L U, (m : ℝ)⁻¹ • (if q ∣ m then F m else 0) := by
  classical
  have hq1 : 1 ≤ q := hq
  have hqr : (q : ℝ) ≠ 0 := by positivity
  simp only [smul_ite, smul_zero]
  rw [← Finset.sum_filter, Finset.smul_sum]
  apply Finset.sum_bij (fun n _ ↦ q * n)
  · intro n hn
    have hn' := (Finset.mem_filter.mp hn).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hn', dvd_mul_right q n⟩
  · intro n hn m hm heq
    exact Nat.eq_of_mul_eq_mul_left hq heq
  · intro m hm
    obtain ⟨hmI, hqm⟩ := Finset.mem_filter.mp hm
    obtain ⟨n, rfl⟩ := hqm
    have hn : 0 < n := by
      have hprod := hL.trans_le (Finset.mem_Icc.mp hmI).1
      by_contra hn
      have hn0 : n = 0 := by omega
      simp [hn0] at hprod
    refine ⟨n, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hn, ?_⟩, Finset.mem_Icc.mp hmI⟩
    exact (Nat.le_mul_of_pos_left n hq).trans (Finset.mem_Icc.mp hmI).2
  · intro n hn
    rw [smul_smul]
    congr 1
    simp only [Nat.cast_mul, mul_inv_rev]
    field_simp

/-- Before normalization, only two multiplicative endpoint strips remain. -/
theorem norm_sum_dilation_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U q : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    (F : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    ‖(∑ n ∈ Icc L U, (n : ℝ)⁻¹ • F (q * n)) -
      (q : ℝ) • ∑ n ∈ Icc L U, (n : ℝ)⁻¹ • (if q ∣ n then F n else 0)‖ ≤
        2 * B * q := by
  classical
  rw [← sum_logDilationPreimage hL hq F, ← Finset.sum_sdiff_sub_sum_sdiff]
  have hupper :
      ‖∑ n ∈ Icc L U \ logDilationPreimage L U q, (n : ℝ)⁻¹ • F (q * n)‖ ≤ q * B := by
    apply norm_sum_harmonic_smul_le_of_mul_lower (hL.trans_le hLU) _
    · intro n hn
      have hnI := Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1
      exact Finset.mem_Icc.mpr ⟨hL.trans_le hnI.1, hnI.2⟩
    · intro n hn
      obtain ⟨hnI, hnT⟩ := Finset.mem_sdiff.mp hn
      have hnL := (Finset.mem_Icc.mp hnI).1
      have hnU := (Finset.mem_Icc.mp hnI).2
      have hqn : L ≤ q * n := hnL.trans (Nat.le_mul_of_pos_left n hq)
      have hnpos : 1 ≤ n := hL.trans_le hnL
      simp only [logDilationPreimage, Finset.mem_filter, Finset.mem_Icc,
        hnpos, hnU, hqn, true_and, not_le] at hnT
      exact hnT.le
    · exact hB
    · intro n hn
      exact hF (q * n) (Nat.mul_pos hq (hL.trans_le
        (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hn).1).1))
  have hlower :
      ‖∑ n ∈ logDilationPreimage L U q \ Icc L U, (n : ℝ)⁻¹ • F (q * n)‖ ≤ q * B := by
    apply norm_sum_harmonic_smul_le_of_mul_lower hL _
    · intro n hn
      obtain ⟨hnT, hnI⟩ := Finset.mem_sdiff.mp hn
      obtain ⟨hn1U, hqn⟩ := Finset.mem_filter.mp hnT
      have hnU := (Finset.mem_Icc.mp hn1U).2
      have hnL : n ≤ L := by
        simp only [Finset.mem_Icc, hnU, and_true, not_le] at hnI
        exact hnI.le
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn1U).1, hnL⟩
    · intro n hn
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).2.1
    · exact hB
    · intro n hn
      exact hF (q * n) (Nat.mul_pos hq
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1).1)
  exact (norm_sub_le _ _).trans (by nlinarith)

/-- Dilation invariance compares expectations on the same original window.
It does not silently replace that window by its dilation. -/
theorem norm_logProbExpectation_dilation_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U q : ℕ} (hL : 0 < L) (hLU : L ≤ U) (hq : 0 < q)
    (F : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ n, 0 < n → ‖F n‖ ≤ B) :
    ‖logProbExpectation L U (fun n ↦ F (q * n)) -
      (q : ℝ) • logProbExpectation L U (fun n ↦ if q ∣ n then F n else 0)‖ ≤
        2 * B * q / (logProbMassNN L U : ℝ) := by
  have hM : (0 : ℝ) < logProbMassNN L U := by
    exact_mod_cast logProbMassNN_pos hL hLU
  rw [logProbExpectation_eq_mass_inv_smul_sum,
    logProbExpectation_eq_mass_inv_smul_sum, smul_comm (q : ℝ), ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hM.le)]
  have h := mul_le_mul_of_nonneg_left (norm_sum_dilation_sub_le hL hLU hq F hB hF)
    (inv_nonneg.mpr hM.le)
  simpa only [div_eq_mul_inv, mul_comm] using h

/-- Each half-open doubling interval carries at least half a unit of
harmonic mass; the half-open convention permits disjoint concatenation. -/
theorem half_le_harmonic_Ico_double {L : ℕ} (hL : 0 < L) :
    (1 / 2 : ℝ) ≤ ∑ n ∈ Finset.Ico L (2 * L), (n : ℝ)⁻¹ := by
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hweight (n : ℕ) (hn : n ∈ Finset.Ico L (2 * L)) :
      (1 : ℝ) / (2 * L) ≤ (n : ℝ)⁻¹ := by
    have hnL := (Finset.mem_Ico.mp hn).1
    have hnU := (Finset.mem_Ico.mp hn).2
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (hL.trans_le hnL)
    simpa only [one_div] using one_div_le_one_div_of_le hnpos
      (show (n : ℝ) ≤ 2 * L by exact_mod_cast hnU.le)
  have hsum := Finset.sum_le_sum hweight
  have hcard : (Finset.Ico L (2 * L)).card = L := by rw [Nat.card_Ico]; omega
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
  have heq : (L : ℝ) * (1 / (2 * L)) = 1 / 2 := by field_simp
  exact heq ▸ hsum

/-- Disjoint doubling intervals provide an elementary quantitative
divergence bound, with no appeal to an unproved asymptotic formula. -/
theorem nat_half_le_harmonic_Ico_pow_two {L : ℕ} (hL : 0 < L) (k : ℕ) :
    (k : ℝ) / 2 ≤ ∑ n ∈ Finset.Ico L (2 ^ k * L), (n : ℝ)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hmid : L ≤ 2 ^ k * L := by nlinarith
    have hpos : 0 < 2 ^ k * L := by positivity
    have hstep := half_le_harmonic_Ico_double hpos
    have hlast : 2 ^ (k + 1) * L = 2 * (2 ^ k * L) := by rw [pow_succ]; ring
    rw [hlast, ← Finset.sum_Ico_consecutive (fun n : ℕ ↦ (n : ℝ)⁻¹)
      hmid (by omega : 2 ^ k * L ≤ 2 * (2 ^ k * L))]
    push_cast
    linarith

/-- An explicit lower bound on the actual normalizing mass. -/
theorem nat_half_le_logProbMassNN_pow_two {L : ℕ} (hL : 0 < L) (k : ℕ) :
    (k : ℝ) / 2 ≤ logProbMassNN L (2 ^ k * L) := by
  rw [logProbMassNN_coe_eq_Icc_sum]
  apply (nat_half_le_harmonic_Ico_pow_two hL k).trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hn).1, (Finset.mem_Ico.mp hn).2.le⟩
  · intro n _ _
    positivity

/-- Every positive lower endpoint admits arbitrarily large harmonic
mass, while retaining the doubling-window condition used in entropy. -/
theorem exists_logProbMassNN_ge {L : ℕ} (hL : 0 < L) (W : ℝ) :
    ∃ U : ℕ, 2 * L ≤ U ∧ W ≤ (logProbMassNN L U : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * W)
  refine ⟨2 ^ (k + 1) * L, ?_, ?_⟩
  · have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    rw [pow_succ]
    nlinarith
  · have hmass := nat_half_le_logProbMassNN_pow_two hL (k + 1)
    push_cast at hmass
    linarith

end Erdos67b
