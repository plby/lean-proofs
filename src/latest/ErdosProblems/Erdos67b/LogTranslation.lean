import ErdosProblems.Erdos67b.LogProbability
import Mathlib.Algebra.BigOperators.Module

/-!
# Uniform translation estimates for finite logarithmic laws

Finite summation by parts gives a uniform estimate for every bounded
function, hence also for every coordinate of a fixed finite block law.
-/

open scoped BigOperators
open Finset

namespace Erdos67b

/-- The finite Dirichlet bound for nonnegative decreasing real weights.
All partial-sum estimates are hypotheses on finite sums, not analytic
oracles. -/
theorem norm_sum_smul_le_of_antitone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → ℝ) (v : ℕ → E) (N : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hw : ∀ i, 0 ≤ w i) (hmono : Antitone w)
    (hv : ∀ n ≤ N, ‖∑ i ∈ range n, v i‖ ≤ D) :
    ‖∑ i ∈ range N, w i • v i‖ ≤ D * w 0 := by
  by_cases hN : N = 0
  · simp [hN, mul_nonneg hD (hw 0)]
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  rw [Finset.sum_range_by_parts]
  calc
    ‖w (N - 1) • (∑ i ∈ range N, v i) -
        ∑ i ∈ range (N - 1), (w (i + 1) - w i) • (∑ j ∈ range (i + 1), v j)‖ ≤
        ‖w (N - 1) • (∑ i ∈ range N, v i)‖ +
          ∑ i ∈ range (N - 1),
            ‖(w (i + 1) - w i) • (∑ j ∈ range (i + 1), v j)‖ :=
      (norm_sub_le _ _).trans (add_le_add (le_refl _) (norm_sum_le _ _))
    _ ≤ w (N - 1) * D + ∑ i ∈ range (N - 1), (w i - w (i + 1)) * D := by
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw _)]
        exact mul_le_mul_of_nonneg_left (hv N le_rfl) (hw _)
      · apply Finset.sum_le_sum
        intro i hi
        have hiN := Finset.mem_range.mp hi
        have hdiff := hmono (Nat.le_succ i)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hdiff), neg_sub]
        exact mul_le_mul_of_nonneg_left (hv (i + 1) (by omega)) (sub_nonneg.mpr hdiff)
    _ = D * w 0 := by
      rw [← Finset.sum_mul, Finset.sum_range_sub']
      ring

/-- A single shift of a bounded sequence has uniformly bounded weighted
discrepancy under any decreasing nonnegative weights. -/
theorem norm_weighted_shift_one_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → ℝ) (F : ℕ → E) (N : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ i, 0 ≤ w i) (hmono : Antitone w) (hF : ∀ i ≤ N, ‖F i‖ ≤ B) :
    ‖∑ i ∈ range N, w i • (F (i + 1) - F i)‖ ≤ 2 * B * w 0 := by
  apply norm_sum_smul_le_of_antitone w _ N (by positivity) hw hmono
  intro n hn
  rw [Finset.sum_range_sub]
  exact (norm_sub_le _ _).trans (by linarith [hF n hn, hF 0 (Nat.zero_le N)])

/-- Iterate the one-step estimate over an arbitrary finite translation. -/
theorem norm_weighted_shift_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → ℝ) (F : ℕ → E) (N h : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ i, 0 ≤ w i) (hmono : Antitone w) (hF : ∀ i, ‖F i‖ ≤ B) :
    ‖∑ i ∈ range N, w i • (F (i + h) - F i)‖ ≤ 2 * B * h * w 0 := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hstep := norm_weighted_shift_one_le w (fun i ↦ F (i + h)) N hB hw hmono
      (fun i _ ↦ hF (i + h))
    have hsplit : (∑ i ∈ range N, w i • (F (i + (h + 1)) - F i)) =
        (∑ i ∈ range N, w i • (F ((i + 1) + h) - F (i + h))) +
          ∑ i ∈ range N, w i • (F (i + h) - F i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← smul_add]
      congr 1
      rw [sub_add_sub_cancel]
      congr 2
      omega
    rw [hsplit]
    have h := (norm_add_le _ _).trans (add_le_add hstep ih)
    push_cast
    nlinarith

/-- Separate the normalizing mass from the finite harmonic sum. -/
theorem logProbExpectation_eq_mass_inv_smul_sum
    {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (L U : ℕ) (F : ℕ → E) :
    logProbExpectation L U F = (logProbMassNN L U : ℝ)⁻¹ •
      (∑ n ∈ Finset.Icc L U, (n : ℝ)⁻¹ • F n) := by
  rw [logProbExpectation_eq_window_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [NNReal.coe_div, logProbHarmonicNN_coe, div_eq_mul_inv, smul_smul]
  rw [mul_comm]

/-- Uniform translation invariance for the actual logarithmic law. -/
theorem norm_logProbExpectation_translate_sub_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) (h : ℕ)
    (F : ℕ → E) {B : ℝ} (hB : 0 ≤ B) (hF : ∀ n, L ≤ n → ‖F n‖ ≤ B) :
    ‖logProbExpectation L U (fun n ↦ F (n + h)) - logProbExpectation L U F‖ ≤
      2 * B * h / ((L : ℝ) * logProbMassNN L U) := by
  have hM : (0 : ℝ) < logProbMassNN L U := by
    exact_mod_cast logProbMassNN_pos hL hLU
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hw (i : ℕ) : 0 ≤ (((L + i : ℕ) : ℝ)⁻¹) := by positivity
  have hmono : Antitone (fun i : ℕ ↦ (((L + i : ℕ) : ℝ)⁻¹)) := by
    intro i j hij
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_left hij L
  have hsum := norm_weighted_shift_le
    (fun i : ℕ ↦ (((L + i : ℕ) : ℝ)⁻¹)) (fun i ↦ F (L + i))
    (U + 1 - L) h hB hw hmono (fun i ↦ hF (L + i) (Nat.le_add_right _ _))
  have hI : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [logProbExpectation_eq_mass_inv_smul_sum,
    logProbExpectation_eq_mass_inv_smul_sum, ← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← smul_sub]
  rw [hI, Finset.sum_Ico_eq_sum_range, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hM.le)]
  have hscaled := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hM.le)
  simp only [Nat.add_zero] at hscaled
  simpa only [Nat.add_assoc, div_eq_mul_inv, mul_inv_rev,
    mul_assoc, mul_comm, mul_left_comm] using hscaled

/-- Point masses of a finite observable are indicator expectations. -/
theorem logProb_law_apply_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) (F : ℕ → α) (a : α) :
    FiniteEntropy.law (logProbFiniteLaw L U hL hLU) (fun n ↦ F n.1) a =
      logProbExpectation L U (fun n ↦ if F n = a then (1 : ℝ) else 0) := by
  simp only [FiniteEntropy.law, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, logProbFiniteLaw_apply, logProbExpectation,
    smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- Uniform `L¹` translation estimate for any observable with fixed
finite alphabet. A cardinality factor suffices because the alphabet is
chosen before the lower endpoint tends to infinity. -/
theorem l1Dist_logProb_law_translate_le
    {α : Type*} [Fintype α]
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U) (h : ℕ) (F : ℕ → α) :
    FiniteEntropy.l1Dist
      (FiniteEntropy.law (logProbFiniteLaw L U hL hLU) (fun n ↦ F (n.1 + h)))
      (FiniteEntropy.law (logProbFiniteLaw L U hL hLU) (fun n ↦ F n.1)) ≤
      Fintype.card α * (2 * h / ((L : ℝ) * logProbMassNN L U)) := by
  classical
  unfold FiniteEntropy.l1Dist
  have hcoord (a : α) :
      |FiniteEntropy.law (logProbFiniteLaw L U hL hLU) (fun n ↦ F (n.1 + h)) a -
        FiniteEntropy.law (logProbFiniteLaw L U hL hLU) (fun n ↦ F n.1) a| ≤
          2 * h / ((L : ℝ) * logProbMassNN L U) := by
    rw [logProb_law_apply_eq hL hLU (fun n ↦ F (n + h)) a,
      logProb_law_apply_eq hL hLU F a]
    have hbound := norm_logProbExpectation_translate_sub_le hL hLU h
      (fun n ↦ if F n = a then (1 : ℝ) else 0) (B := 1) zero_le_one
      (by intro n _; split_ifs <;> norm_num)
    simpa only [Real.norm_eq_abs, mul_one] using hbound
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) ↦ hcoord a)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum

/-- Real harmonic mass as a sum over the ordinary integer interval. -/
theorem logProbMassNN_coe_eq_Icc_sum (L U : ℕ) :
    (logProbMassNN L U : ℝ) = ∑ n ∈ Finset.Icc L U, (n : ℝ)⁻¹ := by
  simp only [logProbMassNN, NNReal.coe_sum, logProbHarmonicNN_coe]
  exact (Finset.sum_subtype (logProbWindow L U) (fun _ ↦ Iff.rfl)
    (fun n ↦ (n : ℝ)⁻¹)).symm

/-- Windows containing a full doubling interval have uniformly positive
normalizing mass. -/
theorem half_le_logProbMassNN {L U : ℕ} (hL : 0 < L) (hU : 2 * L ≤ U) :
    (1 / 2 : ℝ) ≤ logProbMassNN L U := by
  rw [logProbMassNN_coe_eq_Icc_sum]
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hsub : Finset.Icc L (2 * L) ⊆ Finset.Icc L U := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hU⟩
  have hweights : ∀ n ∈ Finset.Icc L (2 * L), (1 / (2 * L : ℝ)) ≤ (n : ℝ)⁻¹ := by
    intro n hn
    have hnL := (Finset.mem_Icc.mp hn).1
    have hnU := (Finset.mem_Icc.mp hn).2
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (hL.trans_le hnL)
    simpa only [one_div] using one_div_le_one_div_of_le hnpos
      (show (n : ℝ) ≤ 2 * L by exact_mod_cast hnU)
  have hsum := Finset.sum_le_sum hweights
  have hcard : (Finset.Icc L (2 * L)).card = L + 1 := by
    rw [Nat.card_Icc]
    omega
  rw [Finset.sum_const, hcard, nsmul_eq_mul] at hsum
  have hhalf : (1 / 2 : ℝ) ≤ (L + 1 : ℕ) * (1 / (2 * L : ℝ)) := by
    push_cast
    field_simp
    linarith
  exact (hhalf.trans hsum).trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ ↦ by positivity))

/-- A simpler estimate uniform in the upper endpoint. -/
theorem l1Dist_logProb_law_translate_le_of_double
    {α : Type*} [Fintype α]
    {L U : ℕ} (hL : 0 < L) (hU : 2 * L ≤ U) (h : ℕ) (F : ℕ → α) :
    FiniteEntropy.l1Dist
      (FiniteEntropy.law (logProbFiniteLaw L U hL (by omega)) (fun n ↦ F (n.1 + h)))
      (FiniteEntropy.law (logProbFiniteLaw L U hL (by omega)) (fun n ↦ F n.1)) ≤
      4 * Fintype.card α * h / L := by
  have hdist := l1Dist_logProb_law_translate_le hL (by omega : L ≤ U) h F
  have hM := half_le_logProbMassNN hL hU
  have hLr : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hMr : (0 : ℝ) < logProbMassNN L U := by linarith
  have hden : (L : ℝ) / 2 ≤ (L : ℝ) * logProbMassNN L U := by nlinarith
  have hbound := div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ 2 * (h : ℕ))
    (by positivity : (0 : ℝ) < (L : ℝ) / 2) hden
  have hscaled := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg (Fintype.card α))
  exact hdist.trans (by convert hscaled using 1 <;> field_simp <;> ring)

end Erdos67b
