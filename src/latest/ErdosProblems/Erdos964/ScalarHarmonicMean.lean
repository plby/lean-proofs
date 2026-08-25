import ErdosProblems.Erdos964.ScalarRadical
import BoundedGaps.Maynard.CoprimeHarmonicGlobalBound
import BoundedGaps.Maynard.ReciprocalTotientCorrection
import BoundedGaps.Maynard.WeightedSmoothAbel

/-!
# The fixed-modulus harmonic mean

The coprime harmonic cumulative sum has bounded error from its density
times the logarithm. No uniformity in the fixed modulus is asserted here.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_squarefree_coprime_harmonic_bounded_error (W : ℕ) (hW : Squarefree W) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ Q : ℕ, 1 ≤ Q →
      |coprimeHarmonicSum W Q - coprimeHarmonicDensity W * Real.log Q| ≤ E := by
  let δ := coprimeHarmonicDensity W
  let C := 2 * (W.divisors.card : ℝ) + Real.log 2 *
    (∑ d ∈ W.divisors, (1 : ℝ) / d) +
    |δ * (Real.eulerMascheroniConstant + primeLogPredecessorDivisorMass W)|
  let B := ∑ q ∈ Finset.range W, |coprimeHarmonicSum W q - δ * Real.log q|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C + B, add_nonneg hC hB, ?_⟩
  intro Q hQ
  by_cases hWQ : W ≤ Q
  · have hW0 := Nat.pos_of_ne_zero hW.ne_zero
    have hbase := abs_coprimeHarmonicError_le_divisor_envelope hW0 hW hWQ
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hdiv : 2 * (W.divisors.card : ℝ) / Q ≤ 2 * W.divisors.card :=
      div_le_self (by positivity) hQR
    have hmain : coprimeHarmonicMainTerm W Q - δ * Real.log Q =
        δ * (Real.eulerMascheroniConstant + primeLogPredecessorDivisorMass W) := by
      unfold coprimeHarmonicMainTerm
      dsimp only [δ]
      ring
    have h := (abs_sub_le (coprimeHarmonicSum W Q) (coprimeHarmonicMainTerm W Q)
      (δ * Real.log Q)).trans (add_le_add hbase le_rfl)
    rw [hmain] at h
    change |coprimeHarmonicSum W Q - δ * Real.log Q| ≤ _
    calc
      _ ≤ C := by dsimp only [C]; linarith
      _ ≤ C + B := le_add_of_nonneg_right hB
  · have hmem : Q ∈ Finset.range W := Finset.mem_range.mpr (by omega)
    have hsingle := Finset.single_le_sum (f := fun q =>
      |coprimeHarmonicSum W q - δ * Real.log q|) (fun _ _ => abs_nonneg _) hmem
    exact hsingle.trans (le_add_of_nonneg_left hC)

theorem exists_coprime_harmonic_bounded_error (M : ℕ) (hM : 0 < M) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ Q : ℕ, 1 ≤ Q →
      |coprimeHarmonicSum M Q - coprimeHarmonicDensity M * Real.log Q| ≤ E := by
  obtain ⟨E, hE, hbound⟩ := exists_squarefree_coprime_harmonic_bounded_error
    (UniqueFactorizationMonoid.radical M) UniqueFactorizationMonoid.squarefree_radical
  refine ⟨E, hE, ?_⟩
  intro Q hQ
  have hsum : coprimeHarmonicSum (UniqueFactorizationMonoid.radical M) Q =
      coprimeHarmonicSum M Q := by
    unfold coprimeHarmonicSum
    simp only [coprime_radical_iff M _ hM.ne']
  simpa only [hsum, coprimeHarmonicDensity_radical M hM] using hbound Q hQ

theorem coprimeHarmonicAF_cumulative (M : ℕ) (t : ℝ) :
    abelCumulative (coprimeHarmonicAF M) t = coprimeHarmonicSum M ⌊t⌋₊ := by
  classical
  unfold abelCumulative coprimeHarmonicSum
  rw [Finset.sum_filter]
  have hinterval (Q : ℕ) : Finset.Icc 0 Q = insert 0 (Finset.Icc 1 Q) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hinterval, Finset.sum_insert (by simp)]
  simp only [ArithmeticFunction.map_zero, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coprimeHarmonicAF_apply, if_neg (by have := (Finset.mem_Icc.mp hn).1; omega)]

theorem exists_coprime_harmonic_cumulative_bounded_error (M : ℕ) (hM : 0 < M) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 1 ≤ t →
      |abelCumulative (coprimeHarmonicAF M) t -
        coprimeHarmonicDensity M * Real.log t| ≤ E := by
  obtain ⟨E, hE, hbound⟩ := exists_coprime_harmonic_bounded_error M hM
  let δ := coprimeHarmonicDensity M
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  refine ⟨E + δ * Real.log 2, by positivity, ?_⟩
  intro t ht
  have hQ : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr ht
  have hfloor : |δ * Real.log (⌊t⌋₊ : ℕ) - δ * Real.log t| ≤ δ * Real.log 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hδ]
    exact mul_le_mul_of_nonneg_left (abs_log_natFloor_sub_log_le_log_two_global ht) hδ
  rw [coprimeHarmonicAF_cumulative]
  exact (abs_sub_le _ (δ * Real.log (⌊t⌋₊ : ℕ)) _).trans (add_le_add (hbound _ hQ) hfloor)

end Erdos964
