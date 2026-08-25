import ErdosProblems.Erdos964.ScalarKernelPolynomial
import ErdosProblems.Erdos964.ScalarTransformSquareError
import ErdosProblems.Erdos964.ScalarPrimeDivisorMass
import ErdosProblems.Erdos964.WeightedCutError

/-!
# Quantitative approximation of the actual second scalar kernel

The two errors are the transform approximation and the omitted prime-divisor
mass. Both are uniform in the distinguished prime.
-/

namespace Erdos964

open BoundedGaps.Maynard

theorem exists_scalar_prime_kernel_polynomial_error (M : ℕ) (hM : 0 < M)
    (h2M : 2 ∣ M) (h3M : 3 ∣ M) :
    ∃ K C D : ℝ, 0 < K ∧ 0 ≤ C ∧ 0 ≤ D ∧ ∀ R p : ℕ,
      2 ≤ Real.log R → p.Prime → p.Coprime M →
      |scalarCandidatePrimeKernel M R p - scalarPolynomialPrimeKernel M R p| ≤
        D * (1 + Real.log R) ^ 2 *
          ((2 * scalarTransformErrorEnvelope M R K C) *
              (2 * scalarTransformErrorEnvelope M R K C +
                16 * (coprimeHarmonicDensity M * Real.log R)) +
            (512 / (p : ℝ)) * coprimeHarmonicDensity M ^ 2 * (Real.log R) ^ 2) := by
  classical
  obtain ⟨K, C, hK, hC, htransform⟩ := exists_uniform_scalar_transform_difference_sq_error
  obtain ⟨D₁, hD₁, hgrowth⟩ := exists_scalarMoment_two_cumulative_growth M hM h2M h3M
  obtain ⟨D₂, hD₂, hmass⟩ := exists_scalarMoment_two_prime_divisor_mass_bound M hM h2M h3M
  refine ⟨K, C, D₁ + D₂, hK, hC, add_nonneg hD₁ hD₂, ?_⟩
  intro R p hR hp hpM
  let δ := coprimeHarmonicDensity M
  let T := (1 + Real.log R) ^ 2
  let E := (2 * scalarTransformErrorEnvelope M R K C) *
    (2 * scalarTransformErrorEnvelope M R K C + 16 * (δ * Real.log R))
  let U := 64 * δ ^ 2 * (Real.log R) ^ 2
  let A : ℕ → ℝ := fun r =>
    (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
      scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) (p * r)) ^ 2
  let B : ℕ → ℝ := fun r =>
    (δ * (scalarTransformPolynomial R r - scalarTransformPolynomial R (p * r))) ^ 2
  have hδ : 0 ≤ δ := by dsimp [δ, coprimeHarmonicDensity]; positivity
  have hT : 0 ≤ T := sq_nonneg _
  have he : 0 ≤ scalarTransformErrorEnvelope M R K C :=
    scalarTransformErrorEnvelope_nonneg M R K C hK.le hC hR
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hRone : 1 ≤ R := by
    by_contra h
    have hzero : R = 0 := by omega
    subst R
    norm_num at hR
  have hw (r : ℕ) : 0 ≤ scalarMomentAF M 2 r := scalarMomentAF_nonneg M 2 r h2M h3M
  have hkeep (r : ℕ) (_hr : r ∈ Finset.Ico 1 R) (hpr : ¬p ∣ r) :
      |scalarMomentAF M 2 r * A r - scalarMomentAF M 2 r * B r| ≤ E * scalarMomentAF M 2 r := by
    by_cases hs : Squarefree r ∧ r.Coprime M
    · have hpc := hp.coprime_iff_not_dvd.mpr hpr
      have hsq : Squarefree (p * r) := (Nat.squarefree_mul hpc).mpr ⟨hp.squarefree, hs.1⟩
      have hcop : (p * r).Coprime M := hpM.mul_left hs.2
      have h := htransform M R r (p * r) hM hR hs.1 hs.2 hsq hcop
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw r)]
      calc
        _ ≤ scalarMomentAF M 2 r * E := mul_le_mul_of_nonneg_left h (hw r)
        _ = _ := mul_comm _ _
    · have hz : scalarMomentAF M 2 r = 0 := by rw [scalarMomentAF_apply, if_neg hs]
      simp only [hz, zero_mul, sub_self, abs_zero, mul_zero, le_refl]
  have hremove (r : ℕ) (_hr : r ∈ Finset.Ico 1 R) (_hpr : p ∣ r) :
      |scalarMomentAF M 2 r * B r| ≤ U * scalarMomentAF M 2 r := by
    rw [abs_mul, abs_of_nonneg (hw r), abs_of_nonneg (show 0 ≤ B r from sq_nonneg _)]
    calc
      _ ≤ scalarMomentAF M 2 r * U := mul_le_mul_of_nonneg_left
        (scalarTransformPolynomial_difference_sq_le M R r (p * r) (by linarith)) (hw r)
      _ = _ := mul_comm _ _
  have hbase := weighted_cut_sum_error (Finset.Ico 1 R) (scalarMomentAF M 2) A B
    (fun r => p ∣ r) E U hE (fun r _ => hw r) hkeep hremove
  have hactual : scalarCandidatePrimeKernel M R p =
      ∑ r ∈ Finset.Ico 1 R, if p ∣ r then 0 else scalarMomentAF M 2 r * A r :=
    scalarCandidatePrimeKernel_eq_moment_sum M R p
  rw [← hactual] at hbase
  change |scalarCandidatePrimeKernel M R p - scalarPolynomialPrimeKernel M R p| ≤
    E * (∑ r ∈ Finset.Ico 1 R, scalarMomentAF M 2 r) +
      U * (∑ r ∈ Finset.Ico 1 R, if p ∣ r then scalarMomentAF M 2 r else 0) at hbase
  have hsum : (∑ r ∈ Finset.Ico 1 R, scalarMomentAF M 2 r) ≤ D₁ * T := by
    calc
      _ ≤ abelCumulative (scalarMomentAF M 2) R := by
        rw [abelCumulative, Nat.floor_natCast]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          exact Finset.mem_Icc.mpr ⟨Nat.zero_le r, (Finset.mem_Ico.mp hr).2.le⟩
        · intro r hr hnot
          exact hw r
      _ ≤ D₁ * T := hgrowth R (by exact_mod_cast hRone)
  have hsumprime : (∑ r ∈ Finset.Ico 1 R, if p ∣ r then scalarMomentAF M 2 r else 0) ≤
      (8 / (p : ℝ)) * D₂ * T := by
    calc
      _ ≤ ∑ r ∈ Finset.Ioc 0 R, if p ∣ r then scalarMomentAF M 2 r else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro r hr
          exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ico.mp hr).1, (Finset.mem_Ico.mp hr).2.le⟩
        · intro r hr hnot
          split_ifs
          · exact hw r
          · exact le_rfl
      _ ≤ _ := hmass R R p hRone le_rfl hp
  calc
    _ ≤ E * (D₁ * T) + U * ((8 / (p : ℝ)) * D₂ * T) := hbase.trans
      (add_le_add (mul_le_mul_of_nonneg_left hsum hE) (mul_le_mul_of_nonneg_left hsumprime hU))
    _ ≤ (D₁ + D₂) * T * (E + U * (8 / (p : ℝ))) := by
      calc
        _ ≤ E * (D₁ * T) + U * ((8 / (p : ℝ)) * D₂ * T) +
            (D₂ * T * E + D₁ * T * (U * (8 / (p : ℝ)))) :=
          le_add_of_nonneg_right (by positivity)
        _ = _ := by ring
    _ = _ := by dsimp only [E, U, T, δ]; ring

end Erdos964
