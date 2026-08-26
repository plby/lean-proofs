import ErdosProblems.Erdos67b.MRGSTwoBlockA8Scalar

/-!
# Bounded Mertens allowances in the masked GS Euler estimate

The source half-mass and eighth-distance conditions may hold with a
fixed additive allowance. Increasing the retained mass by eight times
that allowance preserves the logarithmic exponent of the GS error.
-/

namespace Erdos67b

open MRHalaszBands

noncomputable section

theorem mrGS_deletedMass_add_sqrt_le_with_allowance
    {B C D K : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hhalf : B ≤ (B + C) / 2 + K) (heighth : D ≤ (B + C) / 8 + K) :
    B + Real.sqrt (2 * D * C) ≤ (7 / 8 : ℝ) * (B + C) + 7 * K := by
  have hbase := deletedMass_add_sqrt_le_seven_eighths hB
    (show 0 ≤ C + 8 * K by positivity) hD (by linarith) (by linarith)
  calc
    _ ≤ B + Real.sqrt (2 * D * (C + 8 * K)) := by
      gcongr
      linarith
    _ ≤ (7 / 8 : ℝ) * (B + (C + 8 * K)) := hbase
    _ = _ := by ring

theorem mrGS_maskedEulerExponent_le_with_allowance
    {f : ℕ → ℂ} (hbound : ∀ n, ‖f n‖ ≤ 1)
    (Q : ℕ → Prop) [DecidablePred Q] (t : ℝ) (N : ℕ)
    {K : ℝ} (hK : 0 ≤ K)
    (hmass : primeBandReciprocalMass Q N ≤ PrimeEstimates.primeReciprocals N / 2 + K)
    (hdist : pretentiousDistSq f (archimedeanTwist t) N ≤
      PrimeEstimates.primeReciprocals N / 8 + K) :
    gsEulerExponent (archimedeanUntwist (gsDeletePrimeBand f Q) t) N ≤
      (7 / 8 : ℝ) * PrimeEstimates.primeReciprocals N + 7 * K + 8 := by
  have hsum := primeBandReciprocalMass_add_compl Q N
  have hB : 0 ≤ primeBandReciprocalMass Q N := by
    unfold primeBandReciprocalMass
    positivity
  have hC : 0 ≤ primeBandReciprocalMass (fun p ↦ ¬Q p) N := by
    unfold primeBandReciprocalMass
    positivity
  have hD : 0 ≤ pretentiousDistSq f (archimedeanTwist t) N :=
    pretentiousDistSq_nonneg (fun p _ ↦ hbound p)
      (fun p hp ↦ (norm_archimedeanTwist hp.pos t).le)
  have hscalar := mrGS_deletedMass_add_sqrt_le_with_allowance hB hC hD hK
    (by simpa only [hsum] using hmass) (by simpa only [hsum] using hdist)
  rw [hsum] at hscalar
  exact (gsEulerExponent_archimedeanUntwist_deletePrimeBand_le hbound Q t N).trans
    (add_le_add hscalar le_rfl)

theorem mrGS_linearError_le_log_rpow_of_euler_bound
    (a : ℕ → ℂ) (u : ℝ) {N : ℕ} (hN : 2 ≤ N) {K : ℝ}
    (hEuler : gsEulerExponent a N ≤ (7 / 8 : ℝ) * Real.log (Real.log (N : ℝ)) + K) :
    gsPrefixRenormalizationLinearError a u N ≤
      (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) * Real.exp K) *
        (1 + |u|) * (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hC : 0 ≤ HalberstamScratch.explicitMassConstant 2 1 + 1 :=
    add_nonneg (HalberstamScratch.explicitMassConstant_nonneg (by norm_num) (by norm_num))
      zero_le_one
  have hexp : Real.exp (gsEulerExponent a N) ≤
      Real.exp K * (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) := by
    apply (Real.exp_le_exp.mpr hEuler).trans_eq
    rw [Real.rpow_def_of_pos hL, ← Real.exp_add]
    congr 1
    ring
  have hpowers : (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) / Real.log (N : ℝ) =
      (Real.log (N : ℝ)) ^ (-1 / 8 : ℝ) := by
    calc
      _ = (Real.log (N : ℝ)) ^ (7 / 8 : ℝ) / (Real.log (N : ℝ)) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (Real.log (N : ℝ)) ^ ((7 / 8 : ℝ) - 1) := (Real.rpow_sub hL _ _).symm
      _ = _ := by norm_num
  unfold gsPrefixRenormalizationLinearError
  calc
    _ ≤ 10 * (1 + |u|) * (HalberstamScratch.explicitMassConstant 2 1 + 1) /
        Real.log (N : ℝ) * (Real.exp K * (Real.log (N : ℝ)) ^ (7 / 8 : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (10 * (HalberstamScratch.explicitMassConstant 2 1 + 1) * Real.exp K) *
        (1 + |u|) * ((Real.log (N : ℝ)) ^ (7 / 8 : ℝ) / Real.log (N : ℝ)) := by ring
    _ = _ := by rw [hpowers]

end

end Erdos67b
