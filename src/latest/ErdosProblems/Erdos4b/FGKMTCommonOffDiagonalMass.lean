/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMovedPrimeMass

/-!
# Off-diagonal error after the moved-prime sums are bounded

All combinatorial multiplicities and moved-prime masses are discharged.
Only the genuine arithmetic sum of the reduced profile majorant remains.
The extra linear dimension factor is harmless for the final envelope.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem absoluteAssignmentMajorantSum_nonneg {α : Type*} [DecidableEq α] [Fintype α]
    (k R : ℕ) {p : α → ℕ} (hp : ∀ q, 0 < p q) :
    0 ≤ absoluteAssignmentMajorantSum k R p :=
  Finset.sum_nonneg fun r _hr => mul_nonneg (sq_nonneg _) (commonKernelWeight_nonneg k hp r)

theorem exists_commonSieveCoefficient_offDiagonal_mass_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : Type*) [DecidableEq α] [Fintype α],
      ∀ {k : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      ∀ (R : ℕ) (p : α → ℕ), Function.Injective p → (∀ q, 2 * k ^ 2 < p q) →
        |finiteSieveQuadratic (fun q => (p q : ℝ)) (commonSieveCoefficient k R p) -
          ∑ r, primeAssignmentProfile k R p r ^ 2 / assignmentRowWeight (fun q => (p q : ℝ)) r| ≤
          (C * k * sieveProfileScale k / Real.log R) * absoluteAssignmentMajorantSum k R p := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_commonSieveCoefficient_offDiagonal_bound
  let C := 16 * Real.exp 4 * C₀
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro α _ _ k hk hlog R p hinj hrough
  have hk0 : 0 < k := by omega
  have hpk : ∀ q, k < p q := by
    intro q
    have h := hrough q
    nlinarith
  have hp0 : ∀ q, 0 < p q := fun q => hk0.trans (hpk q)
  have hmajorant := absoluteAssignmentMajorantSum_nonneg k R hp0
  have hfactor : 0 ≤ (C₀ * sieveProfileScale k / Real.log R) *
      absoluteAssignmentMajorantSum k R p :=
    mul_nonneg (div_nonneg (mul_nonneg hC₀.le
      (zero_le_one.trans (profile_scales_bounds hk0 hlog).1)) (Real.log_natCast_nonneg _)) hmajorant
  have hmass :
      Real.exp (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2) *
        (∑ q, (k : ℝ) ^ 2 / ((p q : ℝ) - k) ^ 2 * Real.log (p q)) ≤
      Real.exp 4 * (16 * k) :=
    mul_le_mul (Real.exp_le_exp.mpr (movedPrimeMass_le_four hk hinj hrough))
      (movedPrimeLogMass_le hk hinj hrough)
      (Finset.sum_nonneg fun q _hq => mul_nonneg
        (div_nonneg (sq_nonneg _) (sq_nonneg _)) (Real.log_natCast_nonneg _)) (Real.exp_pos 4).le
  refine (hbound α hk0 hlog R p hpk).trans ?_
  calc
    _ ≤ ((C₀ * sieveProfileScale k / Real.log R) * absoluteAssignmentMajorantSum k R p) *
        (Real.exp 4 * (16 * k)) := mul_le_mul_of_nonneg_left hmass hfactor
    _ = _ := by dsimp only [C]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonSieveCoefficient_offDiagonal_mass_bound
