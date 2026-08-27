import ErdosProblems.Erdos587.EulerDensity
import ErdosProblems.Erdos587.HooleyTotientRatio

/-! # The exact Euler density and its one-log-log inverse bound -/

open scoped BigOperators

namespace Erdos587

lemma delta_primeSetUnitDensity_inv_eq (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (primeSetUnitDensity s)⁻¹ = (primeSetModulus s : ℝ) / (primeSetModulus s).totient := by
  let Q := primeSetModulus s
  have hQ : 0 < Q := Finset.prod_pos (fun p hp => (hs p hp).pos)
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hphi : (Q.totient : ℝ) =
      (Q : ℝ) * ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹) := by
    simpa using congrArg (Rat.castHom ℝ) (Nat.totient_eq_mul_prod_factors Q)
  have hfac : Q.primeFactors = s := primeFactors_primeSetModulus s hs
  rw [hfac] at hphi
  have hrho : primeSetUnitDensity s = (Q.totient : ℝ) / Q := by
    apply (eq_div_iff hQR).mpr
    simpa only [primeSetUnitDensity, mul_comm] using hphi.symm
  rw [hrho, inv_div]

theorem exists_delta_primeSetUnitDensity_inv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset ℕ), (∀ p ∈ s, p.Prime) →
      ∀ X : ℕ, primeSetModulus s ≤ X →
      (primeSetUnitDensity s)⁻¹ ≤ C * max 1 (Real.log (Real.log (X : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_delta_totient_ratio_bound
  refine ⟨C, hC, ?_⟩
  intro s hs X hX
  rw [delta_primeSetUnitDensity_inv_eq s hs]
  exact hbound X (primeSetModulus s) (Finset.prod_pos (fun p hp => (hs p hp).pos)) hX

end Erdos587
