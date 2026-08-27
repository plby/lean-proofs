/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTMainConstantEuler

/-!
# The exact arithmetic coordinate recurrence

Integrating one coordinate replaces the denominator `g(p)` of each
remaining squarefree coordinate by `g(p) + 1`. The change in the
forbidden-modulus main constant cancels exactly with this replacement.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem primeFactor_not_dvd_of_coprime {M e p : ℕ} (hcop : M.Coprime e)
    (hp : p ∈ e.primeFactors) : ¬p ∣ M := by
  intro hpM
  have hpPrime := Nat.prime_of_mem_primeFactors hp
  have hpe := Nat.dvd_of_mem_primeFactors hp
  have hdvd := Nat.dvd_gcd hpM hpe
  rw [hcop.gcd_eq_one] at hdvd
  exact hpPrime.ne_one (Nat.dvd_one.mp hdvd)

theorem roughSieveWeight_apply_of_squarefree_coprime {M e : ℕ}
    (he : Squarefree e) (hcop : M.Coprime e) (g : ℕ → ℝ) :
    roughSieveWeight M g e = ∏ p ∈ e.primeFactors, 1 / g p := by
  rw [roughSieveWeight, squarefreePrimeWeight_apply_of_squarefree _ he]
  apply Finset.prod_congr rfl
  intro p hp
  rw [if_neg (primeFactor_not_dvd_of_coprime hcop hp)]

theorem modulusEulerMultiplier_mul_shiftedWeight {M e : ℕ}
    (he : Squarefree e) (hcop : M.Coprime e) (g : ℕ → ℝ)
    (hg : ∀ p ∈ e.primeFactors, 0 < g p) :
    modulusEulerMultiplier M e g * roughSieveWeight M (fun p => g p + 1) e =
      roughSieveWeight M g e := by
  rw [roughSieveWeight_apply_of_squarefree_coprime he hcop,
    roughSieveWeight_apply_of_squarefree_coprime he hcop, modulusEulerMultiplier,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [if_neg (primeFactor_not_dvd_of_coprime hcop hp)]
  have hgp := hg p hp
  have hgp1 : 0 < g p + 1 := by linarith
  field_simp [hgp.ne', hgp1.ne']

theorem sieveMainConstant_coordinate_recurrence {k M e : ℕ}
    (hk : 0 < k) (hM : 0 < M) (he : Squarefree e) (hcop : M.Coprime e)
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → (p : ℝ) / 2 ≤ g p)
    (hclose : ∀ p : ℕ, p.Prime → ¬p ∣ M → |g p - p| ≤ 2 * (k : ℝ)) :
    sieveMainConstant (M * e) g * roughSieveWeight M g e =
      sieveMainConstant M g * roughSieveWeight M (fun p => g p + 1) e := by
  have hgp : ∀ p ∈ e.primeFactors, 0 < g p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    exact (half_pos hp0).trans_le (hg p hpPrime (primeFactor_not_dvd_of_coprime hcop hp))
  have hconstant := sieveMainConstant_modulus_mul hk hM
    (Nat.pos_of_ne_zero he.ne_zero) hsmall g hg hclose
  have hweight := modulusEulerMultiplier_mul_shiftedWeight he hcop g hgp
  calc
    _ = sieveMainConstant (M * e) g *
        (modulusEulerMultiplier M e g * roughSieveWeight M (fun p => g p + 1) e) := by
      rw [hweight]
    _ = (modulusEulerMultiplier M e g * sieveMainConstant (M * e) g) *
        roughSieveWeight M (fun p => g p + 1) e := by ring
    _ = _ := by rw [← hconstant]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sieveMainConstant_coordinate_recurrence
