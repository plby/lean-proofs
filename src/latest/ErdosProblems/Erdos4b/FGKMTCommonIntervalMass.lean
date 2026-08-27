/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPreSieveResidues
import ErdosProblems.Erdos4b.FGKMTCommonResidueMass

/-!
# Physical common-weight mass with the complete presieve indicator

Summing the disjoint allowed presieve classes keeps the original
coprimality condition. Their main densities add, and their endpoint
errors cost at most `W` times the uniform squared coefficient bound.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

open scoped Classical in
def commonPreSieveIntervalMass (k W R : ℕ) (p : α → ℕ) (a : Fin k → ℤ)
    (A B : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ico A B, if preSieveCondition W a n then
    commonDivisorWeight k R p (fun i => n + a i) else 0

theorem commonPreSieveIntervalMass_eq_residue_sum {W : ℕ} (hW : 0 < W)
    (k R : ℕ) (p : α → ℕ) (a : Fin k → ℤ) (A B : ℤ) :
    commonPreSieveIntervalMass k W R p a A B =
      ∑ v ∈ preSieveResidues W a, commonResidueIntervalMass k R p a W v A B := by
  unfold commonPreSieveIntervalMass commonResidueIntervalMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  exact (sum_preSieve_residue_indicator hW a n _).symm

theorem commonPreSieveIntervalMass_quadratic_error {k R W : ℕ}
    (hk : 2 ≤ k) (hR : 1 < R) (hW : 0 < W) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hlarge : ∀ q, 2 * k ^ 2 < p q) (hcop : ∀ q, (p q).Coprime W)
    (a : Fin k → ℤ) (hroot : ∀ q i j, (p q : ℤ) ∣ a i - a j → i = j)
    (A B : ℤ) (hAB : A ≤ B) :
    |commonPreSieveIntervalMass k W R p a A B -
      (((preSieveResidues W a).card : ℝ) * ((B : ℝ) - A) / W) *
        finiteSieveQuadratic (fun q => (p q : ℝ)) (commonSieveCoefficient k R p)| ≤
      (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) := by
  rw [commonPreSieveIntervalMass_eq_residue_sum hW]
  let Q := finiteSieveQuadratic (fun q => (p q : ℝ)) (commonSieveCoefficient k R p)
  let L := ((B : ℝ) - A) / W * Q
  have hid :
      (∑ v ∈ preSieveResidues W a, commonResidueIntervalMass k R p a W v A B) -
        (((preSieveResidues W a).card : ℝ) * ((B : ℝ) - A) / W) * Q =
      ∑ v ∈ preSieveResidues W a, (commonResidueIntervalMass k R p a W v A B - L) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    dsimp only [L]
    ring
  change |(∑ v ∈ preSieveResidues W a, commonResidueIntervalMass k R p a W v A B) -
    (((preSieveResidues W a).card : ℝ) * ((B : ℝ) - A) / W) * Q| ≤ _
  rw [hid]
  calc
    _ ≤ ∑ v ∈ preSieveResidues W a,
        |commonResidueIntervalMass k R p a W v A B - L| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ preSieveResidues W a,
        (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) :=
      Finset.sum_le_sum fun v _ => commonResidueIntervalMass_error hk hR hW hp hinj
        hlarge hcop a hroot v A B hAB
    _ ≤ _ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast card_preSieveResidues_le W a
      · positivity

omit [DecidableEq α] [Fintype α] in
theorem commonPrimePreSieveIntervalMass_quadratic_error {k W M R P : ℕ}
    (hk : 2 ≤ k) (hR : 1 < R) (hW : 0 < W) (hWM : W ∣ M)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M)
    (hP : P.Prime) (hRP : R < P) (h : Fin k → ℕ) (hinj : Function.Injective h)
    (hshift : ∀ i, h i < 2 * k ^ 2) (A B : ℤ) (hAB : A ≤ B) :
    |commonPreSieveIntervalMass k W R (fun q : commonPrimeUniverse M R => q.val)
      (fun i => (h i : ℤ) * P) A B -
        (((preSieveResidues W (fun i => (h i : ℤ) * P)).card : ℝ) * ((B : ℝ) - A) / W) *
          commonSieveQuadratic k M R| ≤
      (W : ℝ) * ((R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k)) := by
  exact commonPreSieveIntervalMass_quadratic_error hk hR hW commonPrimeUniverse_prime
    Subtype.val_injective (commonPrimeUniverse_large hsmall)
    (fun q => (commonPrimeUniverse_prime q).coprime_iff_not_dvd.mpr
      (fun hh => commonPrimeUniverse_not_dvd q (hh.trans hWM))) _
    (fun q _ _ hh => commonPrimeUniverse_shift_roots_distinct hsmall hP hRP h hinj hshift q hh)
    A B hAB

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimePreSieveIntervalMass_quadratic_error
