/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentIntervalCount
import ErdosProblems.Erdos4b.FGKMTQuadraticCountError
import ErdosProblems.Erdos4b.FGKMTCommonMainTerm

/-!
# Physical common-weight mass in one presieve residue class

The finite expansion and the actual CRT count identify the main term
with the already checked arithmetic quadratic. The complete endpoint
error is bounded by the uniform squared coefficient norm.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

def commonResidueIntervalMass (k R : ℕ) (p : α → ℕ) (a : Fin k → ℤ)
    (W : ℕ) (v A B : ℤ) : ℝ :=
  ∑ n ∈ Finset.Ico A B, if n ≡ v [ZMOD W] then
    commonDivisorWeight k R p (fun i => n + a i) else 0

theorem commonResidueIntervalMass_eq_quadratic (k R : ℕ) (p : α → ℕ)
    (a : Fin k → ℤ) (W : ℕ) (v A B : ℤ) :
    commonResidueIntervalMass k R p a W v A B =
      ∑ d : α → Option (Fin k), ∑ e : α → Option (Fin k),
        commonSieveCoefficient k R p d * commonSieveCoefficient k R p e *
          assignmentPairIntervalCount p a d e W v A B := by
  classical
  let T := fun (n : ℤ) (d e : α → Option (Fin k)) =>
    if n ≡ v [ZMOD W] ∧
      ((∀ i, (assignmentPrimeTuple p d i : ℤ) ∣ n + a i) ∧
        (∀ i, (assignmentPrimeTuple p e i : ℤ) ∣ n + a i)) then
      commonSieveCoefficient k R p d * commonSieveCoefficient k R p e else 0
  have hterm (n : ℤ) :
      (if n ≡ v [ZMOD W] then commonDivisorWeight k R p (fun i => n + a i) else 0) =
        ∑ d, ∑ e, T n d e := by
    rw [commonDivisorWeight_eq_quadratic]
    by_cases hn : n ≡ v [ZMOD W]
    · simp only [T, hn, true_and, if_true]
    · simp only [T, hn, false_and, if_false, Finset.sum_const_zero]
  calc
    _ = ∑ n ∈ Finset.Ico A B, ∑ d, ∑ e, T n d e := by
      simp only [commonResidueIntervalMass, hterm]
    _ = ∑ d, ∑ e, ∑ n ∈ Finset.Ico A B, T n d e := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      dsimp only [T, assignmentPairIntervalCount]
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring

theorem commonResidueIntervalMass_error {k R W : ℕ} (hk : 2 ≤ k) (hR : 1 < R)
    (hW : 0 < W) {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (hlarge : ∀ q, 2 * k ^ 2 < p q) (hcop : ∀ q, (p q).Coprime W)
    (a : Fin k → ℤ) (hroot : ∀ q i j, (p q : ℤ) ∣ a i - a j → i = j)
    (v A B : ℤ) (hAB : A ≤ B) :
    |commonResidueIntervalMass k R p a W v A B -
      ((B : ℝ) - A) / W * finiteSieveQuadratic (fun q => (p q : ℝ))
        (commonSieveCoefficient k R p)| ≤ (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) := by
  rw [commonResidueIntervalMass_eq_quadratic, finiteSieveQuadratic]
  have herr := quadratic_count_error (commonSieveCoefficient k R p)
    (fun d e => assignmentPairIntervalCount p a d e W v A B)
    (assignmentCrtKernel (fun q => (p q : ℝ))) (((B : ℝ) - A) / W) 1
    (fun d e => assignmentPairIntervalCount_error hW hp hinj hcop a hroot d e v A B hAB)
  rw [one_mul] at herr
  exact herr.trans (commonSieveCoefficient_l1_sq_le hk hp hinj hlarge hR)

omit [DecidableEq α] [Fintype α] in
theorem commonPrimeResidueIntervalMass_error {k W M R P : ℕ}
    (hk : 2 ≤ k) (hR : 1 < R) (hW : 0 < W) (hWM : W ∣ M)
    (hsmall : ∀ q : ℕ, q.Prime → q ≤ 2 * k ^ 2 → q ∣ M)
    (hP : P.Prime) (hRP : R < P) (h : Fin k → ℕ) (hinj : Function.Injective h)
    (hshift : ∀ i, h i < 2 * k ^ 2) (v A B : ℤ) (hAB : A ≤ B) :
    |commonResidueIntervalMass k R (fun q : commonPrimeUniverse M R => q.val)
      (fun i => (h i : ℤ) * P) W v A B -
        ((B : ℝ) - A) / W * commonSieveQuadratic k M R| ≤
      (R : ℝ) ^ 3 * (1 + Real.log R) ^ (2 * k) := by
  exact commonResidueIntervalMass_error hk hR hW commonPrimeUniverse_prime
    Subtype.val_injective (commonPrimeUniverse_large hsmall)
    (fun q => (commonPrimeUniverse_prime q).coprime_iff_not_dvd.mpr
      (fun hh => commonPrimeUniverse_not_dvd q (hh.trans hWM))) _
    (fun q _ _ hh => commonPrimeUniverse_shift_roots_distinct hsmall hP hRP h hinj hshift q hh)
    v A B hAB

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.commonPrimeResidueIntervalMass_error
