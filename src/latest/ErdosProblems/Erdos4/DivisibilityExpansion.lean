import ErdosProblems.Erdos4.LocalIndicatorExpansion
import ErdosProblems.Erdos4.CutoffMass
import ErdosProblems.Erdos4.AffineWeights

/-!
# The actual divisor expansion and its total absolute coefficient mass

Factoring the divisor normalization into the local basis gives an exact
expansion in products of residue indicators. The row bounds and the
quadratic cutoff-mass estimate control the entire expansion without
counting divisor tuples.
-/

open scoped BigOperators

namespace Erdos4.DivisibilityExpansion

open DivisorCoefficients LocalOrthogonality LocalIndicatorExpansion

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

noncomputable def cutoffProfile (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) : ℝ :=
  if totalDivisor ell a ≤ R then profileProduct m R ell a else 0

theorem cutoffProfile_nonneg {m : ℝ} (hm : 0 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (a : P → Option (Fin k)) : 0 ≤ cutoffProfile m R ell a := by
  unfold cutoffProfile
  split_ifs
  · exact profileProduct_nonneg hm hR ell a
  · exact le_rfl

theorem profileProduct_le_one {m : ℝ} (hm : 1 ≤ m) (R : ℕ)
    (ell : P → ℕ) (a : P → Option (Fin k)) : profileProduct m R ell a ≤ 1 := by
  unfold profileProduct
  apply Finset.prod_le_one
  · intro i _hi
    exact (PrimitiveProfile.profile_pos (by linarith) (Nat.cast_nonneg k)
      (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))).le
  · intro i _hi
    exact PrimitiveProfile.profile_le_one hm (Nat.cast_nonneg k)
      (div_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))

theorem coefficient_factor (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (a : P → Option (Fin k)) :
    coefficient m R ell a = cutoffProfile m R ell a * normalization ell a := by
  unfold coefficient cutoffProfile
  split_ifs <;> simp

noncomputable def divisorCoefficient (m : ℝ) (R : ℕ) (ell : P → ℕ)
    (b : P → Option (Fin k)) : ℝ :=
  ∑ a : P → Option (Fin k), cutoffProfile m R ell a * ∏ p, transition (ell p) (a p) (b p)

noncomputable def evaluation (s b : P → Option (Fin k)) : ℝ :=
  ∏ p, indicator (s p) (b p)

theorem evaluation_nonneg (s b : P → Option (Fin k)) : 0 ≤ evaluation s b :=
  Finset.prod_nonneg (fun p _hp => indicator_nonneg (s p) (b p))

theorem evaluation_le_one (s b : P → Option (Fin k)) : evaluation s b ≤ 1 :=
  Finset.prod_le_one (fun p _hp => indicator_nonneg (s p) (b p))
    (fun p _hp => indicator_le_one (s p) (b p))

theorem expansion_eq (m : ℝ) (R : ℕ) (ell : P → ℕ) (s : P → Option (Fin k)) :
    (∑ b, divisorCoefficient m R ell b * evaluation s b) =
      ∑ a, coefficient m R ell a * ∏ p, extendedBasis (ell p : ℝ) (a p) (s p) := by
  unfold divisorCoefficient evaluation
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b : P → Option (Fin k),
        (cutoffProfile m R ell a * ∏ p, transition (ell p) (a p) (b p)) *
          ∏ p, indicator (s p) (b p)) =
        cutoffProfile m R ell a * ∑ b : P → Option (Fin k),
          ∏ p, transition (ell p) (a p) (b p) * indicator (s p) (b p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Finset.prod_mul_distrib]
      ring
    _ = cutoffProfile m R ell a * ∏ p, localWeight (ell p) (a p) *
        extendedBasis (ell p : ℝ) (a p) (s p) := by
      rw [← Fintype.prod_sum (fun p (b : Option (Fin k)) =>
        transition (ell p) (a p) b * indicator (s p) b)]
      simp only [local_expansion]
    _ = _ := by
      rw [Finset.prod_mul_distrib, coefficient_factor]
      unfold normalization
      ring

theorem sum_abs_coefficient_le_mass {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) :
    (∑ b : P → Option (Fin k), |divisorCoefficient m R ell b|) ≤
      CutoffMass.mass (k := k) R ell (rowCost k) := by
  have hq : ∀ a : P → Option (Fin k), 0 ≤ cutoffProfile m R ell a :=
    cutoffProfile_nonneg (by linarith) hR ell
  have hpoint : ∀ a : P → Option (Fin k),
      cutoffProfile m R ell a * (∏ p, ∑ b : Option (Fin k), |transition (ell p) (a p) b|) ≤
        if totalDivisor ell a ≤ R then CutoffMass.labelCost (rowCost k) a else 0 := by
    intro a
    have hprod : (∏ p, ∑ b : Option (Fin k), |transition (ell p) (a p) b|) ≤
        CutoffMass.labelCost (rowCost k) a := by
      apply Finset.prod_le_prod
      · intro p _hp
        exact Finset.sum_nonneg (fun b _hb => abs_nonneg _)
      · intro p _hp
        exact row_bound (hell p) (a p)
    by_cases ha : totalDivisor ell a ≤ R
    · rw [cutoffProfile, if_pos ha, if_pos ha]
      have hh := mul_le_mul (profileProduct_le_one hm R ell a) hprod
        (Finset.prod_nonneg (fun p _hp => Finset.sum_nonneg (fun b _hb => abs_nonneg _))) zero_le_one
      simpa only [one_mul] using hh
    · simp [cutoffProfile, ha]
  calc
    _ ≤ ∑ b : P → Option (Fin k), ∑ a : P → Option (Fin k),
        cutoffProfile m R ell a * ∏ p, |transition (ell p) (a p) (b p)| := by
      apply Finset.sum_le_sum
      intro b _hb
      have hh := Finset.abs_sum_le_sum_abs
        (fun a : P → Option (Fin k) => cutoffProfile m R ell a *
          ∏ p, transition (ell p) (a p) (b p)) Finset.univ
      simpa only [divisorCoefficient, abs_mul, abs_of_nonneg (hq _), Finset.abs_prod] using hh
    _ = ∑ a : P → Option (Fin k), cutoffProfile m R ell a *
        ∏ p, ∑ b : Option (Fin k), |transition (ell p) (a p) b| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [← Finset.mul_sum,
        ← Fintype.prod_sum (fun p (b : Option (Fin k)) => |transition (ell p) (a p) b|)]
    _ ≤ _ := Finset.sum_le_sum (fun a _ha => hpoint a)

theorem sum_abs_coefficient_le {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) :
    (∑ b : P → Option (Fin k), |divisorCoefficient m R ell b|) ≤
      (R : ℝ) ^ 2 * Real.exp ((k : ℝ) * rowCost k * ∑ p, 1 / (ell p : ℝ) ^ 2) :=
  (sum_abs_coefficient_le_mass hm hR ell hell).trans
    (CutoffMass.mass_le R ell (fun p => by have := hell p; omega) (rowCost_nonneg k))

theorem amplitude_abs_le_mass {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) (hell : ∀ p, k + 2 ≤ ell p) (s : P → Option (Fin k)) :
    |∑ a, coefficient m R ell a * ∏ p, extendedBasis (ell p : ℝ) (a p) (s p)| ≤
      CutoffMass.mass (k := k) R ell (rowCost k) := by
  rw [← expansion_eq]
  calc
    _ ≤ ∑ b : P → Option (Fin k), |divisorCoefficient m R ell b * evaluation s b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : P → Option (Fin k), |divisorCoefficient m R ell b| := by
      apply Finset.sum_le_sum
      intro b _hb
      rw [abs_mul, abs_of_nonneg (evaluation_nonneg s b)]
      exact mul_le_of_le_one_right (abs_nonneg _) (evaluation_le_one s b)
    _ ≤ _ := sum_abs_coefficient_le_mass hm hR ell hell

theorem weight_le_of_small_tail {m : ℝ} (hm : 1 ≤ m) {R : ℕ} (hR : 2 ≤ R)
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime] (hell : ∀ l, k + 2 ≤ ell l)
    (htail : (k : ℝ) * rowCost k * ∑ l, 1 / (ell l : ℝ) ^ 2 ≤ 1)
    (Y W : ℕ) (h : Fin k → ℕ) (p n : ℕ) :
    AffineWeights.weight ell m R Y W h p n ≤ Real.exp 1 ^ 2 * (R : ℝ) ^ 4 := by
  have hmass := CutoffMass.mass_le_of_small_tail R ell
    (fun l => by have := hell l; omega) (rowCost_nonneg k) htail
  have habs : |AffineWeights.amplitude ell m R h p n| ≤ Real.exp 1 * (R : ℝ) ^ 2 :=
    (amplitude_abs_le_mass hm hR ell hell (AffineWeights.residueState ell h n p)).trans hmass
  have hsq := (sq_le_sq₀ (abs_nonneg (AffineWeights.amplitude ell m R h p n))
    (mul_nonneg (Real.exp_pos 1).le (sq_nonneg (R : ℝ)))).mpr habs
  rw [sq_abs, mul_pow, ← pow_mul] at hsq
  unfold AffineWeights.weight
  split_ifs
  · exact hsq
  · positivity

end Erdos4.DivisibilityExpansion
