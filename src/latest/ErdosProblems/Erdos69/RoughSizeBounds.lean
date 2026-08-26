import ErdosProblems.Erdos69.CompositeDilations
import ErdosProblems.Erdos69.ElementaryArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary size estimates for the rough composite dilations

These estimates use the elementary bound `primorial P ≤ 4^P`.
-/

open scoped BigOperators

namespace Erdos69.Elementary

theorem roughDilation_le (P j : ℕ) :
    roughDilation P j ≤ 2 * primorial P * (1 + j) := by
  have hv : 0 < primorial P * (1 + j) := Nat.mul_pos (primorial_pos P) (by omega)
  dsimp [roughDilation]
  nlinarith

theorem log_primorial_le (P : ℕ) :
    Real.log (primorial P : ℝ) ≤ (P : ℝ) * Real.log 4 := by
  have h : (primorial P : ℝ) ≤ (4 : ℝ) ^ P := by
    exact_mod_cast primorial_le_four_pow P
  have hlog := Real.log_le_log (by exact_mod_cast primorial_pos P) h
  simpa [Real.log_pow] using hlog

theorem log_roughDilation_le {P j : ℕ} (hP : 1 ≤ P) (hj : j ≤ P) :
    Real.log (roughDilation P j : ℝ) ≤ 5 * (P : ℝ) := by
  have hv : (0 : ℝ) < primorial P := by exact_mod_cast primorial_pos P
  have hjpos : (0 : ℝ) < 1 + (j : ℝ) := by positivity
  have hupper : (roughDilation P j : ℝ) ≤ 2 * (primorial P : ℝ) * (1 + (j : ℝ)) := by
    exact_mod_cast roughDilation_le P j
  have hlog := Real.log_le_log
    (by exact_mod_cast roughDilation_pos P j) hupper
  rw [Real.log_mul (mul_pos (by norm_num) hv).ne' hjpos.ne',
    Real.log_mul (by norm_num) hv.ne'] at hlog
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog4 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
  have hlogj := Real.log_le_sub_one_of_pos hjpos
  have hlogV := log_primorial_le P
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hjR : (j : ℝ) ≤ P := by exact_mod_cast hj
  nlinarith

theorem sum_log_primeFactors_subset_le {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : s ⊆ n.primeFactors) :
    ∑ p ∈ s, Real.log (p : ℝ) ≤ Real.log (n : ℝ) := by
  have hp (p : ℕ) (hps : p ∈ s) : p.Prime :=
    (Nat.mem_primeFactors.mp (hs hps)).1
  have hd : (∏ p ∈ s, p) ∣ n :=
    (Finset.prod_dvd_prod_of_subset s n.primeFactors id hs).trans
      (Nat.prod_primeFactors_dvd n)
  have hprodpos : 0 < ∏ p ∈ s, p := Finset.prod_pos (fun p hps ↦ (hp p hps).pos)
  have hle : ((∏ p ∈ s, p : ℕ) : ℝ) ≤ n := by
    exact_mod_cast Nat.le_of_dvd hn hd
  have hlog := Real.log_le_log (by exact_mod_cast hprodpos) hle
  rw [Nat.cast_prod, Real.log_prod (fun p hps ↦ by
    exact_mod_cast (hp p hps).ne_zero)] at hlog
  exact hlog

theorem card_primeFactors_subset_mul_log_le {n : ℕ} (hn : 0 < n)
    (s : Finset ℕ) (hs : s ⊆ n.primeFactors) {R : ℝ} (hR : 0 < R)
    (hlarge : ∀ p ∈ s, R ≤ (p : ℝ)) :
    (s.card : ℝ) * Real.log R ≤ Real.log (n : ℝ) := by
  calc
    (s.card : ℝ) * Real.log R = ∑ p ∈ s, Real.log R := by simp
    _ ≤ ∑ p ∈ s, Real.log (p : ℝ) :=
      Finset.sum_le_sum (fun p hp ↦ Real.log_le_log hR (hlarge p hp))
    _ ≤ Real.log (n : ℝ) := sum_log_primeFactors_subset_le hn s hs

theorem omegaCount_mul_log_two_le {n : ℕ} (hn : 0 < n) :
    (omegaCount n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) := by
  apply card_primeFactors_subset_mul_log_le hn n.primeFactors (by rfl) (by norm_num)
  intro p hp
  exact_mod_cast (Nat.mem_primeFactors.mp hp).1.two_le

theorem roughDilation_reciprocal_mass_le {P j : ℕ} (hP : 2 ≤ P) (hj : j ≤ P) :
    (∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / p) ≤
      5 / Real.log (P : ℝ) := by
  have hPR : (1 : ℝ) < P := by exact_mod_cast (show 1 < P by omega)
  have hPpos : (0 : ℝ) < P := by positivity
  have hlogpos : 0 < Real.log (P : ℝ) := Real.log_pos hPR
  have hlarge (p : ℕ) (hp : p ∈ (roughDilation P j).primeFactors) : (P : ℝ) ≤ p := by
    have hp' := Nat.mem_primeFactors.mp hp
    exact_mod_cast (prime_gt_of_dvd_roughDilation hp'.1 hp'.2.1).le
  have hcard := card_primeFactors_subset_mul_log_le (roughDilation_pos P j)
    (roughDilation P j).primeFactors (by rfl) hPpos hlarge
  have hsize := log_roughDilation_le (show 1 ≤ P by omega) hj
  calc
    (∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / p) ≤
        ∑ p ∈ (roughDilation P j).primeFactors, (1 : ℝ) / P := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le hPpos (hlarge p hp)
    _ = ((roughDilation P j).primeFactors.card : ℝ) / P := by simp [div_eq_mul_inv]
    _ ≤ 5 / Real.log (P : ℝ) := by
      rw [div_le_div_iff₀ hPpos hlogpos]
      exact hcard.trans hsize

end Erdos69.Elementary
