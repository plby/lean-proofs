import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Composition of two finite mean-square estimates

This is the finite analytic step in the target-averaging route. The estimates
for actual primitive characters over primes are separate obligations; this
module does not assume them as axioms or assert that they have been proved.
-/

open scoped BigOperators

namespace Erdos4.DoubleMeanSquare

variable {I P Q : Type*} [Fintype I] [Fintype P] [Fintype Q]

/-- A diagonal multiplier between two mean-square bounded finite transforms. -/
theorem sum_norm_sq_composition_le
    (source : I → P → ℂ) (target : I → Q → ℂ)
    (A B gamma : ℝ) (hB : 0 ≤ B) (hgamma : 0 ≤ gamma)
    (hsource : ∀ a : P → ℂ,
      (∑ i, ‖∑ p, a p * source i p‖ ^ 2) ≤ A * ∑ p, ‖a p‖ ^ 2)
    (htarget : ∀ b : I → ℂ,
      (∑ q, ‖∑ i, b i * target i q‖ ^ 2) ≤ B * ∑ i, ‖b i‖ ^ 2)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ gamma) (a : P → ℂ) :
    (∑ q, ‖∑ i, (c i * ∑ p, a p * source i p) * target i q‖ ^ 2) ≤
      B * gamma ^ 2 * (A * ∑ p, ‖a p‖ ^ 2) := by
  have hdiag : (∑ i, ‖c i * ∑ p, a p * source i p‖ ^ 2) ≤
      gamma ^ 2 * ∑ i, ‖∑ p, a p * source i p‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    rw [norm_mul, mul_pow]
    have hsq : ‖c i‖ ^ 2 ≤ gamma ^ 2 := by nlinarith [norm_nonneg (c i), hc i]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  calc
    (∑ q, ‖∑ i, (c i * ∑ p, a p * source i p) * target i q‖ ^ 2) ≤
        B * ∑ i, ‖c i * ∑ p, a p * source i p‖ ^ 2 :=
      htarget (fun i => c i * ∑ p, a p * source i p)
    _ ≤ B * (gamma ^ 2 * ∑ i, ‖∑ p, a p * source i p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hdiag hB
    _ ≤ B * (gamma ^ 2 * (A * ∑ p, ‖a p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hsource a) (sq_nonneg gamma)) hB
    _ = B * gamma ^ 2 * (A * ∑ p, ‖a p‖ ^ 2) := by ring

/-- Specialization to the unweighted sum over source primes (the type `P`
will be the finite source-prime set). -/
theorem sum_norm_sq_source_average_le
    (source : I → P → ℂ) (target : I → Q → ℂ)
    (A B gamma : ℝ) (hB : 0 ≤ B) (hgamma : 0 ≤ gamma)
    (hsource : ∀ a : P → ℂ,
      (∑ i, ‖∑ p, a p * source i p‖ ^ 2) ≤ A * ∑ p, ‖a p‖ ^ 2)
    (htarget : ∀ b : I → ℂ,
      (∑ q, ‖∑ i, b i * target i q‖ ^ 2) ≤ B * ∑ i, ‖b i‖ ^ 2)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ gamma) :
    (∑ q, ‖∑ i, (c i * ∑ p, source i p) * target i q‖ ^ 2) ≤
      B * gamma ^ 2 * (A * Fintype.card P) := by
  simpa only [one_mul, norm_one, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using
    sum_norm_sq_composition_le source target A B gamma hB hgamma hsource htarget c hc
      (fun _ => 1)

/-- The exact finite exceptional-set bound, with its threshold visible. -/
theorem large_values_card_le (f : Q → ℂ) {delta V : ℝ} (hdelta : 0 < delta)
    (hV : (∑ q, ‖f q‖ ^ 2) ≤ V) :
    ((Finset.univ.filter (fun q => delta < ‖f q‖)).card : ℝ) ≤ V / delta ^ 2 := by
  classical
  let bad := Finset.univ.filter (fun q => delta < ‖f q‖)
  have hbad : (bad.card : ℝ) * delta ^ 2 ≤ ∑ q ∈ bad, ‖f q‖ ^ 2 := by
    calc
      (bad.card : ℝ) * delta ^ 2 = ∑ _q ∈ bad, delta ^ 2 := by simp
      _ ≤ ∑ q ∈ bad, ‖f q‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hh : delta < ‖f q‖ := (Finset.mem_filter.mp hq).2
        nlinarith [norm_nonneg (f q)]
  have htotal : (∑ q ∈ bad, ‖f q‖ ^ 2) ≤ ∑ q, ‖f q‖ ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun q _hq _hnot => sq_nonneg _)
  exact (le_div_iff₀ (sq_pos_of_pos hdelta)).mpr (hbad.trans (htotal.trans hV))

/-- Combining both transforms and Chebyshev's inequality. -/
theorem exceptional_targets_card_le
    (source : I → P → ℂ) (target : I → Q → ℂ)
    (A B gamma delta : ℝ) (hB : 0 ≤ B) (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hsource : ∀ a : P → ℂ,
      (∑ i, ‖∑ p, a p * source i p‖ ^ 2) ≤ A * ∑ p, ‖a p‖ ^ 2)
    (htarget : ∀ b : I → ℂ,
      (∑ q, ‖∑ i, b i * target i q‖ ^ 2) ≤ B * ∑ i, ‖b i‖ ^ 2)
    (c : I → ℂ) (hc : ∀ i, ‖c i‖ ≤ gamma) :
    ((Finset.univ.filter (fun q =>
      delta < ‖∑ i, (c i * ∑ p, source i p) * target i q‖)).card : ℝ) ≤
      (B * gamma ^ 2 * (A * Fintype.card P)) / delta ^ 2 := by
  exact large_values_card_le _ hdelta
    (sum_norm_sq_source_average_le source target A B gamma hB hgamma hsource htarget c hc)

end Erdos4.DoubleMeanSquare
