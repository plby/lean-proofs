import ErdosProblems.Erdos587.HooleyMoments

/-!
# Reflection symmetry of divisor moments

The involution `d ↦ n / d` reflects the divisor window. Because it exchanges
the open and closed endpoints, its local-count identity holds almost
everywhere, which is precisely what is needed for integral moments.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos587

lemma log_divisor_quotient {n d : ℕ} (hd : d ∈ n.divisors) :
    Real.log (n / d : ℕ) = Real.log n - Real.log d := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.mem_divisors.mp hd).2
  rw [Nat.cast_div (Nat.mem_divisors.mp hd).1 hdpos.ne', Real.log_div hn hdpos.ne']

lemma divisor_indicator_reflection {n d : ℕ} (hd : d ∈ n.divisors) (u : ℝ) :
    (Set.Ico (Real.log d - 1) (Real.log d)).indicator (fun _ : ℝ => (1 : ℝ))
        (Real.log n - u - 1) =
      (Set.Ioc (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
        (fun _ : ℝ => (1 : ℝ)) u := by
  rw [log_divisor_quotient hd]
  have hmem : Real.log n - u - 1 ∈ Set.Ico (Real.log d - 1) (Real.log d) ↔
      u ∈ Set.Ioc (Real.log n - Real.log d - 1) (Real.log n - Real.log d) := by
    simp only [Set.mem_Ico, Set.mem_Ioc]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  simp only [Set.indicator_apply, hmem]

/-- Reflection reverses the window endpoints; the resulting discrepancy
is confined to a finite, hence null, set. -/
theorem deltaCount_reflection_ae (n : ℕ) :
    (fun u : ℝ => deltaCount n (Real.log n - u - 1)) =ᵐ[volume] deltaCount n := by
  have hpoint (d : ℕ) :
      (Set.Ioc (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) =ᵐ[volume]
        (Set.Ico (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) :=
    indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Ioc.symm
  have hall : ∀ᵐ u : ℝ, ∀ d ∈ n.divisors,
      (Set.Ioc (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) u =
        (Set.Ico (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) u := by
    rw [Filter.eventually_all_finset]
    exact fun d _ => hpoint d
  filter_upwards [hall] with u hu
  rw [deltaCount_eq_sum_indicator, deltaCount_eq_sum_indicator]
  calc
    _ = ∑ d ∈ n.divisors,
        (Set.Ico (Real.log (n / d : ℕ) - 1) (Real.log (n / d : ℕ))).indicator
          (fun _ : ℝ => (1 : ℝ)) u := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [divisor_indicator_reflection hd, hu d hd]
    _ = _ := Nat.sum_div_divisors n
      (fun d => (Set.Ico (Real.log d - 1) (Real.log d)).indicator
        (fun _ : ℝ => (1 : ℝ)) u)

/-- Swapping the exponents of a mixed moment does not change it. -/
theorem deltaMixedMoment_symm (n a b : ℕ) (t : ℝ) :
    deltaMixedMoment n a b t = deltaMixedMoment n b a t := by
  have href := deltaCount_reflection_ae n
  have hshift := href.comp_tendsto
    (measurePreserving_sub_right volume t).quasiMeasurePreserving.tendsto_ae
  calc
    deltaMixedMoment n a b t = ∫ u : ℝ,
        deltaCount n (Real.log n - u - 1) ^ a *
          deltaCount n (Real.log n - (u - t) - 1) ^ b := by
      apply integral_congr_ae
      filter_upwards [href, hshift] with u hu hsu
      dsimp only [Function.comp_def] at hu hsu ⊢
      rw [hu, hsu]
    _ = ∫ u : ℝ,
        deltaCount n ((Real.log n - 1 + t - u) - t) ^ a *
          deltaCount n (Real.log n - 1 + t - u) ^ b := by
      congr 1
      funext u
      congr 2 <;> congr 1 <;> ring
    _ = ∫ u : ℝ, deltaCount n (u - t) ^ a * deltaCount n u ^ b :=
      integral_sub_left_eq_self
        (fun u : ℝ => deltaCount n (u - t) ^ a * deltaCount n u ^ b)
        volume (Real.log n - 1 + t)
    _ = deltaMixedMoment n b a t := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => mul_comm _ _)

end Erdos587
