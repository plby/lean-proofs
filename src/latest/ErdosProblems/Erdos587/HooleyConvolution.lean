import ErdosProblems.Erdos587.HooleyHarmonicMean

/-!
# Divisor twists of the harmonic Delta sum

Expanding a nonnegative divisor weight and factoring each integer turns
the twist into a divisor-count convolution. This is the finite algebraic
input for Rankin weights in the short-progression sieve.
-/

open scoped BigOperators

namespace Erdos587

theorem delta_harmonic_divisor_twist_le (N : ℕ) (g : ℕ → ℝ) (hg : ∀ d, 0 ≤ g d) :
    (∑ n ∈ Finset.Icc 1 N, ((hooleyDelta n : ℝ) / n) * ∑ d ∈ n.divisors, g d) ≤
      (∑ d ∈ Finset.Icc 1 N, (d.divisors.card : ℝ) * g d / d) *
        ∑ m ∈ Finset.Icc 1 N, (hooleyDelta m : ℝ) / m := by
  classical
  let D : Finset (Σ _n : ℕ, ℕ) := (Finset.Icc 1 N).sigma (fun n => n.divisors)
  let i := fun z : (Σ _n : ℕ, ℕ) => (z.2, z.1 / z.2)
  let H := fun z : ℕ × ℕ =>
    ((z.1.divisors.card : ℝ) * g z.1 / z.1) * ((hooleyDelta z.2 : ℝ) / z.2)
  have hprod (z : Σ _n : ℕ, ℕ) (hz : z ∈ D) : z.2 * (z.1 / z.2) = z.1 :=
    Nat.mul_div_cancel' (Nat.mem_divisors.mp (Finset.mem_sigma.mp hz).2).1
  have hinj : Set.InjOn i (D : Set (Σ _n : ℕ, ℕ)) := by
    intro z hz w hw heq
    have hd := congrArg Prod.fst heq
    have hm := congrArg Prod.snd heq
    have hfirst : z.1 = w.1 :=
      (hprod z hz).symm.trans ((congrArg₂ Nat.mul hd hm).trans (hprod w hw))
    exact Sigma.ext hfirst (heq_of_eq hd)
  have hsub : D.image i ⊆ (Finset.Icc 1 N) ×ˢ Finset.Icc 1 N := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hn, hd⟩ := Finset.mem_sigma.mp hw
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    have hdpos := Nat.pos_of_mem_divisors hd
    have hdle := Nat.le_of_dvd hn1 (Nat.mem_divisors.mp hd).1
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hdpos, hdle.trans hnN⟩,
      Finset.mem_Icc.mpr ⟨Nat.div_pos hdle hdpos, (Nat.div_le_self _ _).trans hnN⟩⟩
  have hpoint (z : Σ _n : ℕ, ℕ) (hz : z ∈ D) :
      ((hooleyDelta z.1 : ℝ) / z.1) * g z.2 ≤ H (i z) := by
    calc
      _ = g z.2 * ((hooleyDelta (z.2 * (z.1 / z.2)) : ℝ) / (z.2 * (z.1 / z.2) : ℕ)) := by
        rw [hprod z hz]
        ring
      _ ≤ g z.2 * (((z.2.divisors.card : ℝ) / z.2) *
          ((hooleyDelta (z.1 / z.2) : ℝ) / (z.1 / z.2 : ℕ))) :=
        mul_le_mul_of_nonneg_left (delta_harmonic_mul_le z.2 (z.1 / z.2)) (hg z.2)
      _ = _ := by dsimp only [H, i]; ring
  calc
    _ = ∑ z ∈ D, ((hooleyDelta z.1 : ℝ) / z.1) * g z.2 := by
      dsimp only [D]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
    _ ≤ ∑ z ∈ D, H (i z) := Finset.sum_le_sum hpoint
    _ = ∑ z ∈ D.image i, H z := (Finset.sum_image hinj).symm
    _ ≤ ∑ z ∈ (Finset.Icc 1 N) ×ˢ Finset.Icc 1 N, H z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro z hz hnot
      dsimp only [H]
      exact mul_nonneg (div_nonneg (mul_nonneg (by positivity) (hg _)) (by positivity))
        (by positivity)
    _ = _ := by
      dsimp only [H]
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]

end Erdos587
