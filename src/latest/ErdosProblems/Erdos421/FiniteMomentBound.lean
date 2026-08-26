import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! # A finite mixed-moment bound for a repeated coordinate

The argument uses the three-term weighted arithmetic-geometric mean
inequality. Keeping a common moment bound as a positive power avoids
fractional powers in the finite counting step.
-/

namespace Erdos421

theorem mixed_power_young (n : ℕ) {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ((n : ℝ) + 2) * c * (a ^ n * b) ≤
      (n : ℝ) * a ^ (n + 2) + b ^ (n + 2) + c ^ (n + 2) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hweights : (n : ℝ) / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2) +
      1 / ((n : ℝ) + 2) = 1 := by field_simp; ring
  have h := Real.geom_mean_le_arith_mean3_weighted
    (p₁ := a ^ (n + 2)) (p₂ := b ^ (n + 2)) (p₃ := c ^ (n + 2))
    (div_nonneg (Nat.cast_nonneg n) hn.le) (div_nonneg zero_le_one hn.le)
    (div_nonneg zero_le_one hn.le) (pow_nonneg ha _) (pow_nonneg hb _)
    (pow_nonneg hc _) hweights
  have hpow (x : ℝ) (hx : 0 ≤ x) (t : ℝ) :
      (x ^ (n + 2)) ^ (t / ((n : ℝ) + 2)) = x ^ t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    congr 1
    push_cast
    field_simp
  rw [hpow a ha n, hpow b hb 1, hpow c hc 1, Real.rpow_natCast,
    Real.rpow_one, Real.rpow_one] at h
  have hm := mul_le_mul_of_nonneg_left h hn.le
  field_simp at hm
  nlinarith

theorem finite_mixed_moment_bound {X : Type*} (S : Finset X) (f g : X → ℝ)
    (n : ℕ) {B : ℝ} (hB : 0 < B) (hf : ∀ x ∈ S, 0 ≤ f x) (hg : ∀ x ∈ S, 0 ≤ g x)
    (hfm : (∑ x ∈ S, f x ^ (n + 2)) ≤ (S.card : ℝ) * B ^ (n + 2))
    (hgm : (∑ x ∈ S, g x ^ (n + 2)) ≤ (S.card : ℝ) * B ^ (n + 2)) :
    (∑ x ∈ S, f x ^ n * g x) ≤ (S.card : ℝ) * B ^ (n + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hy := Finset.sum_le_sum (fun x hx ↦ mixed_power_young n (hf x hx) (hg x hx) hB.le)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hy
  have hupper : ((n : ℝ) + 2) * B * (∑ x ∈ S, f x ^ n * g x) ≤
      ((n : ℝ) + 2) * ((S.card : ℝ) * B ^ (n + 2)) := by
    calc
      _ ≤ (n : ℝ) * (∑ x ∈ S, f x ^ (n + 2)) +
          (∑ x ∈ S, g x ^ (n + 2)) + (S.card : ℝ) * B ^ (n + 2) := hy
      _ ≤ (n : ℝ) * ((S.card : ℝ) * B ^ (n + 2)) +
          (S.card : ℝ) * B ^ (n + 2) + (S.card : ℝ) * B ^ (n + 2) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfm (Nat.cast_nonneg n)) hgm) le_rfl
      _ = _ := by ring
  apply (mul_le_mul_iff_right₀ hB).mp
  calc
    B * (∑ x ∈ S, f x ^ n * g x) ≤ (S.card : ℝ) * B ^ (n + 2) :=
      (mul_le_mul_iff_right₀ hn).mp (by simpa only [mul_assoc] using hupper)
    _ = B * ((S.card : ℝ) * B ^ (n + 1)) := by rw [pow_succ]; ring

end Erdos421
