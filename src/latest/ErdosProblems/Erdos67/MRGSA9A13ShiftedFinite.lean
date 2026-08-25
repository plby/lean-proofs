import ErdosProblems.Erdos67.MRGSA9A14Shifted

/-!
# A shifted-line finite A.13 estimate

After the finitely many small primes have been removed, every Euler variable
on the left A.10 line has norm at most one third.  This file packages the
finite A.11 argument in a form which can then be shifted horizontally without
a loss proportional to the number of primes.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- Finite A.13 in squared form on an arbitrary vertical line.  The three
sets are intended to be the outside primes and the two deleted blocks.  No
relation among the sets is needed for this analytic inequality; exact
partition identities are applied downstream. -/
theorem norm_threeEulerBlockAlternating_sq_le_full_products_of_norm_le_third
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S₀ S₂ S₃ : Finset ℕ)
    (hprime₀ : ∀ p ∈ S₀, p.Prime)
    (hprime₂ : ∀ p ∈ S₂, p.Prime)
    (hprime₃ : ∀ p ∈ S₃, p.Prime)
    {sigma t : ℝ}
    (hsmall₀ : ∀ p ∈ S₀,
      ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hsmall₂ : ∀ p ∈ S₂,
      ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ))
    (hsmall₃ : ∀ p ∈ S₃,
      ‖(p : ℂ) ^ (-((sigma : ℂ) + Complex.I * (t : ℂ)))‖ ≤ (1 / 3 : ℝ)) :
    let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
    let sr : ℂ := (sigma : ℂ)
    let one : ℕ → ℂ := fun _ ↦ 1
    let P₀ := ∏ p ∈ S₀, gsA9LocalEulerFactor f s p
    let P₂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f s p
    let P₃ := ∏ p ∈ S₃, gsA9LocalEulerFactor f s p
    let P₀p := ∏ p ∈ S₀, gsA9LocalEulerFactor one sr p
    let P₂p := ∏ p ∈ S₂, gsA9LocalEulerFactor one sr p
    let P₃p := ∏ p ∈ S₃, gsA9LocalEulerFactor one sr p
    let V₀ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-s)‖ ^ 2
    let V₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖ ^ 2
    let V₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖ ^ 2
    ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
      Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
        ‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖ := by
  dsimp only
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let sr : ℂ := (sigma : ℂ)
  let one : ℕ → ℂ := fun _ ↦ 1
  let P₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor f s p
  let P₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f s p
  let P₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor f s p
  let P₀p : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor one sr p
  let P₂p : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor one sr p
  let P₃p : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor one sr p
  let R₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-s)‖
  let R₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖
  let R₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖
  let z₀ : ℂ := ∑ p ∈ S₀, f p * (p : ℂ) ^ (-s)
  let V₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖ ^ 2
  change ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
    Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
      ‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖
  have honeMul : IsMultiplicativeOnPositiveNat one := by
    refine ⟨by simp [one], ?_⟩
    intro m n _ _ _
    simp [one]
  have honeBound : ∀ n, 0 < n → ‖one n‖ ≤ 1 := by simp [one]
  have hnormShift (p : ℕ) (hp : p.Prime) :
      ‖(p : ℂ) ^ (-s)‖ = ‖(p : ℂ) ^ (-sr)‖ := by
    rw [show s = (sigma : ℂ) + Complex.I * (t : ℂ) by rfl,
      Erdos67.HalaszCpowDeficit.norm_nat_cpow_neg_sigma_add_I_mul hp.pos,
      show sr = (sigma : ℂ) by rfl,
      Erdos67.EulerQuantitative.norm_prime_cpow_neg_real sigma ⟨p, hp⟩]
  have hreNorm (p : ℕ) (hp : p.Prime) :
      ((p : ℂ) ^ (-sr)).re = ‖(p : ℂ) ^ (-s)‖ := by
    calc
      ((p : ℂ) ^ (-sr)).re = ‖(p : ℂ) ^ (-sr)‖ := by
        rw [show sr = (sigma : ℂ) by rfl]
        have hr : ((p : ℂ) ^ (-(sigma : ℂ))) =
            (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
          rw [show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by push_cast; ring]
          exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-sigma)).symm
        rw [hr, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
      _ = ‖(p : ℂ) ^ (-s)‖ := (hnormShift p hp).symm
  have hsmall₀p : ∀ p ∈ S₀, ‖(p : ℂ) ^ (-sr)‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    rw [← hnormShift p (hprime₀ p hp)]
    exact hsmall₀ p hp
  have hsmall₂p : ∀ p ∈ S₂, ‖(p : ℂ) ^ (-sr)‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    rw [← hnormShift p (hprime₂ p hp)]
    exact hsmall₂ p hp
  have hsmall₃p : ∀ p ∈ S₃, ‖(p : ℂ) ^ (-sr)‖ ≤ (1 / 3 : ℝ) := by
    intro p hp
    rw [← hnormShift p (hprime₃ p hp)]
    exact hsmall₃ p hp
  have hV₀p : (∑ p ∈ S₀, ‖(p : ℂ) ^ (-sr)‖ ^ 2) = V₀ := by
    dsimp only [V₀]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hprime₀ p hp)]
  have hV₂p : (∑ p ∈ S₂, ‖(p : ℂ) ^ (-sr)‖ ^ 2) = V₂ := by
    dsimp only [V₂]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hprime₂ p hp)]
  have hV₃p : (∑ p ∈ S₃, ‖(p : ℂ) ^ (-sr)‖ ^ 2) = V₃ := by
    dsimp only [V₃]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hprime₃ p hp)]
  have hR₀p : (∑ p ∈ S₀, ‖(p : ℂ) ^ (-sr)‖) = R₀ := by
    dsimp only [R₀]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hnormShift p (hprime₀ p hp)]
  have hblock₂ : ‖P₂ - 1‖ ^ 2 ≤
      Real.exp (R₂ + 20 * V₂) * ‖P₂‖ := by
    have hu := norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le_of_norm_le_third
      hmul hbound S₂ hprime₂ (s := s) hsmall₂
    have hl := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
      hmul hbound S₂ hprime₂ (s := s) hsmall₂
    exact sq_le_exp_radius_add_twenty_mul_square_mul_of_block_bounds
      (norm_nonneg _) (by simpa only [P₂, R₂, V₂] using hu)
      (by simpa only [P₂, V₂] using hl)
  have hblock₃ : ‖P₃ - 1‖ ^ 2 ≤
      Real.exp (R₃ + 20 * V₃) * ‖P₃‖ := by
    have hu := norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le_of_norm_le_third
      hmul hbound S₃ hprime₃ (s := s) hsmall₃
    have hl := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
      hmul hbound S₃ hprime₃ (s := s) hsmall₃
    exact sq_le_exp_radius_add_twenty_mul_square_mul_of_block_bounds
      (norm_nonneg _) (by simpa only [P₃, R₃, V₃] using hu)
      (by simpa only [P₃, V₃] using hl)
  have hP₀upper : ‖P₀‖ ≤ Real.exp (z₀.re + 3 * V₀) := by
    dsimp only [P₀, z₀, V₀]
    simpa only [Complex.re_sum] using
      norm_prod_gsA9LocalEulerFactor_le_exp_linear_add_square_of_norm_le_half
        hmul hbound S₀ hprime₀ (s := s)
          (fun p hp ↦ (hsmall₀ p hp).trans (by norm_num))
  have hz₀ : z₀.re ≤ R₀ := by
    dsimp only [z₀, R₀]
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro p hp
    exact (Complex.re_le_norm _).trans (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (hbound p (hprime₀ p hp).pos))
  have hP₀plower : Real.exp (R₀ - 4 * V₀) ≤ ‖P₀p‖ := by
    have hl := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
      honeMul honeBound S₀ hprime₀ (s := sr) hsmall₀p
    have hz : (∑ p ∈ S₀, one p * (p : ℂ) ^ (-sr)).re = R₀ := by
      simp only [one, one_mul, Complex.re_sum]
      rw [← hR₀p]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show sr = (sigma : ℂ) by rfl]
      have hr : ((p : ℂ) ^ (-(sigma : ℂ))) =
          (((p : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
        rw [show -(sigma : ℂ) = ((-sigma : ℝ) : ℂ) by push_cast; ring]
        exact (Complex.ofReal_cpow (Nat.cast_nonneg p) (-sigma)).symm
      rw [hr, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    simpa only [P₀p, hz, hV₀p] using hl
  have hP₀sq : ‖P₀‖ ^ 2 ≤
      Real.exp (7 * V₀) * (‖P₀‖ * ‖P₀p‖) := by
    have hratio : ‖P₀‖ ≤ Real.exp (7 * V₀) * ‖P₀p‖ := by
      calc
        ‖P₀‖ ≤ Real.exp (z₀.re + 3 * V₀) := hP₀upper
        _ ≤ Real.exp (R₀ + 3 * V₀) := by gcongr
        _ = Real.exp (7 * V₀) * Real.exp (R₀ - 4 * V₀) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ Real.exp (7 * V₀) * ‖P₀p‖ := by gcongr
    nlinarith [norm_nonneg P₀]
  have hnormAlt : ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 =
      ‖P₀‖ ^ 2 * ‖P₂ - 1‖ ^ 2 * ‖P₃ - 1‖ ^ 2 := by
    rw [norm_mul, norm_mul]
    ring
  have hexpPre :
      Real.exp (7 * V₀) * Real.exp (R₂ + 20 * V₂) * Real.exp (R₃ + 20 * V₃) =
        Real.exp (7 * V₀ + 20 * (V₂ + V₃)) * Real.exp (R₂ + R₃) := by
    calc
      Real.exp (7 * V₀) * Real.exp (R₂ + 20 * V₂) * Real.exp (R₃ + 20 * V₃) =
          Real.exp (7 * V₀ + (R₂ + 20 * V₂) + (R₃ + 20 * V₃)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      _ = Real.exp (7 * V₀ + 20 * (V₂ + V₃)) * Real.exp (R₂ + R₃) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hpre : ‖P₀ * (P₂ - 1) * (P₃ - 1)‖ ^ 2 ≤
      Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
        (‖P₀ * P₂ * P₃‖ * ‖P₀p‖) *
        Real.exp (R₂ + R₃) := by
    rw [hnormAlt]
    calc
      ‖P₀‖ ^ 2 * ‖P₂ - 1‖ ^ 2 * ‖P₃ - 1‖ ^ 2 ≤
        (Real.exp (7 * V₀) * (‖P₀‖ * ‖P₀p‖)) *
          (Real.exp (R₂ + 20 * V₂) * ‖P₂‖) *
          (Real.exp (R₃ + 20 * V₃) * ‖P₃‖) := by
        gcongr
      _ = Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
          (‖P₀ * P₂ * P₃‖ * ‖P₀p‖) *
          Real.exp (R₂ + R₃) := by
        rw [norm_mul, norm_mul]
        calc
          (Real.exp (7 * V₀) * (‖P₀‖ * ‖P₀p‖)) *
                (Real.exp (R₂ + 20 * V₂) * ‖P₂‖) *
                (Real.exp (R₃ + 20 * V₃) * ‖P₃‖) =
              (Real.exp (7 * V₀) * Real.exp (R₂ + 20 * V₂) *
                Real.exp (R₃ + 20 * V₃)) *
                ((‖P₀‖ * ‖P₂‖ * ‖P₃‖) * ‖P₀p‖) := by ring
          _ = Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
                ((‖P₀‖ * ‖P₂‖ * ‖P₃‖) * ‖P₀p‖) *
                Real.exp (R₂ + R₃) := by
            rw [hexpPre]
            ring
  have hR₂lower : Real.exp (R₂ - 4 * V₂) ≤ ‖P₂p‖ := by
    have hl := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
      honeMul honeBound S₂ hprime₂ (s := sr) hsmall₂p
    have hz : (∑ p ∈ S₂, one p * (p : ℂ) ^ (-sr)).re = R₂ := by
      simp only [one, one_mul, Complex.re_sum, R₂]
      apply Finset.sum_congr rfl
      intro p hp
      exact hreNorm p (hprime₂ p hp)
    simpa only [P₂p, hz, hV₂p] using hl
  have hR₃lower : Real.exp (R₃ - 4 * V₃) ≤ ‖P₃p‖ := by
    have hl := exp_linear_sub_square_le_norm_prod_gsA9LocalEulerFactor_of_norm_le_third
      honeMul honeBound S₃ hprime₃ (s := sr) hsmall₃p
    have hz : (∑ p ∈ S₃, one p * (p : ℂ) ^ (-sr)).re = R₃ := by
      simp only [one, one_mul, Complex.re_sum, R₃]
      apply Finset.sum_congr rfl
      intro p hp
      exact hreNorm p (hprime₃ p hp)
    simpa only [P₃p, hz, hV₃p] using hl
  have hR : Real.exp (R₂ + R₃) ≤
      Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖) := by
    calc
      Real.exp (R₂ + R₃) =
          Real.exp (4 * (V₂ + V₃)) *
            (Real.exp (R₂ - 4 * V₂) * Real.exp (R₃ - 4 * V₃)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖) := by
        gcongr
  have hexpFinal :
      Real.exp (7 * V₀ + 20 * (V₂ + V₃)) * Real.exp (4 * (V₂ + V₃)) =
        Real.exp (7 * V₀ + 24 * (V₂ + V₃)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  exact hpre.trans (by
    calc
    Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
          (‖P₀ * P₂ * P₃‖ * ‖P₀p‖) *
          Real.exp (R₂ + R₃) ≤
        Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
          (‖P₀ * P₂ * P₃‖ * ‖P₀p‖) *
          (Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖)) := by
      gcongr
    _ = Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
        ‖P₀ * P₂ * P₃‖ * ‖P₀p * P₂p * P₃p‖ := by
      simp only [norm_mul]
      calc
        Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
              (‖P₀‖ * ‖P₂‖ * ‖P₃‖ * ‖P₀p‖) *
              (Real.exp (4 * (V₂ + V₃)) * (‖P₂p‖ * ‖P₃p‖)) =
            (Real.exp (7 * V₀ + 20 * (V₂ + V₃)) *
              Real.exp (4 * (V₂ + V₃))) *
              ((‖P₀‖ * ‖P₂‖ * ‖P₃‖) *
                (‖P₀p‖ * ‖P₂p‖ * ‖P₃p‖)) := by ring
        _ = Real.exp (7 * V₀ + 24 * (V₂ + V₃)) *
              (‖P₀‖ * ‖P₂‖ * ‖P₃‖) *
              (‖P₀p‖ * ‖P₂p‖ * ‖P₃p‖) := by
          rw [hexpFinal]
          ring)

/-- A paired horizontal-shift estimate for the actual and positive finite
Euler products.  Keeping the two radial displacement sums explicit lets the
source-shaped real/complex specialization identify them exactly, without
dividing by any local Euler factor. -/
theorem mul_norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
    {sLow sHigh srLow srHigh : ℂ} (c cp : ℕ → ℝ)
    (hc : ∀ p ∈ S, 1 ≤ c p)
    (hcp : ∀ p ∈ S, 1 ≤ cp p)
    (hfactor : ∀ p ∈ S,
      (p : ℂ) ^ (-sLow) = (c p : ℂ) * (p : ℂ) ^ (-sHigh))
    (hfactorp : ∀ p ∈ S,
      (p : ℂ) ^ (-srLow) = (cp p : ℂ) * (p : ℂ) ^ (-srHigh))
    (hthird : ∀ p ∈ S, ‖(p : ℂ) ^ (-sLow)‖ ≤ (1 / 3 : ℝ))
    (hthirdp : ∀ p ∈ S, ‖(p : ℂ) ^ (-srLow)‖ ≤ (1 / 3 : ℝ)) :
    let one : ℕ → ℂ := fun _ ↦ 1
    ‖∏ p ∈ S, gsA9LocalEulerFactor f sLow p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor one srLow p‖ ≤
      (‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
        ‖∏ p ∈ S, gsA9LocalEulerFactor one srHigh p‖) *
      Real.exp (6 *
        ((∑ p ∈ S, (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) +
          ∑ p ∈ S, (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖))) := by
  dsimp only
  let one : ℕ → ℂ := fun _ ↦ 1
  have honeMul : IsMultiplicativeOnPositiveNat one := by
    refine ⟨by simp [one], ?_⟩
    intro m n _ _ _
    simp [one]
  have honeBound : ∀ n, 0 < n → ‖one n‖ ≤ 1 := by simp [one]
  have hf := norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    hmul hbound S hprime c hc hfactor hthird
  have hp := norm_prod_gsA9LocalEulerFactor_shift_le_exp_sum_norm_sub
    honeMul honeBound S hprime cp hcp hfactorp hthirdp
  have hexp :
      Real.exp (6 * ∑ p ∈ S,
          (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) *
        Real.exp (6 * ∑ p ∈ S,
          (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖)) =
      Real.exp (6 *
        ((∑ p ∈ S, (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) +
          ∑ p ∈ S, (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    ‖∏ p ∈ S, gsA9LocalEulerFactor f sLow p‖ *
          ‖∏ p ∈ S, gsA9LocalEulerFactor one srLow p‖ ≤
        (‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
          Real.exp (6 * ∑ p ∈ S,
            (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖))) *
        (‖∏ p ∈ S, gsA9LocalEulerFactor one srHigh p‖ *
          Real.exp (6 * ∑ p ∈ S,
            (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖))) := by
      gcongr
    _ = (‖∏ p ∈ S, gsA9LocalEulerFactor f sHigh p‖ *
          ‖∏ p ∈ S, gsA9LocalEulerFactor one srHigh p‖) *
        Real.exp (6 *
          ((∑ p ∈ S, (‖(p : ℂ) ^ (-sLow)‖ - ‖(p : ℂ) ^ (-sHigh)‖)) +
            ∑ p ∈ S, (‖(p : ℂ) ^ (-srLow)‖ - ‖(p : ℂ) ^ (-srHigh)‖))) := by
      rw [← hexp]
      ring

end

end Erdos67.MRHalaszBands
