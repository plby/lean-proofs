import ErdosProblems.Erdos67.MRGSA9OutsideEuler
import ErdosProblems.Erdos67.MRGSA9ActualBlockFactor

/-!
# The finite Euler-product composition used in GS A.13

This file combines the exact alternating low-factor identity, the ordinary
outside Euler-product bound, and the two actual block-factor estimates.  Its
conclusion is the complete finite Euler inequality inserted into the contour
identity before the maximum-modulus step.
-/

open scoped BigOperators LSeries.notation

namespace Erdos67.MRHalaszBands

noncomputable section

/-- The alternating four low-prime series for two arbitrary disjoint deletion
blocks has the expected exact three-factor Euler decomposition. -/
theorem twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_disjoint
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    (y : ℕ)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s =
      (∏ p ∈ primesUpTo y with ¬ Q₂ p ∧ ¬ Q₃ p,
          gsA9LocalEulerFactor f s p) *
        ((∏ p ∈ primesUpTo y with Q₂ p,
            gsA9LocalEulerFactor f s p) - 1) *
        ((∏ p ∈ primesUpTo y with Q₃ p,
            gsA9LocalEulerFactor f s p) - 1) := by
  rw [LSeries_gsA9Low_eq_finiteEulerProduct hmul hbound y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound Q₂ y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound Q₃ y hs,
    LSeries_gsA9LowDeletion_eq_finiteEulerProduct hmul hbound
      (fun p ↦ Q₂ p ∨ Q₃ p) y hs]
  exact alternating_filtered_products_eq (primesUpTo y) Q₂ Q₃
    hdisj (gsA9LocalEulerFactor f s)

/-- A.13-ready finite Euler bound.  The outside primes retain their full
linear real part, while each deleted block contributes half its linear real
part; every higher prime power is absorbed by the corresponding quadratic
prime mass. -/
theorem norm_twoBlock_alternatingLow_LSeries_mul_exp_neg_radii_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (Q₂ Q₃ : ℕ → Prop) [DecidablePred Q₂] [DecidablePred Q₃]
    (y : ℕ)
    (hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False)
    (hthree₂ : ∀ p ∈ primesUpTo y, Q₂ p → 3 ≤ p)
    (hthree₃ : ∀ p ∈ primesUpTo y, Q₃ p → 3 ≤ p)
    {sigma t : ℝ} (hsigma : 1 < sigma) :
    let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
    let S₀ := (primesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
    let S₂ := (primesUpTo y).filter Q₂
    let S₃ := (primesUpTo y).filter Q₃
    let z₀ := ∑ p ∈ S₀, f p * (p : ℂ) ^ (-s)
    let z₂ := ∑ p ∈ S₂, f p * (p : ℂ) ^ (-s)
    let z₃ := ∑ p ∈ S₃, f p * (p : ℂ) ^ (-s)
    let R₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖
    let R₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖
    let V₀ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-s)‖ ^ 2
    let V₂ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖ ^ 2
    let V₃ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖ ^ 2
    ‖LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s‖ *
        Real.exp (-(R₂ + R₃) / 2) ≤
      Real.exp
        (z₀.re + 3 * V₀ + z₂.re / 2 + 8 * V₂ +
          z₃.re / 2 + 8 * V₃) := by
  dsimp only
  let s : ℂ := (sigma : ℂ) + Complex.I * (t : ℂ)
  let S₀ : Finset ℕ :=
    (primesUpTo y).filter (fun p ↦ ¬ Q₂ p ∧ ¬ Q₃ p)
  let S₂ : Finset ℕ := (primesUpTo y).filter Q₂
  let S₃ : Finset ℕ := (primesUpTo y).filter Q₃
  let z₀ : ℂ := ∑ p ∈ S₀, f p * (p : ℂ) ^ (-s)
  let z₂ : ℂ := ∑ p ∈ S₂, f p * (p : ℂ) ^ (-s)
  let z₃ : ℂ := ∑ p ∈ S₃, f p * (p : ℂ) ^ (-s)
  let R₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖
  let R₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖
  let V₀ : ℝ := ∑ p ∈ S₀, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let V₂ : ℝ := ∑ p ∈ S₂, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let V₃ : ℝ := ∑ p ∈ S₃, ‖(p : ℂ) ^ (-s)‖ ^ 2
  let P₀ : ℂ := ∏ p ∈ S₀, gsA9LocalEulerFactor f s p
  let P₂ : ℂ := ∏ p ∈ S₂, gsA9LocalEulerFactor f s p
  let P₃ : ℂ := ∏ p ∈ S₃, gsA9LocalEulerFactor f s p
  have hsre : 1 < s.re := by simpa [s] using hsigma
  have hsreWeak : 1 ≤ s.re := hsre.le
  have hS₀prime : ∀ p ∈ S₀, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₂prime : ∀ p ∈ S₂, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₃prime : ∀ p ∈ S₃, p.Prime := by
    intro p hp
    exact (mem_primesUpTo.mp (Finset.mem_filter.mp hp).1).1
  have hS₂three : ∀ p ∈ S₂, 3 ≤ p := by
    intro p hp
    exact hthree₂ p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have hS₃three : ∀ p ∈ S₃, 3 ≤ p := by
    intro p hp
    exact hthree₃ p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  have halt := twoBlock_alternatingLow_LSeries_eq_EulerFactors_of_disjoint
    hmul hbound Q₂ Q₃ y hdisj hsre
  have halt' :
      LSeries (gsA9Low f y) s -
          LSeries (gsA9LowDeletion f Q₂ y) s -
          LSeries (gsA9LowDeletion f Q₃ y) s +
          LSeries (gsA9LowDeletion f (fun p ↦ Q₂ p ∨ Q₃ p) y) s =
        P₀ * (P₂ - 1) * (P₃ - 1) := by
    simpa only [S₀, S₂, S₃, P₀, P₂, P₃] using halt
  have h₀ : ‖P₀‖ ≤ Real.exp (z₀.re + 3 * V₀) := by
    dsimp only [P₀, z₀, V₀]
    simpa only [s, Complex.re_sum] using
      norm_prod_gsA9LocalEulerFactor_le_exp_linear_add_square
        hmul hbound S₀ hS₀prime hsigma.le t
  have h₂ : ‖P₂ - 1‖ * Real.exp (-R₂ / 2) ≤
      Real.exp (z₂.re / 2 + 8 * V₂) := by
    dsimp only [P₂, R₂, z₂, V₂]
    exact norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le
      hmul hbound S₂ hS₂prime hS₂three hsreWeak
  have h₃ : ‖P₃ - 1‖ * Real.exp (-R₃ / 2) ≤
      Real.exp (z₃.re / 2 + 8 * V₃) := by
    dsimp only [P₃, R₃, z₃, V₃]
    exact norm_prod_gsA9LocalEulerFactor_sub_one_mul_exp_neg_radius_le
      hmul hbound S₃ hS₃prime hS₃three hsreWeak
  rw [halt', norm_mul, norm_mul]
  have hexpRadius : Real.exp (-(R₂ + R₃) / 2) =
      Real.exp (-R₂ / 2) * Real.exp (-R₃ / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexpRadius]
  calc
    ‖P₀‖ * ‖P₂ - 1‖ * ‖P₃ - 1‖ *
          (Real.exp (-R₂ / 2) * Real.exp (-R₃ / 2)) =
        ‖P₀‖ * (‖P₂ - 1‖ * Real.exp (-R₂ / 2)) *
          (‖P₃ - 1‖ * Real.exp (-R₃ / 2)) := by ring
    _ ≤ Real.exp (z₀.re + 3 * V₀) *
          Real.exp (z₂.re / 2 + 8 * V₂) *
          Real.exp (z₃.re / 2 + 8 * V₃) := by
      gcongr
    _ = Real.exp
        (z₀.re + 3 * V₀ + z₂.re / 2 + 8 * V₂ +
          z₃.re / 2 + 8 * V₃) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end

end Erdos67.MRHalaszBands
