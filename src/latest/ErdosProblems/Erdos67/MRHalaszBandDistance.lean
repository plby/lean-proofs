import ErdosProblems.Erdos67.MRHalaszBandLSeries

/-!
# Pretentious distance across the three Halász prime bands

At a prime, exactly one of the three canonical band restrictions retains
the original coefficient and the other two vanish.  Consequently the sum
of their pretentious-distance terms is the original term plus `2/p`.  In
particular a nonpretentious coefficient has at least one band carrying one
third of its distance.  This is the pigeonhole input for choosing the
`L∞` factor in the cheap Halász proof.
-/

open scoped BigOperators ComplexConjugate
open Finset Complex

namespace Erdos67.MRHalaszBands

noncomputable section

theorem primeSupported_prime_iff
    (P : ℕ → Prop) {p : ℕ} (hp : p.Prime) :
    PrimeSupported P p ↔ P p := by
  constructor
  · intro h
    apply h.2 p
    rw [hp.primeFactors]
    simp
  · intro hP
    refine ⟨hp.ne_zero, ?_⟩
    intro q hq
    rw [hp.primeFactors] at hq
    simp only [Finset.mem_singleton] at hq
    subst q
    exact hP

theorem primeBandCoefficient_at_prime
    (f : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {p : ℕ} (hp : p.Prime) :
    primeBandCoefficient f P p = if P p then f p else 0 := by
  unfold primeBandCoefficient
  rw [primeSupported_prime_iff P hp]
  by_cases hP : P p <;> simp [hP]

theorem pretentiousTerm_primeBandCoefficient
    (f g : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P]
    {p : ℕ} (hp : p.Prime) :
    pretentiousTerm (primeBandCoefficient f P) g p =
      if P p then pretentiousTerm f g p else 1 / (p : ℝ) := by
  rw [pretentiousTerm, primeBandCoefficient_at_prime f P hp]
  split_ifs <;> simp [pretentiousTerm]

/-- Pointwise three-band identity at a prime. -/
theorem sum_threeBand_pretentiousTerm
    (f g : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    {p : ℕ} (hp : p.Prime) :
    pretentiousTerm (primeBandCoefficient f P₁) g p +
        pretentiousTerm
          (primeBandCoefficient f (fun q ↦ ¬ P₁ q ∧ P₂ q)) g p +
        pretentiousTerm
          (primeBandCoefficient f (fun q ↦ ¬ P₁ q ∧ ¬ P₂ q)) g p =
      pretentiousTerm f g p + 2 / (p : ℝ) := by
  rw [pretentiousTerm_primeBandCoefficient f g P₁ hp,
    pretentiousTerm_primeBandCoefficient f g
      (fun q ↦ ¬ P₁ q ∧ P₂ q) hp,
    pretentiousTerm_primeBandCoefficient f g
      (fun q ↦ ¬ P₁ q ∧ ¬ P₂ q) hp]
  by_cases h₁ : P₁ p
  · simp [h₁]
    ring
  · by_cases h₂ : P₂ p
    · simp [h₁, h₂]
      ring
    · simp [h₁, h₂]
      ring

/-- The original distance is no larger than the sum of the distances of
the three canonical band restrictions. -/
theorem pretentiousDistSq_le_sum_threeBands
    (f g : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂] (X : ℕ) :
    pretentiousDistSq f g X ≤
      pretentiousDistSq (primeBandCoefficient f P₁) g X +
        pretentiousDistSq
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) g X +
        pretentiousDistSq
          (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) g X := by
  unfold pretentiousDistSq
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hpX
  have hp := (mem_primesUpTo.mp hpX).1
  rw [sum_threeBand_pretentiousTerm f g P₁ P₂ hp]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have htwo : (0 : ℝ) ≤ 2 / (p : ℝ) := div_nonneg (by norm_num) hpR.le
  linarith

/-- Quantitative pigeonhole: one of the three band factors carries at
least one third of any prescribed lower bound for the original distance. -/
theorem one_third_le_one_threeBand_pretentiousDistSq
    (f g : ℕ → ℂ) (P₁ P₂ : ℕ → Prop)
    [DecidablePred P₁] [DecidablePred P₂]
    {A : ℝ} {X : ℕ} (hA : A ≤ pretentiousDistSq f g X) :
    A / 3 ≤ pretentiousDistSq (primeBandCoefficient f P₁) g X ∨
      A / 3 ≤ pretentiousDistSq
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ P₂ p)) g X ∨
      A / 3 ≤ pretentiousDistSq
        (primeBandCoefficient f (fun p ↦ ¬ P₁ p ∧ ¬ P₂ p)) g X := by
  have hsum := pretentiousDistSq_le_sum_threeBands f g P₁ P₂ X
  by_contra h
  push Not at h
  linarith

end

end Erdos67.MRHalaszBands
