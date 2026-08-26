/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientIncidence

/-!
# Uniform local bound at a forced prime

Every retained coefficient state, including the empty state, carries
the denominator `p - 1`. The estimate is valid for every restriction
of the state set and all Fourier exponents with nonnegative real part.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem norm_doubledPrimeChoiceNumerator_le_one
    {ι : Type*} [Fintype ι] (c : DoubledPrimeChoice ι)
    (W : (ι ⊕ ι) → Bool → ℂ) (hW : ∀ i b, ‖W i b‖ ≤ 1) :
    ‖doubledPrimeChoiceNumerator c W‖ ≤ 1 := by
  classical
  unfold doubledPrimeChoiceNumerator
  simp only [norm_prod]
  apply Finset.prod_le_one (fun i _ ↦ Finset.prod_nonneg fun b _ ↦ norm_nonneg _)
  intro i hi
  apply Finset.prod_le_one (fun b _ ↦ norm_nonneg _)
  intro b hb
  split_ifs
  · simpa only [norm_neg] using hW i b
  · simp only [norm_one, le_refl]

open Classical in
def forcedTotientLocalFactor {ι : Type*} [Fintype ι]
    (allow : DoubledPrimeChoice ι → Prop) (p : ℝ) (W : (ι ⊕ ι) → Bool → ℂ) : ℂ :=
  ∑ c : DoubledPrimeChoice ι,
    if allow c then doubledPrimeChoiceNumerator c W / ((p - 1 : ℝ) : ℂ) else 0

theorem norm_forcedTotientLocalFactor_le
    {ι : Type*} [Fintype ι] (allow : DoubledPrimeChoice ι → Prop)
    {p : ℝ} (hp : 2 ≤ p) (W : (ι ⊕ ι) → Bool → ℂ) (hW : ∀ i b, ‖W i b‖ ≤ 1) :
    ‖forcedTotientLocalFactor allow p W‖ ≤ 2 * Fintype.card (DoubledPrimeChoice ι) / p := by
  classical
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  unfold forcedTotientLocalFactor
  calc
    _ ≤ ∑ c : DoubledPrimeChoice ι,
        ‖if allow c then doubledPrimeChoiceNumerator c W / ((p - 1 : ℝ) : ℂ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _c : DoubledPrimeChoice ι, (1 : ℝ) / (p - 1) := by
      apply Finset.sum_le_sum
      intro c hc
      split_ifs
      · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp1]
        exact div_le_div_of_nonneg_right (norm_doubledPrimeChoiceNumerator_le_one c W hW) hp1.le
      · simpa only [norm_zero] using (div_nonneg zero_le_one hp1.le)
    _ = (Fintype.card (DoubledPrimeChoice ι) : ℝ) / (p - 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    _ ≤ _ := by
      rw [div_le_div_iff₀ hp1 hp0]
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (DoubledPrimeChoice ι))]

def forcedTotientFourierPrimeFactor {ι : Type*} [Fintype ι]
    (allow : DoubledPrimeChoice ι → Prop) (s : (ι ⊕ ι) → Bool → ℂ) (p : ℕ) : ℂ :=
  forcedTotientLocalFactor allow p (fun i b ↦ primeFourierPower p (s i b))

theorem norm_forcedTotientFourierPrimeFactor_le
    {ι : Type*} [Fintype ι] (allow : DoubledPrimeChoice ι → Prop)
    (s : (ι ⊕ ι) → Bool → ℂ) (hs : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes) :
    ‖forcedTotientFourierPrimeFactor allow s p‖ ≤
      2 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ) := by
  exact norm_forcedTotientLocalFactor_le allow (by exact_mod_cast p.property.two_le) _
    (fun i b ↦ norm_primeFourierPower_le_one (by exact_mod_cast p.property.one_lt.le) (hs i b))

theorem half_le_norm_totientDoubledFourierPrimeFactor
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (hs : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes)
    (hp : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ (p : ℝ)) :
    (1 : ℝ) / 2 ≤ ‖totientDoubledFourierPrimeFactor edges companion s p‖ := by
  unfold totientDoubledFourierPrimeFactor
  have hpos : 0 < (p : ℝ) - 1 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    linarith only [hp2]
  have hbound : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ (p : ℝ) - 1 := by
    linarith only [hp]
  have hnum := norm_doubledFourierPrimeNumerator_le edges companion s hs p
  have he := half_le_norm_one_add_div_of_norm_le hpos hbound hnum
  simpa only [Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_one] using he

theorem norm_forcedTotientFourierPrimeFactor_div_le
    {ι : Type*} [Fintype ι] (allow : DoubledPrimeChoice ι → Prop)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s : (ι ⊕ ι) → Bool → ℂ) (hs : ∀ i b, 0 ≤ (s i b).re) (p : Nat.Primes)
    (hp : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) + 2 ≤ (p : ℝ)) :
    ‖forcedTotientFourierPrimeFactor allow s p /
      totientDoubledFourierPrimeFactor edges companion s p‖ ≤
        4 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ) := by
  rw [norm_div]
  calc
    _ ≤ (2 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ)) /
        ‖totientDoubledFourierPrimeFactor edges companion s p‖ :=
      div_le_div_of_nonneg_right (norm_forcedTotientFourierPrimeFactor_le allow s hs p)
        (norm_nonneg _)
    _ ≤ (2 * Fintype.card (DoubledPrimeChoice ι) / (p : ℝ)) / (1 / 2 : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num)
        (half_le_norm_totientDoubledFourierPrimeFactor edges companion s hs p hp)
    _ = _ := by ring

end

end Erdos4b
