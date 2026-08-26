/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierReferenceProduct

/-!
# Uniform removal of the finite pre-sieve reference correction

The local reference factor differs from its zero-exponent value by an
exact product of two Fourier increments. A deliberately coarse bound
is enough: the error in the full small-prime correction tends to zero
whenever the exponent bound times the pre-sieve cutoff tends to zero.
-/

namespace Erdos4b

noncomputable section

open Filter
open scoped BigOperators Topology

theorem selbergPairZetaFactor_sub_zero_identity {p : ℝ} (hp : p ≠ 0)
    {X Y : ℂ} (hden : 1 - X * Y / (p : ℂ) ≠ 0) :
    selbergPairZetaFactor p X Y - (1 - 1 / (p : ℂ)) =
      (selbergPairPolynomial X Y + 1) / ((p : ℂ) * (1 - X * Y / p)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hden' : (p : ℂ) - X * Y ≠ 0 := by
    intro h
    apply hden
    rw [← sub_eq_zero.mp h, div_self hpC]
    ring
  unfold selbergPairZetaFactor selbergPairPolynomial
  field_simp [hpC, hden, hden']
  ring

theorem norm_zero_div_selbergPairZetaFactor_sub_one_le
    {p σ : ℝ} (hp : 2 ≤ p) (hσ : 0 ≤ σ) {s t : ℂ}
    (hs : 0 ≤ s.re) (ht : 0 ≤ t.re) (hNorm : ‖s‖ ≤ σ) :
    ‖(1 - 1 / (p : ℂ)) /
      selbergPairZetaFactor p (primeFourierPower p s) (primeFourierPower p t) - 1‖ ≤
        24 * σ := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  let X := primeFourierPower p s
  let Y := primeFourierPower p t
  have hX : ‖X‖ ≤ 1 := norm_primeFourierPower_le_one hp1 hs
  have hY : ‖Y‖ ≤ 1 := norm_primeFourierPower_le_one hp1 ht
  have hXY : ‖X * Y‖ ≤ 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg X, norm_nonneg Y]
  have hden := half_le_norm_one_sub_complex_div hp hXY
  have hden0 : 1 - X * Y / (p : ℂ) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hden
    norm_num at hden
  have hB := one_sixth_le_norm_selbergPairZetaFactor hp hX hY
  have hB0 := selbergPairZetaFactor_ne_zero hp hX hY
  have hnum : ‖selbergPairPolynomial X Y + 1‖ ≤ 2 * σ * Real.log p :=
    norm_selbergPairPolynomial_primeFourierPowers_add_one_le hp1 hs ht hNorm
  have hlog : Real.log p ≤ p := (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg hp1
  have hdiff : ‖selbergPairZetaFactor p X Y - (1 - 1 / (p : ℂ))‖ ≤ 4 * σ := by
    rw [selbergPairZetaFactor_sub_zero_identity hp0.ne' hden0, norm_div,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    calc
      _ ≤ (2 * σ * Real.log p) / (p * (1 / 2)) :=
        div_le_div₀ (by positivity) hnum (by positivity)
          (mul_le_mul_of_nonneg_left hden hp0.le)
      _ ≤ (2 * σ * p) / (p * (1 / 2)) := by gcongr
      _ = 4 * σ := by field_simp; ring
  change ‖(1 - 1 / (p : ℂ)) / selbergPairZetaFactor p X Y - 1‖ ≤ _
  conv_lhs => arg 1; rhs; rw [← div_self hB0]
  rw [← sub_div, norm_div, norm_sub_rev]
  calc
    _ ≤ (4 * σ) / (1 / 6) := div_le_div₀ (by positivity) hdiff (by norm_num) hB
    _ = 24 * σ := by ring

theorem doubledFourierReferenceFactor_zero {ι : Type*} [Fintype ι] (p : Nat.Primes) :
    doubledFourierReferenceFactor (ι := ι) (fun _ _ ↦ 0) p =
      (1 - 1 / (p : ℂ)) ^ Fintype.card (ι ⊕ ι) := by
  unfold doubledFourierReferenceFactor
  simp only [primeFourierPower, zero_mul, neg_zero, Complex.exp_zero]
  rw [selbergPairZetaFactor_at_zero_exponents (by exact_mod_cast p.property.two_le)]
  simp

theorem card_boundedFourierPrimes_le (w : ℕ) :
    (boundedFourierPrimes w).card ≤ w + 1 := by
  have h := Finset.card_le_card_of_injOn (s := boundedFourierPrimes w)
    (t := Finset.range (w + 1)) (fun p : Nat.Primes ↦ p.val)
    (fun p hp ↦ Finset.mem_range.mpr
      (Nat.lt_succ_of_le ((mem_boundedFourierPrimes w p).mp hp)))
    (fun p hp q hq h ↦ Subtype.ext h)
  simpa only [Finset.card_range] using h

theorem smallDoubledFourierReferenceProduct_zero_div_eq
    {ι : Type*} [Fintype ι] (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) :
    smallDoubledFourierReferenceProduct (ι := ι) w (fun _ _ ↦ 0) /
      smallDoubledFourierReferenceProduct w s =
      ∏ pi ∈ (boundedFourierPrimes w).product (Finset.univ : Finset (ι ⊕ ι)),
        (1 - 1 / (pi.1.val : ℂ)) /
          selbergPairZetaFactor pi.1.val (primeFourierPower pi.1.val (s pi.2 false))
            (primeFourierPower pi.1.val (s pi.2 true)) := by
  calc
    _ = ∏ p ∈ boundedFourierPrimes w, ∏ i : ι ⊕ ι,
        (1 - 1 / (p.val : ℂ)) /
          selbergPairZetaFactor p.val (primeFourierPower p.val (s i false))
            (primeFourierPower p.val (s i true)) := by
      rw [smallDoubledFourierReferenceProduct,
        smallDoubledFourierReferenceProduct, ← Finset.prod_div_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      rw [doubledFourierReferenceFactor_zero]
      unfold doubledFourierReferenceFactor
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ]
    _ = _ := by
      exact (Finset.prod_product (boundedFourierPrimes w) (Finset.univ : Finset (ι ⊕ ι))
        (fun pi : Nat.Primes × (ι ⊕ ι) ↦
          (1 - 1 / (pi.1.val : ℂ)) /
            selbergPairZetaFactor pi.1.val (primeFourierPower pi.1.val (s pi.2 false))
              (primeFourierPower pi.1.val (s pi.2 true)))).symm

theorem norm_smallDoubledFourierReferenceProduct_zero_div_sub_one_le
    {ι : Type*} [Fintype ι] (w : ℕ) (s : (ι ⊕ ι) → Bool → ℂ) {σ : ℝ}
    (hσ : 0 ≤ σ) (hRe : ∀ i b, 0 ≤ (s i b).re) (hNorm : ∀ i, ‖s i false‖ ≤ σ) :
    ‖smallDoubledFourierReferenceProduct (ι := ι) w (fun _ _ ↦ 0) /
      smallDoubledFourierReferenceProduct w s - 1‖ ≤
      Real.exp (24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ * (w + 1)) - 1 := by
  classical
  let P := (boundedFourierPrimes w).product (Finset.univ : Finset (ι ⊕ ι))
  let R : Nat.Primes × (ι ⊕ ι) → ℂ := fun pi ↦
    (1 - 1 / (pi.1.val : ℂ)) /
      selbergPairZetaFactor pi.1.val (primeFourierPower pi.1.val (s pi.2 false))
        (primeFourierPower pi.1.val (s pi.2 true))
  have hlocal (pi : Nat.Primes × (ι ⊕ ι)) : ‖R pi - 1‖ ≤ 24 * σ :=
    norm_zero_div_selbergPairZetaFactor_sub_one_le
      (by exact_mod_cast pi.1.property.two_le) hσ
      (hRe pi.2 false) (hRe pi.2 true) (hNorm pi.2)
  have hsum : (∑ pi ∈ P, ‖R pi - 1‖) ≤
      24 * (Fintype.card (ι ⊕ ι) : ℝ) * σ * (w + 1) := by
    have hcardP : P.card = (boundedFourierPrimes w).card * Fintype.card (ι ⊕ ι) := by
      simpa only [Finset.card_univ] using!
        Finset.card_product (boundedFourierPrimes w) (Finset.univ : Finset (ι ⊕ ι))
    calc
      _ ≤ ∑ pi ∈ P, 24 * σ := Finset.sum_le_sum (fun pi hpi ↦ hlocal pi)
      _ = (boundedFourierPrimes w).card * (Fintype.card (ι ⊕ ι) : ℝ) * (24 * σ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcardP, Nat.cast_mul]
      _ ≤ (w + 1) * (Fintype.card (ι ⊕ ι) : ℝ) * (24 * σ) := by
        gcongr
        exact_mod_cast card_boundedFourierPrimes_le w
      _ = _ := by ring
  rw [smallDoubledFourierReferenceProduct_zero_div_eq]
  have hprod := norm_prod_one_add_error_le P (fun pi ↦ R pi - 1)
  simp only [add_sub_cancel] at hprod
  exact hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

theorem tendsto_smallDoubledFourierReferenceProduct_zero_div
    {α ι : Type*} [Fintype ι] {l : Filter α}
    (w : α → ℕ) (s : α → (ι ⊕ ι) → Bool → ℂ) (σ : α → ℝ)
    (hσ : ∀ a, 0 ≤ σ a) (hRe : ∀ a i b, 0 ≤ (s a i b).re)
    (hNorm : ∀ a i, ‖s a i false‖ ≤ σ a)
    (hsmall : Tendsto (fun a ↦ σ a * (w a + 1)) l (𝓝 0)) :
    Tendsto (fun a ↦ smallDoubledFourierReferenceProduct (ι := ι) (w a) (fun _ _ ↦ 0) /
      smallDoubledFourierReferenceProduct (w a) (s a)) l (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun a ↦ norm_nonneg _) (fun a ↦
    norm_smallDoubledFourierReferenceProduct_zero_div_sub_one_le
      (w a) (s a) (hσ a) (hRe a) (hNorm a))
  have hbound := ((Real.continuous_exp.continuousAt.tendsto).comp
    (hsmall.const_mul (24 * (Fintype.card (ι ⊕ ι) : ℝ)))).sub_const 1
  simpa only [mul_zero, Real.exp_zero, sub_self, Function.comp_def, mul_assoc] using hbound

theorem norm_smallDoubledFourierReferenceProduct_zero_le_one
    {ι : Type*} [Fintype ι] (w : ℕ) :
    ‖smallDoubledFourierReferenceProduct (ι := ι) w (fun _ _ ↦ 0)‖ ≤ 1 := by
  unfold smallDoubledFourierReferenceProduct
  rw [norm_prod]
  apply Finset.prod_le_one (fun p hp ↦ norm_nonneg _)
  intro p hp
  rw [doubledFourierReferenceFactor_zero]
  exact norm_zeroExponentPairProduct_le_one _ (by exact_mod_cast p.property.two_le)

end

end Erdos4b
