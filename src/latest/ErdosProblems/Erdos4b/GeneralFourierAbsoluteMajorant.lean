/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPrimeChoices
import ErdosProblems.Erdos4b.GeneralFourierEulerProduct

/-!
# A cutoff-independent absolute Euler majorant

Positive real Euler factors bound the sum of the absolute values of all
finite prime-choice terms. Their complete product is the norm of the
Riemann zeta function on the real half-line to the right of one.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def realPrimeEulerDecay (σ p : ℝ) : ℝ := Real.exp (-σ * Real.log p)

theorem realPrimeEulerDecay_pos (σ p : ℝ) : 0 < realPrimeEulerDecay σ p := Real.exp_pos _

theorem realPrimeEulerDecay_lt_one {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) :
    realPrimeEulerDecay σ p < 1 := by
  unfold realPrimeEulerDecay
  rw [Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hσ) (Real.log_pos hp)

theorem realPrimeEulerDecay_le_one {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) :
    realPrimeEulerDecay σ p ≤ 1 := by
  unfold realPrimeEulerDecay
  rw [Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) (Real.log_nonneg hp)

theorem primeFourierPower_real_eq (σ p : ℝ) :
    primeFourierPower p (σ : ℂ) = (realPrimeEulerDecay σ p : ℂ) := by
  simp only [primeFourierPower, realPrimeEulerDecay, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg, neg_mul]

theorem norm_primeFourierPower_eq_realPrimeEulerDecay (p : ℝ) (s : ℂ) :
    ‖primeFourierPower p s‖ = realPrimeEulerDecay s.re p := by
  simp [primeFourierPower, Complex.norm_exp, realPrimeEulerDecay]

theorem realPrimeEulerDecay_sub_one_div {p : ℝ} (hp : 0 < p) (σ : ℝ) :
    realPrimeEulerDecay (σ - 1) p / p = realPrimeEulerDecay σ p := by
  unfold realPrimeEulerDecay
  calc
    _ = Real.exp (-(σ - 1) * Real.log p) / Real.exp (Real.log p) := by rw [Real.exp_log hp]
    _ = Real.exp (-(σ - 1) * Real.log p - Real.log p) := (Real.exp_sub _ _).symm
    _ = _ := congrArg Real.exp (by ring)

theorem one_add_nat_mul_le_inv_one_sub_pow {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (n : ℕ) :
    1 + n * x ≤ ((1 - x)⁻¹) ^ n := by
  have hrec : 1 + x ≤ (1 - x)⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr hx1)]
    nlinarith [sq_nonneg x]
  exact (one_add_mul_le_pow (by linarith : -2 ≤ x) n).trans
    (pow_le_pow_left₀ (by linarith) hrec n)

theorem norm_complex_primeEulerFactor_eq {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) :
    ‖((1 : ℂ) - (p : ℂ) ^ (-(σ : ℂ)))⁻¹‖ = (1 - realPrimeEulerDecay σ p)⁻¹ := by
  rw [← primeFourierPower_eq_cpow_neg (lt_trans zero_lt_one hp), primeFourierPower_real_eq]
  have hcast : (1 : ℂ) - (realPrimeEulerDecay σ p : ℂ) =
      ((1 - realPrimeEulerDecay σ p : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (sub_pos.mpr (realPrimeEulerDecay_lt_one hσ hp))]

theorem one_le_realPrimeEulerFactor {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) :
    1 ≤ (1 - realPrimeEulerDecay σ p)⁻¹ := by
  rw [inv_eq_one_div, le_div_iff₀ (sub_pos.mpr (realPrimeEulerDecay_lt_one hσ hp))]
  have hx := realPrimeEulerDecay_pos σ p
  linarith

theorem hasProd_realPrimeEulerFactors {σ : ℝ} (hσ : 1 < σ) :
    HasProd (fun p : Nat.Primes ↦ (1 - realPrimeEulerDecay σ p)⁻¹)
      ‖riemannZeta (σ : ℂ)‖ := by
  have h := (riemannZeta_eulerProduct_hasProd (s := (σ : ℂ)) (by simpa using hσ)).norm
  convert! h using 1
  ext p
  exact (norm_complex_primeEulerFactor_eq (lt_trans zero_lt_one hσ)
    (by exact_mod_cast p.property.one_lt)).symm

theorem prod_realPrimeEulerFactors_le_zeta
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {σ : ℝ} (hσ : 1 < σ) :
    (∏ p ∈ P, (1 - realPrimeEulerDecay σ p)⁻¹) ≤ ‖riemannZeta (σ : ℂ)‖ := by
  classical
  let f : P → Nat.Primes := fun p ↦ ⟨p.val, hP p p.property⟩
  have hf : Function.Injective f := fun p q h ↦
    Subtype.ext (congrArg (fun p : Nat.Primes ↦ p.val) h)
  have hfactor (p : Nat.Primes) : 1 ≤ (1 - realPrimeEulerDecay σ p)⁻¹ :=
    one_le_realPrimeEulerFactor (lt_trans zero_lt_one hσ) (by exact_mod_cast p.property.one_lt)
  have hbound : (∏ p ∈ Finset.univ.image f, (1 - realPrimeEulerDecay σ p)⁻¹) ≤
      ‖riemannZeta (σ : ℂ)‖ := by
    apply ge_of_tendsto (hasProd_realPrimeEulerFactors hσ)
    filter_upwards [Filter.eventually_ge_atTop (Finset.univ.image f)] with T hT
    exact Finset.prod_le_prod_of_subset_of_one_le hT
      (fun p hp ↦ (zero_le_one.trans (hfactor p))) (fun p hp hpS ↦ hfactor p)
  rw [Finset.prod_image (fun p hp q hq h ↦ hf h)] at hbound
  simpa only [f, Finset.prod_coe_sort P (fun p : ℕ ↦
    (1 - realPrimeEulerDecay σ p)⁻¹)] using hbound

theorem norm_primeFourierPower_le_decay {p σ : ℝ} (hp : 1 ≤ p)
    {s : ℂ} (hσ : σ ≤ s.re) : ‖primeFourierPower p s‖ ≤ realPrimeEulerDecay σ p := by
  rw [norm_primeFourierPower_eq_realPrimeEulerDecay]
  unfold realPrimeEulerDecay
  apply Real.exp_le_exp.mpr
  have hlog := Real.log_nonneg hp
  nlinarith

theorem sum_norm_prod_doubledPrimeChoiceWeight_le_zeta
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {σ : ℝ} (hσ : 1 < σ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (X X' Y Y' : ℕ → ι → ℂ)
    (hX : ∀ p ∈ P, ∀ i, ‖X p i‖ ≤ realPrimeEulerDecay (σ - 1) p)
    (hX' : ∀ p ∈ P, ∀ i, ‖X' p i‖ ≤ realPrimeEulerDecay (σ - 1) p)
    (hY : ∀ p ∈ P, ∀ i, ‖Y p i‖ ≤ realPrimeEulerDecay (σ - 1) p)
    (hY' : ∀ p ∈ P, ∀ i, ‖Y' p i‖ ≤ realPrimeEulerDecay (σ - 1) p) :
    (∑ c : P → DoubledPrimeChoice ι, ‖∏ p : P,
      doubledPrimeChoiceWeight (edges p) (companion p) p
        (X p) (X' p) (Y p) (Y' p) (c p)‖) ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  classical
  let N := Fintype.card (NonemptyDoubledPrimeChoice ι)
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  calc
    _ ≤ ∏ p ∈ P, (1 + (N : ℝ) * realPrimeEulerDecay (σ - 1) p / p) :=
      sum_norm_prod_doubledPrimeChoiceWeight_le P edges companion X X' Y Y'
        (fun p ↦ realPrimeEulerDecay (σ - 1) p)
        (fun p hp ↦ (hP p hp).pos)
        (fun p hp ↦ (realPrimeEulerDecay_pos _ _).le)
        (fun p hp ↦ realPrimeEulerDecay_le_one (by linarith)
          (by exact_mod_cast (hP p hp).one_lt.le)) hX hX' hY hY'
    _ ≤ ∏ p ∈ P, ((1 - realPrimeEulerDecay σ p)⁻¹) ^ N := by
      apply Finset.prod_le_prod
      · intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
        have hdecay := realPrimeEulerDecay_pos (σ - 1) p
        positivity
      · intro p hp
        rw [mul_div_assoc, realPrimeEulerDecay_sub_one_div (by exact_mod_cast (hP p hp).pos)]
        exact one_add_nat_mul_le_inv_one_sub_pow (realPrimeEulerDecay_pos _ _).le
          (realPrimeEulerDecay_lt_one hσ0 (by exact_mod_cast (hP p hp).one_lt)) N
    _ = (∏ p ∈ P, (1 - realPrimeEulerDecay σ p)⁻¹) ^ N := Finset.prod_pow ..
    _ ≤ _ := pow_le_pow_left₀ (Finset.prod_nonneg fun p hp ↦
        zero_le_one.trans (one_le_realPrimeEulerFactor hσ0 (by exact_mod_cast (hP p hp).one_lt)))
      (prod_realPrimeEulerFactors_le_zeta P hP hσ) N

theorem norm_prod_doubledFourierPolynomial_le_zeta
    {ι : Type*} [Fintype ι]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {σ : ℝ} (hσ : 1 < σ)
    (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (s s' t t' : ι → ℂ)
    (hs : ∀ i, σ - 1 ≤ (s i).re) (hs' : ∀ i, σ - 1 ≤ (s' i).re)
    (ht : ∀ i, σ - 1 ≤ (t i).re) (ht' : ∀ i, σ - 1 ≤ (t' i).re) :
    ‖∏ p ∈ P, doubledFourierLocalPolynomial Finset.univ (edges p) (companion p) p
      (fun i ↦ selbergPairPolynomial (primeFourierPower p (s i)) (primeFourierPower p (s' i)))
      (fun i ↦ selbergPairPolynomial (primeFourierPower p (t i)) (primeFourierPower p (t' i)))‖ ≤
      ‖riemannZeta (σ : ℂ)‖ ^ Fintype.card (NonemptyDoubledPrimeChoice ι) := by
  classical
  rw [← sum_prod_doubledPrimeChoiceWeight P edges companion
    (fun p i ↦ primeFourierPower p (s i)) (fun p i ↦ primeFourierPower p (s' i))
    (fun p i ↦ primeFourierPower p (t i)) (fun p i ↦ primeFourierPower p (t' i))]
  apply (norm_sum_le _ _).trans
  exact sum_norm_prod_doubledPrimeChoiceWeight_le_zeta P hP hσ edges companion
    (fun p i ↦ primeFourierPower p (s i)) (fun p i ↦ primeFourierPower p (s' i))
    (fun p i ↦ primeFourierPower p (t i)) (fun p i ↦ primeFourierPower p (t' i))
    (fun p hp i ↦ norm_primeFourierPower_le_decay (by exact_mod_cast (hP p hp).one_lt.le) (hs i))
    (fun p hp i ↦ norm_primeFourierPower_le_decay (by exact_mod_cast (hP p hp).one_lt.le) (hs' i))
    (fun p hp i ↦ norm_primeFourierPower_le_decay (by exact_mod_cast (hP p hp).one_lt.le) (ht i))
    (fun p hp i ↦ norm_primeFourierPower_le_decay (by exact_mod_cast (hP p hp).one_lt.le) (ht' i))

theorem exists_small_real_zeta_norm_bound :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ → ε * ‖riemannZeta (1 + (ε : ℂ))‖ ≤ 2 := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp
    continuousAt_selbergZetaResidueFactor_zero 1 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  have hdist : dist (ε : ℂ) 0 < δ := by
    simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] using hεδ
  have hclose : ‖selbergZetaResidueFactor (ε : ℂ) - 1‖ < 1 := by
    simpa only [selbergZetaResidueFactor_zero, dist_eq_norm] using hbound hdist
  have hnorm : ‖selbergZetaResidueFactor (ε : ℂ)‖ ≤ 2 := by
    have htri := norm_le_norm_sub_add (selbergZetaResidueFactor (ε : ℂ)) (1 : ℂ)
    norm_num only [norm_one] at htri
    linarith
  rw [selbergZetaResidueFactor_of_ne_zero (by exact_mod_cast hε.ne'), norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at hnorm
  exact hnorm

theorem exists_zetaRealNearOne_norm_bound :
    ∃ L₀ > 0, ∀ L : ℝ, L₀ ≤ L → ‖riemannZeta (1 + ((L⁻¹ : ℝ) : ℂ))‖ ≤ 2 * L := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_real_zeta_norm_bound
  refine ⟨δ⁻¹ + 1, by positivity, ?_⟩
  intro L hL₀
  have hL : 0 < L := lt_of_lt_of_le (by positivity : 0 < δ⁻¹ + 1) hL₀
  have hδinv : 1 / δ < L := by rw [one_div]; linarith
  have hprod : 1 < L * δ := (div_lt_iff₀ hδ).mp hδinv
  have hsmallL : L⁻¹ < δ := by
    rw [← one_div, div_lt_iff₀ hL]
    nlinarith
  have hb := hsmall L⁻¹ (inv_pos.mpr hL) hsmallL
  have hdiv : ‖riemannZeta (1 + ((L⁻¹ : ℝ) : ℂ))‖ / L ≤ 2 := by
    simpa only [div_eq_mul_inv, mul_comm] using hb
  exact (div_le_iff₀ hL).mp hdiv

end

end Erdos4b
