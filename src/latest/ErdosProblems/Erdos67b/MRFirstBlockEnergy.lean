import ErdosProblems.Erdos67b.MRSmallBlockEnergy
import ErdosProblems.Erdos67b.MRSmallBlockParameters

/-!
# The first-small-block base case

Without a preceding large block, use the cofactor's finite mean square
and sum the current prime thresholds as a geometric progression.
-/

open scoped BigOperators Interval
open Finset MeasureTheory

namespace Erdos67b

theorem intervalIntegral_cofactor_subset_rectangle_le
    {S : Finset ℕ} {b : ℕ → ℂ} {L U X : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hX : 0 < X) (hLX : L ≤ X) (hUL : U ≤ 2 * L)
    (hS : S ⊆ mrDyadicCofactorRectangle (L, U) X)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      8 * T * U / X + 32 * Real.pi := by
  let M := X / U + 1
  let N := (2 * X) / L
  have hM : 0 < M := Nat.succ_pos _
  have hN : 0 < N := Nat.div_pos (by omega) hL
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hSlow (m : ℕ) (hm : m ∈ S) : M ≤ m :=
    Nat.succ_le_iff.mpr (Finset.mem_Ioc.mp (hS hm)).1
  have hSup (m : ℕ) (hm : m ∈ S) : m ≤ N := (Finset.mem_Ioc.mp (hS hm)).2
  have hSpos (m : ℕ) (hm : m ∈ S) : 0 < m := hM.trans_le (hSlow m hm)
  have hmass : (∑ m ∈ S, Complex.normSq (b m)) ≤
      ((mrDyadicCofactorRectangle (L, U) X).card : ℝ) / (M : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _m ∈ S, (M : ℝ)⁻¹ ^ 2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hinv : (m : ℝ)⁻¹ ≤ (M : ℝ)⁻¹ :=
          inv_anti₀ (by exact_mod_cast hM) (by exact_mod_cast hSlow m hm)
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) ((hb m hm).trans hinv) 2
      _ = (S.card : ℝ) * (M : ℝ)⁻¹ ^ 2 := by simp
      _ ≤ ((mrDyadicCofactorRectangle (L, U) X).card : ℝ) * (M : ℝ)⁻¹ ^ 2 := by
        gcongr
      _ = _ := by rw [div_eq_mul_inv, inv_pow]
  have hmass' : (∑ m ∈ S, Complex.normSq (b m)) ≤ 4 * (U : ℝ) / X :=
    hmass.trans (mrDyadicCofactorRectangle_cardRatio_cofactor_le hL hU hX hUL)
  have hNU : N * U ≤ 4 * X := by
    calc
      _ ≤ N * (2 * L) := Nat.mul_le_mul_left N hUL
      _ = 2 * (L * N) := by ring
      _ ≤ 2 * (2 * X) := Nat.mul_le_mul_left 2 (Nat.mul_div_le _ _)
      _ = _ := by ring
  have hNUr : (N : ℝ) * U / X ≤ 4 := by
    apply (div_le_iff₀ hXr).mpr
    exact_mod_cast hNU
  calc
    _ = ‖∫ t in -T..T,
        star (logarithmicDirichletPolynomial S b t) * logarithmicDirichletPolynomial S b t‖ :=
      intervalIntegral_norm_sq_eq_norm_conj_mul_self _ hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) * ∑ m ∈ S, Complex.normSq (b m) :=
      norm_logarithmicDirichletPolynomial_intervalIntegral_le_support hN hSpos hSup b hT
    _ ≤ (2 * T + 2 * Real.pi * (N : ℝ)) * (4 * U / X) :=
      mul_le_mul_of_nonneg_left hmass' (by positivity)
    _ = 8 * T * U / X + 8 * Real.pi * ((N : ℝ) * U / X) := by ring
    _ ≤ _ := by nlinarith [Real.pi_pos]

/-- A lower bound for the geometric denominator, with no asymptotic
notation or limit argument. -/
theorem one_sub_exp_neg_ge_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have hbound := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hbound
  have hnonneg : 0 ≤ 1 - Real.exp (-x) := by
    have hh : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hx1) hnonneg]

theorem sum_mrLogBlock_threshold_sq_le
    {H p q beta : ℝ} (hH : 1 ≤ H) (_hp : 0 ≤ p)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1 / 4) :
    (∑ r ∈ mrLogBlockIndices H p q, Real.exp (-beta * ((r : ℝ) / H)) ^ 2) ≤
      Real.exp 1 * (H / beta) * Real.exp (-2 * beta * p) := by
  have hH0 : 0 < H := by linarith
  let x : ℝ := 2 * beta / H
  let z : ℝ := Real.exp (-x)
  have hx0 : 0 < x := by dsimp only [x]; positivity
  have hx1 : x ≤ 1 := by
    apply (div_le_iff₀ hH0).mpr
    linarith
  have hz0 : 0 < z := Real.exp_pos _
  have hz1 : z < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx0)
  have hden : beta / H ≤ 1 - z := by
    have hh := one_sub_exp_neg_ge_half hx0.le hx1
    calc
      beta / H = x / 2 := by dsimp only [x]; ring
      _ ≤ 1 - z := hh
  have hterm (r : ℕ) : Real.exp (-beta * ((r : ℝ) / H)) ^ 2 = z ^ r := by
    dsimp only [z, x]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hfloor : p - 1 ≤ (Nat.floor (H * p) : ℝ) / H := by
    have hh := (Nat.lt_floor_add_one (H * p)).le
    apply (le_div_iff₀ hH0).mpr
    nlinarith
  have hstart : z ^ Nat.floor (H * p) ≤ Real.exp 1 * Real.exp (-2 * beta * p) := by
    dsimp only [z, x]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hfloor (by positivity : 0 ≤ 2 * beta)
    calc
      _ = -(2 * beta * ((Nat.floor (H * p) : ℝ) / H)) := by ring
      _ ≤ -(2 * beta * (p - 1)) := neg_le_neg hh
      _ ≤ _ := by nlinarith
  calc
    _ = ∑ r ∈ Finset.Ico (Nat.floor (H * p)) (Nat.floor (H * q) + 1), z ^ r := by
      have hi : Finset.Icc (Nat.floor (H * p)) (Nat.floor (H * q)) =
          Finset.Ico (Nat.floor (H * p)) (Nat.floor (H * q) + 1) := by
        ext r
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      simp only [hterm, mrLogBlockIndices, hi]
    _ ≤ z ^ Nat.floor (H * p) / (1 - z) := geom_sum_Ico_le_of_lt_one hz0.le hz1
    _ ≤ (Real.exp 1 * Real.exp (-2 * beta * p)) / (beta / H) := by
      exact div_le_div₀ (by positivity) hstart (by positivity) hden
    _ = _ := by field_simp

/-- Uniform cofactor bound for all narrow intervals in one logarithmic
prime block. The support may be restricted arbitrarily. -/
theorem intervalIntegral_cofactor_rectangle_uniform_le
    {S : Finset ℕ} {b : ℕ → ℂ} {L U X : ℕ}
    (hL : 0 < L) (hU : 0 < U) (hX : 0 < X) (hLX : L ≤ X) (hUL : U ≤ 2 * L)
    (hS : S ⊆ mrDyadicCofactorRectangle (L, U) X)
    (hb : ∀ m ∈ S, ‖b m‖ ≤ (m : ℝ)⁻¹)
    {q : ℝ} (hUq : (U : ℝ) ≤ Real.exp (q + 1)) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in -T..T, ‖logarithmicDirichletPolynomial S b t‖ ^ 2) ≤
      32 * (1 + Real.pi) * (T / X * Real.exp q + 1) := by
  have hUexp : (U : ℝ) ≤ 4 * Real.exp q := by
    calc
      _ ≤ Real.exp (q + 1) := hUq
      _ = Real.exp q * Real.exp 1 := Real.exp_add q 1
      _ ≤ Real.exp q * 4 := mul_le_mul_of_nonneg_left
        (Real.exp_one_lt_d9.le.trans (by norm_num)) (Real.exp_pos _).le
      _ = _ := by ring
  have hbase := intervalIntegral_cofactor_subset_rectangle_le hL hU hX hLX hUL hS hb hT
  apply hbase.trans
  have hscale := mul_le_mul_of_nonneg_left hUexp (show 0 ≤ 8 * T / X by positivity)
  have hpi := mul_nonneg (Real.pi_pos.le) (show 0 ≤ T / X * Real.exp q by positivity)
  calc
    8 * T * U / X + 32 * Real.pi = (8 * T / X) * U + 32 * Real.pi := by ring
    _ ≤ (8 * T / X) * (4 * Real.exp q) + 32 * Real.pi := add_le_add hscale le_rfl
    _ ≤ _ := by ring_nf at hpi ⊢; linarith

/-- Complete first-small-block product energy, before substituting the
source resolution. No preceding prime polynomial is required. -/
theorem firstBlock_frequencyClass_energy_le
    {H p q beta : ℝ} (hH : 1 ≤ H) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hbeta0 : 0 < beta) (hbeta1 : beta ≤ 1 / 4)
    (J : ℕ → ℕ × ℕ) (S : ℕ → Finset ℕ) (b : ℕ → ℕ → ℂ) (F : ℕ → ℝ → ℂ)
    {X : ℕ} (hX : 0 < X)
    (hJlo : ∀ r ∈ mrLogBlockIndices H p q, 0 < (J r).1)
    (hJhi : ∀ r ∈ mrLogBlockIndices H p q, 0 < (J r).2)
    (hJX : ∀ r ∈ mrLogBlockIndices H p q, (J r).1 ≤ X)
    (hJwidth : ∀ r ∈ mrLogBlockIndices H p q, (J r).2 ≤ 2 * (J r).1)
    (hJq : ∀ r ∈ mrLogBlockIndices H p q, ((J r).2 : ℝ) ≤ Real.exp (q + 1))
    (hS : ∀ r ∈ mrLogBlockIndices H p q, S r ⊆ mrDyadicCofactorRectangle (J r) X)
    (hb : ∀ r ∈ mrLogBlockIndices H p q, ∀ m ∈ S r, ‖b r m‖ ≤ (m : ℝ)⁻¹)
    (hF : ∀ r ∈ mrLogBlockIndices H p q, Continuous (F r))
    {E : Set ℝ} (hE : MeasurableSet E) {T : ℝ} (hT : 0 ≤ T)
    (hsmall : ∀ r ∈ mrLogBlockIndices H p q, ∀ t ∈ E, t ∈ Set.Icc (-T) T →
      ‖F r t‖ ≤ Real.exp (-beta * ((r : ℝ) / H))) :
    H * q * (∑ r ∈ mrLogBlockIndices H p q, ∫ t in -T..T,
      E.indicator (fun t ↦ ‖F r t * logarithmicDirichletPolynomial (S r) (b r) t‖ ^ 2) t) ≤
        (32 * Real.exp 1 * (1 + Real.pi) / beta) *
          (T / X * Real.exp q + 1) * (H ^ 2 * q * Real.exp (-2 * beta * p)) := by
  let C : ℝ := 32 * (1 + Real.pi) * (T / X * Real.exp q + 1)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hlocal (r : ℕ) (hr : r ∈ mrLogBlockIndices H p q) :
      (∫ t in -T..T, E.indicator
        (fun t ↦ ‖F r t * logarithmicDirichletPolynomial (S r) (b r) t‖ ^ 2) t) ≤
          Real.exp (-beta * ((r : ℝ) / H)) ^ 2 * C := by
    have hrestrict := intervalIntegral_indicator_norm_sq_mul_le_cross_power (hF r hr)
      (continuous_const : Continuous (fun _ : ℝ ↦ (1 : ℂ)))
      (continuous_logarithmicDirichletPolynomial (S r) (b r)) hE hT
      (Real.exp_pos _).le (by norm_num : (0 : ℝ) < 1)
      (hsmall r hr) (by intros; norm_num) 0
    simp only [Nat.mul_zero, pow_zero, inv_one, mul_one, one_mul] at hrestrict
    apply hrestrict.trans
    exact mul_le_mul_of_nonneg_left
      (intervalIntegral_cofactor_rectangle_uniform_le (hJlo r hr) (hJhi r hr) hX
        (hJX r hr) (hJwidth r hr) (hS r hr) (hb r hr) (hJq r hr) hT) (by positivity)
  calc
    _ ≤ H * q * (∑ r ∈ mrLogBlockIndices H p q,
        Real.exp (-beta * ((r : ℝ) / H)) ^ 2 * C) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hlocal) (by positivity)
    _ = (H * q * C) * ∑ r ∈ mrLogBlockIndices H p q,
        Real.exp (-beta * ((r : ℝ) / H)) ^ 2 := by rw [← Finset.sum_mul]; ring
    _ ≤ (H * q * C) * (Real.exp 1 * (H / beta) * Real.exp (-2 * beta * p)) :=
      mul_le_mul_of_nonneg_left (sum_mrLogBlock_threshold_sq_le hH hp hbeta0 hbeta1) (by positivity)
    _ = _ := by dsimp only [C]; ring

/-- Exact saving from the source's first-block resolution. -/
theorem firstBlock_resolution_saving {eta p q : ℝ} (hq : 0 < q) :
    mrLogBlockResolution eta p q 1 ^ 2 * q * Real.exp (-2 * mrThresholdExponent eta 1 * p) =
      Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) := by
  unfold mrLogBlockResolution mrThresholdExponent
  norm_num
  rw [← Real.exp_nat_mul]
  calc
    _ = Real.exp (2 * ((1 / 6 - eta) * p - Real.log q / 3) +
        Real.log q + (-2 * (1 / 4 - eta * (1 + 1 / 2)) * p)) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_log hq]
      norm_num
    _ = _ := by congr 1; ring

/-- The threshold is uniformly at least one eighth, so the first-block
resolution gives the stated source saving with an absolute constant. -/
theorem firstBlock_resolution_energy_prefactor_le
    {eta p q tau : ℝ} (heta : eta ≤ 1 / 12) (hq : 0 < q) (htau : 0 ≤ tau) :
    (32 * Real.exp 1 * (1 + Real.pi) / mrThresholdExponent eta 1) *
        (tau * Real.exp q + 1) *
        (mrLogBlockResolution eta p q 1 ^ 2 * q * Real.exp (-2 * mrThresholdExponent eta 1 * p)) ≤
      256 * Real.exp 1 * (1 + Real.pi) * (tau * Real.exp q + 1) *
        Real.exp (Real.log q / 3 - (1 / 6 - eta) * p) := by
  have hbeta : 1 / 8 ≤ mrThresholdExponent eta 1 := by
    unfold mrThresholdExponent
    norm_num
    linarith
  have hbeta0 : 0 < mrThresholdExponent eta 1 := by linarith
  have hconstant : 32 * Real.exp 1 * (1 + Real.pi) / mrThresholdExponent eta 1 ≤
      256 * Real.exp 1 * (1 + Real.pi) := by
    apply (div_le_iff₀ hbeta0).mpr
    have hh := mul_le_mul_of_nonneg_left hbeta
      (show 0 ≤ 256 * Real.exp 1 * (1 + Real.pi) by positivity)
    nlinarith
  rw [firstBlock_resolution_saving hq]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconstant (by positivity)) (Real.exp_pos _).le

end Erdos67b
