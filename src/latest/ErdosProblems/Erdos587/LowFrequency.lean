import ErdosProblems.Erdos587.CenteredSeries
import ErdosProblems.Erdos587.ChirpQuadrature

/-!
# Low frequencies with the integral main term retained

The centered weighted series subtracts a discrete mean. A uniform Poisson
quadrature bound replaces that mean by the integral used in the nearby-rational
decomposition.
-/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

noncomputable def integralCenteredChirpSeries (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A δ : ℝ) : ℂ :=
  (∑' n : ℤ, quadraticResiduePhase q a n * quadraticChirpMul A f (δ * n)) -
    (completeQuadraticGaussSum q a 0 / q) * (∫ x : ℝ, quadraticChirpMul A f (δ * x))

lemma centeredChirpSeries_eq_discrete_mean (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A : ℝ)
    {δ : ℝ} (hδ : δ ≠ 0) :
    centeredChirpSeries f q a A δ =
      (∑' n : ℤ, quadraticResiduePhase q a n * quadraticChirpMul A f (δ * n)) -
        (completeQuadraticGaussSum q a 0 / q) * ∑' n : ℤ, quadraticChirpMul A f (δ * n) := by
  have hw : Summable (fun n : ℤ => quadraticChirpMul A f (δ * n)) :=
    summable_schwartz_int (dilateSchwartz (quadraticChirpMul A f) δ hδ)
  have hquad : Summable (fun n : ℤ => quadraticResiduePhase q a n * quadraticChirpMul A f (δ * n)) := by
    apply Summable.of_norm
    simpa only [quadraticResiduePhase, norm_mul, norm_phase, one_mul] using hw.norm
  have hmean := hw.mul_left (completeQuadraticGaussSum q a 0 / q)
  have heq (n : ℤ) : quadraticChirpMul A f (δ * n) *
      (quadraticResiduePhase q a n - completeQuadraticGaussSum q a 0 / q) =
        quadraticResiduePhase q a n * quadraticChirpMul A f (δ * n) -
          (completeQuadraticGaussSum q a 0 / q) * quadraticChirpMul A f (δ * n) := by ring
  unfold centeredChirpSeries
  simp_rw [heq]
  rw [hquad.tsum_sub hmean, tsum_mul_left]

lemma integralCenteredChirpSeries_eq (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A : ℝ)
    {δ : ℝ} (hδ : δ ≠ 0) :
    integralCenteredChirpSeries f q a A δ = centeredChirpSeries f q a A δ +
      (completeQuadraticGaussSum q a 0 / q) *
        ((∑' n : ℤ, quadraticChirpMul A f (δ * n)) - (∫ x : ℝ, quadraticChirpMul A f (δ * x))) := by
  rw [centeredChirpSeries_eq_discrete_mean f q a A hδ, integralCenteredChirpSeries]
  ring

lemma norm_complete_quadratic_mean_le_one {q : ℕ} (hq : 0 < q) (a : ℤ) :
    ‖completeQuadraticGaussSum q a 0 / q‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast]
  exact (div_le_one₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
    (norm_completeQuadraticGaussSum_le q a 0)

theorem exists_integral_centering_error_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ), 0 < q → ∀ (a : ℤ) (A : ℝ), |A| ≤ 1 →
      ∀ δ : ℝ, 0 < δ →
        ‖integralCenteredChirpSeries f q a A δ - centeredChirpSeries f q a A δ‖ ≤ C * δ := by
  obtain ⟨C, hC, hquad⟩ := exists_uniform_chirp_quadrature_bound f
  refine ⟨C, hC, ?_⟩
  intro q hq a A hA δ hδ
  have heq : integralCenteredChirpSeries f q a A δ - centeredChirpSeries f q a A δ =
      (completeQuadraticGaussSum q a 0 / q) *
        ((∑' n : ℤ, quadraticChirpMul A f (δ * n)) - (∫ x : ℝ, quadraticChirpMul A f (δ * x))) := by
    rw [integralCenteredChirpSeries_eq f q a A hδ.ne']
    ring
  rw [heq, norm_mul]
  have h := mul_le_mul (norm_complete_quadratic_mean_le_one hq a) (hquad A hA δ hδ)
    (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using h

/-- The low-frequency smooth mean with its integral main term. -/
theorem exists_integral_centered_chirp_mean_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q M K : ℕ),
      let X := 2 * M * K
      let D := Nat.sqrt (Nat.sqrt X)
      a.Coprime q → 0 < q → 0 < K → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        ∀ δ : ℝ, 0 < δ → δ ≤ 1 → 1 / 2 ≤ δ * K → δ * K ≤ 2 →
          ∀ A : ℕ → ℝ, (∀ m ∈ Finset.Icc 1 M, |A m| ≤ 1) →
          (∑ m ∈ Finset.Icc 1 M, ‖integralCenteredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ‖) ≤
            C * M * Real.sqrt K * Real.log (X : ℝ) ^ O := by
  obtain ⟨C₀, hC₀, O, hO, hseries⟩ := exists_centered_chirp_series_mean_bound f
  obtain ⟨C₁, hC₁, herror⟩ := exists_integral_centering_error_bound f
  refine ⟨C₀ + C₁, by positivity, O, hO, ?_⟩
  intro a q M K
  dsimp only
  let X := 2 * M * K
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hK hD hqX hqD δ hδ hδone hlo hhi A hA
  have hmain := hseries a q M K haq hq hK hD hqX hqD δ hδ hlo hhi A hA
  have hpoint (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      ‖integralCenteredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ‖ ≤
        ‖centeredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ‖ + C₁ * δ := by
    have he := herror q hq ((a * m : ℕ) : ℤ) (A m) (hA m hm) δ hδ
    have ht := norm_sub_le (integralCenteredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ -
      centeredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ)
      (-centeredChirpSeries f q ((a * m : ℕ) : ℤ) (A m) δ)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at ht
    linarith
  let F := Real.log (X : ℝ) ^ O
  have hXthree : 3 ≤ X := hD.trans ((Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X))
  have hF : 1 ≤ F := one_le_pow₀ (one_le_log_nat_of_three_le hXthree)
  have hKsqrt : 1 ≤ Real.sqrt K := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ K by exact_mod_cast hK)
    simpa only [Real.sqrt_one] using h
  have hKF : 1 ≤ Real.sqrt K * F := one_le_mul_of_one_le_of_one_le hKsqrt hF
  have hextra : (M : ℝ) * (C₁ * δ) ≤ C₁ * M * Real.sqrt K * F := by
    calc
      _ ≤ (M : ℝ) * (C₁ * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδone hC₁) (Nat.cast_nonneg _)
      _ = C₁ * M := by ring
      _ ≤ (C₁ * M) * (Real.sqrt K * F) := le_mul_of_one_le_right (by positivity) hKF
      _ = _ := by ring
  apply (Finset.sum_le_sum hpoint).trans
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
  calc
    _ ≤ C₀ * M * Real.sqrt K * F + C₁ * M * Real.sqrt K * F := add_le_add hmain hextra
    _ = _ := by ring

lemma nearbyQuadraticRemainder_eq_integral_centered (f : 𝓢(ℝ, ℂ)) (q r v : ℕ) (b : ℤ)
    {L : ℝ} (hL : 0 < L) :
    nearbyQuadraticRemainder f q r v b L = integralCenteredChirpSeries f q ((r : ℤ) * b)
      (((r : ℝ) / (q * v)) * L ^ 2) L⁻¹ := by
  have heq (x : ℝ) : quadraticChirpMul (((r : ℝ) / (q * v)) * L ^ 2) f (L⁻¹ * x) =
      phase (((r : ℝ) / (q * v)) * x ^ 2) * f (L⁻¹ * x) := by
    rw [quadraticChirpMul_apply]
    congr 1
    congr 1
    field_simp
  unfold nearbyQuadraticRemainder integralCenteredChirpSeries
  simp_rw [heq]
  ring

/-- The nearby rational error in the low-frequency range, with the integral
main term and the natural `M * sqrt L` scale. -/
theorem exists_nearby_low_frequency_mean_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧ ∀ (a q v M K : ℕ),
      let X := 2 * M * K
      let D := Nat.sqrt (Nat.sqrt X)
      a.Coprime q → 0 < q → 0 < v → 0 < K → 3 ≤ D → q - 1 ≤ X → q * D ≤ X →
        ∀ L : ℝ, 1 ≤ L → 1 / 2 ≤ L⁻¹ * K → L⁻¹ * K ≤ 2 →
          (∀ m ∈ Finset.Icc 1 M, ((m : ℝ) / (q * v)) * L ^ 2 ≤ 1) →
          (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f q m v (a : ℤ) L‖) ≤
            C * M * Real.sqrt L * Real.log (X : ℝ) ^ O := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_integral_centered_chirp_mean_bound f
  refine ⟨2 * C, by positivity, O, hO, ?_⟩
  intro a q v M K
  dsimp only
  let X := 2 * M * K
  let D := Nat.sqrt (Nat.sqrt X)
  intro haq hq hv hK hD hqX hqD L hL hlo hhi hA
  have hLpos : 0 < L := by linarith
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hAabs : ∀ m ∈ Finset.Icc 1 M, |((m : ℝ) / (q * v)) * L ^ 2| ≤ 1 := by
    intro m hm
    rw [abs_of_nonneg (by positivity)]
    exact hA m hm
  have h := hmean a q M K haq hq hK hD hqX hqD L⁻¹ (inv_pos.mpr hLpos)
    ((inv_le_one₀ hLpos).mpr hL) hlo hhi (fun m => ((m : ℝ) / (q * v)) * L ^ 2) hAabs
  have hKL : (K : ℝ) ≤ 2 * L := by
    apply (div_le_iff₀ hLpos).mp
    simpa only [div_eq_mul_inv, mul_comm] using hhi
  have hroot : Real.sqrt K ≤ 2 * Real.sqrt L := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg K), mul_pow, Real.sq_sqrt hLpos.le]
    nlinarith
  have hXthree : 3 ≤ X := hD.trans ((Nat.sqrt_le_self (Nat.sqrt X)).trans (Nat.sqrt_le_self X))
  have hlog : 0 ≤ Real.log (X : ℝ) :=
    zero_le_one.trans (one_le_log_nat_of_three_le hXthree)
  have heq (m : ℕ) : nearbyQuadraticRemainder f q m v (a : ℤ) L =
      integralCenteredChirpSeries f q ((a * m : ℕ) : ℤ)
        (((m : ℝ) / (q * v)) * L ^ 2) L⁻¹ := by
    rw [nearbyQuadraticRemainder_eq_integral_centered f q m v (a : ℤ) hLpos]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  apply h.trans
  calc
    _ ≤ C * M * (2 * Real.sqrt L) * Real.log (X : ℝ) ^ O := by gcongr
    _ = _ := by ring

/-- Dividing the frequency and modulus by their common factor preserves the
nearby centered error, including its complete-period integral mean. -/
lemma nearbyQuadraticRemainder_mul (f : 𝓢(ℝ, ℂ)) {d q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (r v : ℕ) (b : ℤ) (L : ℝ) :
    nearbyQuadraticRemainder f (d * q) (d * r) v b L = nearbyQuadraticRemainder f q r v b L := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hβ : (((d * r : ℕ) : ℝ) / (((d * q : ℕ) : ℝ) * v)) = (r : ℝ) / (q * v) := by
    push_cast
    rw [show ((d : ℝ) * q) * v = d * (q * v) by ring]
    exact mul_div_mul_left _ _ hdR
  have hcoeff : ((d * r : ℕ) : ℤ) * b = (d : ℤ) * ((r : ℤ) * b) := by push_cast; ring
  have hphase (z : ℤ) : quadraticResiduePhase (d * q) (((d * r : ℕ) : ℤ) * b) z =
      quadraticResiduePhase q ((r : ℤ) * b) z := by
    rw [hcoeff]
    have h := exactQuadraticInterval_mul hd hq ((r : ℤ) * b) z 1
    simpa only [exactQuadraticInterval, Finset.range_one, Finset.sum_singleton,
      Nat.cast_zero, add_zero] using h
  have hG : completeQuadraticGaussSum (d * q) (((d * r : ℕ) : ℤ) * b) 0 =
      (d : ℂ) * completeQuadraticGaussSum q ((r : ℤ) * b) 0 := by
    rw [hcoeff]
    exact completeQuadraticGaussSum_mul hd hq ((r : ℤ) * b)
  unfold nearbyQuadraticRemainder
  simp_rw [hβ, hphase]
  rw [hG]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

end Erdos587
