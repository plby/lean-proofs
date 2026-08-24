import ErdosProblems.Erdos587.NearbyReciprocity
import ErdosProblems.Erdos587.FresnelSeries

/-!
# The small-dual-width range

When the reciprocal dual width is bounded, uniform quadratic decay of the
Fresnel profile bounds the centered series directly. This does not require
the reciprocal counting hypotheses or a dyadic interval of length at least three.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma nonzero_lattice_tail_le_of_decay (g : ℝ → ℂ) (M : ℝ) (_hM : 0 ≤ M)
    (hb : ∀ x, (1 + |x|) ^ 2 * ‖g x‖ ≤ M) {δ : ℝ} (hδ : 0 < δ) :
    (∑' n : ℤ, ‖if n = 0 then 0 else g (δ * n)‖) ≤
      (M * ∑' n : ℤ, 1 / (n : ℝ) ^ 2) / δ ^ 2 := by
  have hpoint (n : ℤ) : ‖if n = 0 then 0 else g (δ * n)‖ ≤
      (M / δ ^ 2) * (1 / (n : ℝ) ^ 2) := by
    by_cases hn : n = 0
    · simp [hn]
    rw [if_neg hn]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hh := hb (δ * n)
    have hsmall : (δ * (n : ℝ)) ^ 2 * ‖g (δ * n)‖ ≤ M := by
      apply le_trans _ hh
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith [abs_nonneg (δ * (n : ℝ)), sq_abs (δ * (n : ℝ))]
    calc
      _ ≤ M / (δ ^ 2 * (n : ℝ) ^ 2) := by
        apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hδ) (sq_pos_of_ne_zero hnR))).mpr
        nlinarith only [hsmall]
      _ = (M / δ ^ 2) * (1 / (n : ℝ) ^ 2) := by ring
  have hmajor : Summable (fun n : ℤ => (M / δ ^ 2) * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left _
  have hsum : Summable (fun n : ℤ => ‖if n = 0 then 0 else g (δ * n)‖) := by
    apply hmajor.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hpoint n
  apply (hsum.tsum_le_tsum hpoint hmajor).trans_eq
  rw [tsum_mul_left]
  ring

theorem exists_fresnel_nonzero_lattice_tail_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 1 ≤ A → ∀ δ : ℝ, 0 < δ →
      (∑' n : ℤ, ‖if n = 0 then 0 else fresnelProfile f A (δ * n)‖) ≤ C / δ ^ 2 := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_fresnelProfile_derivative_bound f 2 0
  refine ⟨M * ∑' n : ℤ, 1 / (n : ℝ) ^ 2, mul_nonneg hM (tsum_nonneg (fun n => by positivity)), ?_⟩
  intro A hA δ hδ
  apply nonzero_lattice_tail_le_of_decay _ M hM _ hδ
  intro x
  simpa only [iteratedDeriv_zero] using hb A hA x

/-- Fourier evaluation before arithmetic reciprocity. Its constant has the
same `sqrt(v/r)` norm bound for every dual frequency. -/
lemma gauss_fourier_quadratic_dilate_term (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L) (b k : ℤ) :
    (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) k *
      𝓕 (quadraticChirpMul ((r : ℝ) / (q * v))
        (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))) ((k : ℝ) / q) =
      nearbyFresnelConstant q r v b k L *
        fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2)
          (((v : ℝ) / (2 * r * L)) * k) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hβ : 0 < (r : ℝ) / (q * v) := by positivity
  rw [fourier_quadratic_dilate f hL hβ]
  have hphase : -(((k : ℝ) / q) ^ 2) / (4 * ((r : ℝ) / (q * v))) =
      (((-(v : ℤ) * k ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) := by
    push_cast
    field_simp
  have hpoint : ((k : ℝ) / q) / (2 * ((r : ℝ) / (q * v)) * L) =
      ((v : ℝ) / (2 * r * L)) * k := by field_simp
  rw [hphase, hpoint]
  unfold nearbyFresnelConstant
  ring

lemma norm_nearbyQuadraticRemainder_le_profile_tail (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L) (b : ℤ)
    (hunit : IsUnit (((r : ℤ) * b : ℤ) : ZMod q)) :
    ‖nearbyQuadraticRemainder f q r v b L‖ ≤ Real.sqrt ((v : ℝ) / r) *
      ∑' k : ℤ, ‖if k = 0 then 0 else
        fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) (((v : ℝ) / (2 * r * L)) * k)‖ := by
  let A := ((r : ℝ) / (q * v)) * L ^ 2
  let δ := (v : ℝ) / (2 * r * L)
  let W : ℤ → ℂ := fun k => if k = 0 then 0 else fresnelProfile f A (δ * k)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hprof : Summable (fun k : ℤ => fresnelProfile f A (δ * k)) := by
    simpa only [zero_add] using summable_fresnelProfile_affine f A 0 hδ.ne'
  have hWnorm : Summable (fun k => ‖W k‖) := by
    apply hprof.norm.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    dsimp [W]
    split_ifs <;> simp only [norm_zero, norm_nonneg, le_refl]
  let g := quadraticChirpMul ((r : ℝ) / (q * v))
    (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))
  have heq : nearbyQuadraticRemainder f q r v b L =
      ∑' k : ℤ, nearbyFresnelConstant q r v b k L * W k := by
    have hraw : nearbyQuadraticRemainder f q r v b L =
        (∑' z : ℤ, quadraticResiduePhase q ((r : ℤ) * b) z * g z) -
          (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) 0 * (∫ x : ℝ, g x) := by
      simp only [nearbyQuadraticRemainder, g, quadraticChirpMul_apply, dilateSchwartz_apply]
    rw [hraw, poisson_quadratic_weight_centered g hq, ← tsum_mul_left]
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · simp [hk, W]
    · simp only [W, if_neg hk]
      rw [← mul_assoc]
      exact gauss_fourier_quadratic_dilate_term f hq hr hv hL b k
  have hbound (k : ℤ) : ‖nearbyFresnelConstant q r v b k L * W k‖ ≤
      Real.sqrt ((v : ℝ) / r) * ‖W k‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_nearbyFresnelConstant_le hq hr hv b k hL hunit)
      (norm_nonneg _)
  have hmajor := hWnorm.mul_left (Real.sqrt ((v : ℝ) / r))
  have hsum : Summable (fun k => ‖nearbyFresnelConstant q r v b k L * W k‖) := by
    apply hmajor.of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hbound k
  rw [heq]
  apply (norm_tsum_le_tsum_norm hsum).trans
  apply (hsum.tsum_le_tsum hbound hmajor).trans_eq
  rw [tsum_mul_left]

lemma small_width_fresnel_scale_bound {δ L : ℝ} (hδ : 1 / 8 ≤ δ) (hL : 0 ≤ L) :
    Real.sqrt (2 * δ * L) / δ ^ 2 ≤ 32 * Real.sqrt L := by
  have hδpos : 0 < δ := by linarith
  have hpow : (1 / 8 : ℝ) ^ 3 ≤ δ ^ 3 := pow_le_pow_left₀ (by norm_num) hδ 3
  have hfactor : 2 ≤ 1024 * δ ^ 3 := by nlinarith only [hpow]
  have hmul := mul_le_mul_of_nonneg_right hfactor (mul_nonneg hδpos.le hL)
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow, Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hL]
  apply (div_le_iff₀ (by positivity : 0 < (δ ^ 2) ^ 2)).mpr
  nlinarith only [hmul]

/-- In the high-frequency range with bounded dual width, the centered error
is `O(sqrt L)` term by term. No reciprocal counting or interval-size condition
is needed in this range. -/
theorem exists_nearby_small_dual_width_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q r v : ℕ), 0 < q → 0 < r → 0 < v →
      ∀ (b : ℤ) (L : ℝ), 0 < L → IsUnit (((r : ℤ) * b : ℤ) : ZMod q) →
        1 ≤ ((r : ℝ) / (q * v)) * L ^ 2 → (r : ℝ) * L / v ≤ 4 →
        ‖nearbyQuadraticRemainder f q r v b L‖ ≤ C * Real.sqrt L := by
  obtain ⟨C, hC, htail⟩ := exists_fresnel_nonzero_lattice_tail_bound f
  refine ⟨32 * C + 1, by positivity, ?_⟩
  intro q r v hq hr hv b L hL hunit hA hwidth
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  let δ := (v : ℝ) / (2 * r * L)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδlo : 1 / 8 ≤ δ := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (r : ℝ) * L)).mpr
    have hh := (div_le_iff₀ hvR).mp hwidth
    linarith
  have hidentity : (v : ℝ) / r = 2 * δ * L := by dsimp [δ]; field_simp
  have ht := htail _ hA δ hδ
  apply (norm_nearbyQuadraticRemainder_le_profile_tail f hq hr hv hL b hunit).trans
  calc
    _ ≤ Real.sqrt ((v : ℝ) / r) * (C / δ ^ 2) :=
      mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
    _ = C * (Real.sqrt (2 * δ * L) / δ ^ 2) := by rw [hidentity]; ring
    _ ≤ C * (32 * Real.sqrt L) :=
      mul_le_mul_of_nonneg_left (small_width_fresnel_scale_bound hδlo hL.le) hC
    _ ≤ (32 * C + 1) * Real.sqrt L := by nlinarith [Real.sqrt_nonneg L]

end Erdos587
