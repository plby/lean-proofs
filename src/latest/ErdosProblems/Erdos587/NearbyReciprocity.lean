import ErdosProblems.Erdos587.GaussReciprocity
import ErdosProblems.Erdos587.ReciprocalPoisson

/-!
# The nearby rational main term after reciprocity

The exact Gauss--Fresnel formula is applied at the Fourier lattice points.
Both parity classes use the same reciprocal denominator `r`.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

noncomputable def nearbyFresnelConstant (q r v : ℕ) (b e : ℤ) (L : ℝ) : ℂ :=
  (q : ℂ)⁻¹ * ((L : ℂ) * fresnelPrefactor (((r : ℝ) / (q * v)) * L ^ 2)) *
    (completeQuadraticGaussSum q ((r : ℤ) * b) e *
      phase (((-(v : ℤ) * e ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)))

/-- A single parity-class Fourier term, including the exact scale and
the constant Gauss factor. -/
theorem gauss_fourier_quadratic_dilate_parity (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L)
    (b B inv j e : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) (2 * j + e) *
      𝓕 (quadraticChirpMul ((r : ℝ) / (q * v))
        (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))) (((2 * j + e : ℤ) : ℝ) / q) =
      nearbyFresnelConstant q r v b e L *
        (fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2)
          ((v : ℝ) / (r * L) * ((j : ℝ) + (e : ℝ) / 2)) *
        phase (((-(v : ℤ) * inv * (j ^ 2 + e * j) : ℤ) : ℝ) / r)) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hβ : 0 < (r : ℝ) / (q * v) := by positivity
  rw [fourier_quadratic_dilate f hL hβ]
  have hphase : -((((2 * j + e : ℤ) : ℝ) / q) ^ 2) / (4 * ((r : ℝ) / (q * v))) =
      (((-(v : ℤ) * (2 * j + e) ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ)) := by
    push_cast
    field_simp
  have hpoint : (((2 * j + e : ℤ) : ℝ) / q) / (2 * ((r : ℝ) / (q * v)) * L) =
      (v : ℝ) / (r * L) * ((j : ℝ) + (e : ℝ) / 2) := by
    push_cast
    field_simp
  rw [hphase, hpoint]
  have hrec := gauss_fresnel_reciprocity_parity hq hr b B (v : ℤ) inv j e hB hbv hinv
  calc
    _ = ((q : ℂ)⁻¹ * ((L : ℂ) * fresnelPrefactor (((r : ℝ) / (q * v)) * L ^ 2))) *
        (completeQuadraticGaussSum q ((r : ℤ) * b) (2 * j + e) *
          phase (((-(v : ℤ) * (2 * j + e) ^ 2 : ℤ) : ℝ) / ((4 * r * q : ℕ) : ℝ))) *
        fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2)
          ((v : ℝ) / (r * L) * ((j : ℝ) + (e : ℝ) / 2)) := by ring
    _ = _ := by rw [hrec]; unfold nearbyFresnelConstant; ring

/-- The combined Poisson, Fresnel, and Gauss prefactor has square-root size
`sqrt(v/r)`, uniformly in the modulus and in the parity representative. -/
theorem norm_nearbyFresnelConstant_le {q r v : ℕ} (hq : 0 < q) (hr : 0 < r) (hv : 0 < v)
    (b e : ℤ) {L : ℝ} (hL : 0 < L) (hunit : IsUnit (((r : ℤ) * b : ℤ) : ZMod q)) :
    ‖nearbyFresnelConstant q r v b e L‖ ≤ Real.sqrt ((v : ℝ) / r) := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  let β := (r : ℝ) / (q * v)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hnorm : ‖nearbyFresnelConstant q r v b e L‖ =
      (q : ℝ)⁻¹ * (1 / Real.sqrt (2 * β)) * ‖completeQuadraticGaussSum q ((r : ℤ) * b) e‖ := by
    unfold nearbyFresnelConstant
    rw [norm_mul, norm_mul, norm_scaled_fresnelPrefactor hL hβ]
    simp only [norm_inv, Complex.norm_natCast, norm_mul, norm_phase, mul_one]
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left
    (norm_completeQuadraticGaussSum_le_sqrt hq _ e hunit) (by positivity)).trans
  let x := (q : ℝ)⁻¹ * (1 / Real.sqrt (2 * β)) * Real.sqrt (2 * q)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hsquare : x ^ 2 = (v : ℝ) / r := by
    dsimp [x]
    rw [mul_pow, mul_pow, inv_pow, div_pow, one_pow,
      Real.sq_sqrt (by positivity : 0 ≤ 2 * β), Real.sq_sqrt (by positivity : 0 ≤ 2 * (q : ℝ))]
    dsimp [β]
    field_simp
  calc
    x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx).symm
    _ = Real.sqrt ((v : ℝ) / r) := congrArg Real.sqrt hsquare
    _ ≤ Real.sqrt ((v : ℝ) / r) := le_rfl

lemma tsum_int_even_add_odd {F : ℤ → ℂ} (hF : Summable F) :
    (∑' k : ℤ, F k) = (∑' n : ℤ, F (2 * n)) + ∑' n : ℤ, F (2 * n + 1) := by
  have h := tsum_int_eq_sum_residues (q := 2) hF
  simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat, zero_add, add_comm] using h

noncomputable def nearbyReciprocalSeries (f : 𝓢(ℝ, ℂ)) (q r v : ℕ) (L : ℝ) (inv e : ℤ) : ℂ :=
  ∑' n : ℤ, fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2)
      ((v : ℝ) / (r * L) * ((n : ℝ) + (e : ℝ) / 2)) *
    phase (((-(v : ℤ) * inv * (n ^ 2 + e * n) : ℤ) : ℝ) / r)

/-- Exact Poisson summation after reciprocity, with the two parity classes
and their possibly vanishing complete Gauss factors kept separate. -/
theorem poisson_nearby_reciprocal_series (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L)
    (b B inv : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    let g := quadraticChirpMul ((r : ℝ) / (q * v))
      (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))
    (∑' z : ℤ, quadraticResiduePhase q ((r : ℤ) * b) z * g z) =
      nearbyFresnelConstant q r v b 0 L * nearbyReciprocalSeries f q r v L inv 0 +
      nearbyFresnelConstant q r v b 1 L * nearbyReciprocalSeries f q r v L inv 1 := by
  dsimp only
  let g := quadraticChirpMul ((r : ℝ) / (q * v))
    (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))
  let F : ℤ → ℂ := fun k => (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) k *
    𝓕 g ((k : ℝ) / q)
  have hF : Summable F := by
    simpa only [F, mul_assoc] using (summable_gauss_fourier_lattice g hq ((r : ℤ) * b)).mul_left (q : ℂ)⁻¹
  have hpoisson : (∑' z : ℤ, quadraticResiduePhase q ((r : ℤ) * b) z * g z) = ∑' k, F k := by
    rw [poisson_quadratic_weight g hq]
    simp only [F, mul_assoc, tsum_mul_left]
  have hparity (e : ℤ) : (∑' n : ℤ, F (2 * n + e)) =
      nearbyFresnelConstant q r v b e L * nearbyReciprocalSeries f q r v L inv e := by
    unfold nearbyReciprocalSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    exact gauss_fourier_quadratic_dilate_parity f hq hr hv hL b B inv n e hB hbv hinv
  have heven : (∑' n : ℤ, F (2 * n)) =
      nearbyFresnelConstant q r v b 0 L * nearbyReciprocalSeries f q r v L inv 0 := by
    simpa only [add_zero] using hparity 0
  rw [hpoisson, tsum_int_even_add_odd hF, heven, hparity 1]

/-- The nearby main term is precisely the omitted zero dual frequency.
After subtraction, only the even-parity series loses its zero term. -/
theorem poisson_nearby_reciprocal_series_centered (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L)
    (b B inv : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    let g := quadraticChirpMul ((r : ℝ) / (q * v))
      (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))
    (∑' z : ℤ, quadraticResiduePhase q ((r : ℤ) * b) z * g z) -
        (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) 0 *
          (∫ x : ℝ, g x) =
      nearbyFresnelConstant q r v b 0 L *
        (nearbyReciprocalSeries f q r v L inv 0 -
          fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0) +
      nearbyFresnelConstant q r v b 1 L * nearbyReciprocalSeries f q r v L inv 1 := by
  dsimp only
  have hp := poisson_nearby_reciprocal_series f hq hr hv hL b B inv hB hbv hinv
  dsimp only at hp
  rw [hp]
  have hz := gauss_fourier_quadratic_dilate_parity f hq hr hv hL b B inv 0 0 hB hbv hinv
  simp only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0), Int.cast_zero, zero_div,
    phase_zero, mul_one] at hz
  rw [SchwartzMap.fourier_coe, fourier_zero_eq_integral] at hz
  rw [hz]
  ring

lemma isUnit_intCast_of_inverse_congruence {q : ℕ} (a B : ℤ)
    (hB : (q : ℤ) ∣ a * B - 1) : IsUnit (a : ZMod q) := by
  have hz := intCast_eq_zero_of_modulus_dvd (a * B - 1) hB
  have hmod : (a : ZMod q) * B = 1 := by
    apply sub_eq_zero.mp
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_one] using hz
  refine ⟨⟨(a : ZMod q), (B : ZMod q), hmod, ?_⟩, rfl⟩
  rwa [mul_comm]

/-- The smoothed rational quadratic sum minus its complete-period mean. -/
noncomputable def nearbyQuadraticRemainder (f : 𝓢(ℝ, ℂ)) (q r v : ℕ) (b : ℤ) (L : ℝ) : ℂ :=
  (∑' z : ℤ, quadraticResiduePhase q ((r : ℤ) * b) z *
      (phase (((r : ℝ) / (q * v)) * (z : ℝ) ^ 2) * f (L⁻¹ * z))) -
    (q : ℂ)⁻¹ * completeQuadraticGaussSum q ((r : ℤ) * b) 0 *
      (∫ x : ℝ, phase (((r : ℝ) / (q * v)) * x ^ 2) * f (L⁻¹ * x))

theorem nearbyQuadraticRemainder_eq (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L)
    (b B inv : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    nearbyQuadraticRemainder f q r v b L =
      nearbyFresnelConstant q r v b 0 L *
        (nearbyReciprocalSeries f q r v L inv 0 -
          fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0) +
      nearbyFresnelConstant q r v b 1 L * nearbyReciprocalSeries f q r v L inv 1 := by
  simpa only [quadraticChirpMul_apply, dilateSchwartz_apply, nearbyQuadraticRemainder] using
    poisson_nearby_reciprocal_series_centered f hq hr hv hL b B inv hB hbv hinv

theorem norm_nearbyQuadraticRemainder_le (f : 𝓢(ℝ, ℂ)) {q r v : ℕ}
    (hq : 0 < q) (hr : 0 < r) (hv : 0 < v) {L : ℝ} (hL : 0 < L)
    (b B inv : ℤ) (hB : (q : ℤ) ∣ (r : ℤ) * b * B - 1)
    (hbv : (q : ℤ) ∣ b * (v : ℤ) + 1)
    (hinv : (r : ℤ) ∣ (q : ℤ) * inv - 1) :
    ‖nearbyQuadraticRemainder f q r v b L‖ ≤ Real.sqrt ((v : ℝ) / r) *
      (‖nearbyReciprocalSeries f q r v L inv 0‖ + ‖nearbyReciprocalSeries f q r v L inv 1‖ +
        ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖) := by
  have hunit := isUnit_intCast_of_inverse_congruence ((r : ℤ) * b) B hB
  have hc₀ := norm_nearbyFresnelConstant_le hq hr hv b 0 hL hunit
  have hc₁ := norm_nearbyFresnelConstant_le hq hr hv b 1 hL hunit
  rw [nearbyQuadraticRemainder_eq f hq hr hv hL b B inv hB hbv hinv]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ Real.sqrt ((v : ℝ) / r) *
        (‖nearbyReciprocalSeries f q r v L inv 0‖ +
          ‖fresnelProfile f (((r : ℝ) / (q * v)) * L ^ 2) 0‖) +
        Real.sqrt ((v : ℝ) / r) * ‖nearbyReciprocalSeries f q r v L inv 1‖ := by
      exact add_le_add (mul_le_mul hc₀ (norm_sub_le _ _) (norm_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul_of_nonneg_right hc₁ (norm_nonneg _))
    _ = _ := by ring

end Erdos587
