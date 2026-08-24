import ErdosProblems.Erdos587.Fresnel

/-!
# Poisson summation for the reciprocal quadratic transform

The scaled identity is stated in the same phase convention as the Gauss
sums and the Fresnel profile.
-/

open MeasureTheory
open scoped FourierTransform SchwartzMap

namespace Erdos587

lemma fourier_eq_phase_integral (f : ℝ → ℂ) (t : ℝ) :
    𝓕 f t = ∫ x : ℝ, phase (-t * x) * f x := by
  rw [Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with x
  change phase (-(t * x)) * f x = phase (-t * x) * f x
  rw [neg_mul]

/-- Fourier scaling with the exact absolute Jacobian. -/
lemma fourier_comp_mul (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    𝓕 (fun x : ℝ => f (a * x)) t = ((|a| : ℝ) : ℂ)⁻¹ * 𝓕 f (t / a) := by
  rw [fourier_eq_phase_integral, fourier_eq_phase_integral]
  let g : ℝ → ℂ := fun x => phase (-(t / a) * x) * f x
  have hphase (x : ℝ) : phase (-(t / a) * (a * x)) = phase (-t * x) := by
    congr 1
    field_simp
  calc
    (∫ x : ℝ, phase (-t * x) * f (a * x)) = ∫ x : ℝ, g (a * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [g]
      rw [hphase]
    _ = |a⁻¹| • ∫ x : ℝ, g x := Measure.integral_comp_mul_left g a
    _ = ((|a| : ℝ) : ℂ)⁻¹ * ∫ x : ℝ, phase (-(t / a) * x) * f x := by
      simp only [g, abs_inv, Complex.real_smul, Complex.ofReal_inv]

/-- Nonzero dilation preserves the Schwartz class. -/
noncomputable def dilateSchwartz (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ ℝ a ha).toContinuousLinearEquiv f

lemma dilateSchwartz_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    dilateSchwartz f a ha x = f (a * x) := rfl

lemma fourier_dilateSchwartz (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    𝓕 (dilateSchwartz f a ha) t = ((|a| : ℝ) : ℂ)⁻¹ * 𝓕 f (t / a) := by
  rw [SchwartzMap.fourier_coe]
  exact fourier_comp_mul f ha t

lemma unitCircle_fourier_eq_phase (n : ℤ) (x : ℝ) :
    _root_.fourier n (x : UnitAddCircle) = phase ((n : ℝ) * x) := by
  rw [_root_.fourier_coe_apply]
  simp only [phase, Real.fourierChar_apply, Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

/-- Poisson summation along any positive-spacing arithmetic progression. -/
theorem poisson_arithmetic_progression (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    (∑' n : ℤ, f (x + a * n)) =
      (a : ℂ)⁻¹ * ∑' k : ℤ, phase ((k : ℝ) * x / a) * 𝓕 f ((k : ℝ) / a) := by
  have h := (dilateSchwartz f a ha.ne').tsum_eq_tsum_fourier (x / a)
  simp_rw [dilateSchwartz_apply, fourier_dilateSchwartz, unitCircle_fourier_eq_phase,
    abs_of_pos ha] at h
  have harg (n : ℤ) : a * (x / a + n) = x + a * n := by field_simp
  have hphase (k : ℤ) : phase ((k : ℝ) * (x / a)) = phase ((k : ℝ) * x / a) := by
    congr 1
    ring
  simp_rw [harg, hphase] at h
  calc
    (∑' n : ℤ, f (x + a * n)) =
        ∑' k : ℤ, ((a : ℂ)⁻¹ * 𝓕 f ((k : ℝ) / a)) * phase ((k : ℝ) * x / a) := h
    _ = (a : ℂ)⁻¹ * ∑' k : ℤ, phase ((k : ℝ) * x / a) * 𝓕 f ((k : ℝ) / a) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      ring

/-- Splitting an absolutely convergent integer sum into residue classes. -/
lemma tsum_int_eq_sum_residues {q : ℕ} [NeZero q] {F : ℤ → ℂ} (hF : Summable F) :
    (∑' z : ℤ, F z) = ∑ r : Fin q, ∑' z : ℤ, F ((r : ℕ) + q * z) := by
  let e : ℤ ≃ Fin q × ℤ := (Int.divModEquiv q).trans (Equiv.prodComm _ _)
  have he : Summable (fun p : Fin q × ℤ => F (e.symm p)) := hF.comp_injective e.symm.injective
  calc
    (∑' z : ℤ, F z) = ∑' p : Fin q × ℤ, F (e.symm p) := (e.symm.tsum_eq F).symm
    _ = ∑' r : Fin q, ∑' z : ℤ, F (e.symm (r, z)) := he.tsum_prod
    _ = ∑ r : Fin q, ∑' z : ℤ, F ((r : ℕ) + q * z) := by
      simp [e, Int.divModEquiv_symm_apply, add_comm, mul_comm]

lemma summable_schwartz_int (f : 𝓢(ℝ, ℂ)) : Summable (fun n : ℤ => f n) := by
  exact summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

lemma summable_schwartz_int_mul_phase (f : 𝓢(ℝ, ℂ)) (θ : ℤ → ℝ) :
    Summable (fun n : ℤ => phase (θ n) * f n) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_phase, one_mul] using (summable_schwartz_int f).norm

lemma summable_fourier_lattice_phase (f : 𝓢(ℝ, ℂ)) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    Summable (fun k : ℤ => phase ((k : ℝ) * x / a) * 𝓕 f ((k : ℝ) / a)) := by
  have h := summable_schwartz_int_mul_phase
    (dilateSchwartz (𝓕 f) a⁻¹ (inv_ne_zero ha)) (fun k => (k : ℝ) * x / a)
  simpa only [dilateSchwartz_apply, div_eq_mul_inv, mul_comm a⁻¹] using h

noncomputable def periodicFourierSum (Φ : ℤ → ℂ) (q : ℕ) (k : ℤ) : ℂ :=
  ∑ r : Fin q, Φ (r : ℕ) * phase ((k : ℝ) * (r : ℕ) / q)

/-- Poisson summation with a periodic arithmetic weight. Its finite Fourier
sum becomes the complete Gauss sum for a quadratic weight. -/
theorem poisson_periodic_weight (f : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q) (Φ : ℤ → ℂ)
    (hΦ : ∀ r : Fin q, ∀ z : ℤ, Φ ((r : ℕ) + q * z) = Φ (r : ℕ))
    (hsum : Summable (fun z : ℤ => Φ z * f z)) :
    (∑' z : ℤ, Φ z * f z) =
      (q : ℂ)⁻¹ * ∑' k : ℤ, periodicFourierSum Φ q k * 𝓕 f ((k : ℝ) / q) := by
  let : NeZero q := ⟨hq.ne'⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hres (r : Fin q) :
      (∑' z : ℤ, Φ ((r : ℕ) + q * z) * f (((r : ℕ) + q * z : ℤ) : ℝ)) =
        Φ (r : ℕ) * (q : ℂ)⁻¹ *
          ∑' k : ℤ, phase ((k : ℝ) * (r : ℕ) / q) * 𝓕 f ((k : ℝ) / q) := by
    simp_rw [hΦ, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [tsum_mul_left, poisson_arithmetic_progression f hqR (r : ℕ)]
    push_cast
    ring
  have hs (r : Fin q) : Summable (fun k : ℤ =>
      (Φ (r : ℕ) * phase ((k : ℝ) * (r : ℕ) / q)) * 𝓕 f ((k : ℝ) / q)) := by
    simpa only [mul_assoc] using
      (summable_fourier_lattice_phase f hqR.ne' (r : ℕ)).mul_left (Φ (r : ℕ))
  rw [tsum_int_eq_sum_residues (q := q) hsum]
  simp_rw [hres]
  calc
    (∑ r : Fin q, Φ (r : ℕ) * (q : ℂ)⁻¹ *
        ∑' k : ℤ, phase ((k : ℝ) * (r : ℕ) / q) * 𝓕 f ((k : ℝ) / q)) =
      (q : ℂ)⁻¹ * ∑ r : Fin q, ∑' k : ℤ,
        (Φ (r : ℕ) * phase ((k : ℝ) * (r : ℕ) / q)) * 𝓕 f ((k : ℝ) / q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      simp_rw [mul_assoc]
      rw [tsum_mul_left]
      ring
    _ = (q : ℂ)⁻¹ * ∑' k : ℤ, ∑ r : Fin q,
        (Φ (r : ℕ) * phase ((k : ℝ) * (r : ℕ) / q)) * 𝓕 f ((k : ℝ) / q) := by
      congr 1
      exact (Summable.tsum_finsetSum (s := Finset.univ) (fun r _ => hs r)).symm
    _ = (q : ℂ)⁻¹ * ∑' k : ℤ, periodicFourierSum Φ q k * 𝓕 f ((k : ℝ) / q) := by
      congr 1
      apply tsum_congr
      intro k
      rw [← Finset.sum_mul]
      rfl

noncomputable def quadraticResiduePhase (q : ℕ) (a z : ℤ) : ℂ :=
  phase (((a * z ^ 2 : ℤ) : ℝ) / q)

noncomputable def completeQuadraticGaussSum (q : ℕ) (a k : ℤ) : ℂ :=
  ∑ r : Fin q, phase (((a * (r : ℕ) ^ 2 + k * (r : ℕ) : ℤ) : ℝ) / q)

lemma quadraticResiduePhase_periodic {q : ℕ} (hq : 0 < q) (a : ℤ) (r : Fin q) (z : ℤ) :
    quadraticResiduePhase q a ((r : ℕ) + q * z) = quadraticResiduePhase q a (r : ℕ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have heq : (((a * ((r : ℕ) + q * z) ^ 2 : ℤ) : ℝ) / q) =
      (((a * (r : ℕ) ^ 2 : ℤ) : ℝ) / q) +
        ((a * (2 * (r : ℕ) * z + q * z ^ 2) : ℤ) : ℝ) := by
    push_cast
    field_simp
    ring
  unfold quadraticResiduePhase
  rw [heq, phase_add]
  have hphase : phase ((a * (2 * (r : ℕ) * z + q * z ^ 2) : ℤ) : ℝ) = 1 :=
    fourierChar_intCast _
  rw [hphase, mul_one]

lemma periodicFourierSum_quadratic (q : ℕ) (a k : ℤ) :
    periodicFourierSum (quadraticResiduePhase q a) q k = completeQuadraticGaussSum q a k := by
  unfold periodicFourierSum completeQuadraticGaussSum quadraticResiduePhase
  apply Finset.sum_congr rfl
  intro r hr
  rw [← phase_add]
  congr 1
  push_cast
  ring

/-- Exact Poisson formula for a quadratic residue phase with an arbitrary
Schwartz weight. The zero Fourier mode is included in this identity. -/
theorem poisson_quadratic_weight (f : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q) (a : ℤ) :
    (∑' z : ℤ, quadraticResiduePhase q a z * f z) =
      (q : ℂ)⁻¹ * ∑' k : ℤ, completeQuadraticGaussSum q a k * 𝓕 f ((k : ℝ) / q) := by
  have hsum : Summable (fun z : ℤ => quadraticResiduePhase q a z * f z) :=
    summable_schwartz_int_mul_phase f (fun z => ((a * z ^ 2 : ℤ) : ℝ) / q)
  have h := poisson_periodic_weight f hq (quadraticResiduePhase q a)
    (quadraticResiduePhase_periodic hq a) hsum
  simpa only [periodicFourierSum_quadratic] using h

lemma norm_completeQuadraticGaussSum_le (q : ℕ) (a k : ℤ) :
    ‖completeQuadraticGaussSum q a k‖ ≤ q := by
  unfold completeQuadraticGaussSum
  calc
    ‖∑ r : Fin q, phase (((a * (r : ℕ) ^ 2 + k * (r : ℕ) : ℤ) : ℝ) / q)‖ ≤
        ∑ r : Fin q, ‖phase (((a * (r : ℕ) ^ 2 + k * (r : ℕ) : ℤ) : ℝ) / q)‖ :=
      norm_sum_le _ _
    _ = q := by simp only [norm_phase, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]

lemma summable_gauss_fourier_lattice (f : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q) (a : ℤ) :
    Summable (fun k : ℤ => completeQuadraticGaussSum q a k * 𝓕 f ((k : ℝ) / q)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs : Summable (fun k : ℤ => 𝓕 f ((k : ℝ) / q)) := by
    simpa only [mul_zero, zero_div, phase_zero, one_mul] using
      summable_fourier_lattice_phase f hqR 0
  apply Summable.of_norm_bounded (hs.norm.mul_left (q : ℝ))
  intro k
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_completeQuadraticGaussSum_le q a k) (norm_nonneg _)

lemma fourier_zero_eq_integral (f : ℝ → ℂ) : 𝓕 f 0 = ∫ x : ℝ, f x := by
  rw [fourier_eq_phase_integral]
  simp only [neg_zero, zero_mul, phase_zero, one_mul]

/-- Exact centered quadratic Poisson identity, with the complete zero-mode
mean explicitly subtracted rather than estimated as an error. -/
theorem poisson_quadratic_weight_centered (f : 𝓢(ℝ, ℂ)) {q : ℕ} (hq : 0 < q) (a : ℤ) :
    (∑' z : ℤ, quadraticResiduePhase q a z * f z) -
      (q : ℂ)⁻¹ * completeQuadraticGaussSum q a 0 * (∫ x : ℝ, f x) =
      (q : ℂ)⁻¹ * ∑' k : ℤ, if k = 0 then 0 else
        completeQuadraticGaussSum q a k * 𝓕 f ((k : ℝ) / q) := by
  have hsplit := (summable_gauss_fourier_lattice f hq a).tsum_eq_add_tsum_ite (0 : ℤ)
  rw [poisson_quadratic_weight f hq a, hsplit]
  simp only [Int.cast_zero, zero_div, SchwartzMap.fourier_coe, fourier_zero_eq_integral]
  ring

/-- Fourier transform of a quadratically modulated Schwartz weight. -/
theorem fourier_quadraticChirpMul (f : 𝓢(ℝ, ℂ)) {A : ℝ} (hA : 0 < A) (k : ℝ) :
    𝓕 (quadraticChirpMul A f) k =
      fresnelPrefactor A * phase (-(k ^ 2) / (4 * A)) * fresnelProfile f A (k / (2 * A)) := by
  rw [SchwartzMap.fourier_coe, fourier_eq_phase_integral]
  have heq : (∫ x : ℝ, phase (-k * x) * quadraticChirpMul A f x) =
      ∫ x : ℝ, f x * phase (A * x ^ 2 - k * x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [quadraticChirpMul_apply, ← mul_assoc, ← phase_add]
    have harg : -k * x + A * x ^ 2 = A * x ^ 2 - k * x := by ring
    rw [harg, mul_comm]
  rw [heq]
  exact fresnel_identity_phase f.integrable (𝓕 f).integrable f.continuous hA k

lemma quadraticChirpMul_dilate (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : L ≠ 0) (β : ℝ) :
    quadraticChirpMul β (dilateSchwartz f L⁻¹ (inv_ne_zero hL)) =
      dilateSchwartz (quadraticChirpMul (β * L ^ 2) f) L⁻¹ (inv_ne_zero hL) := by
  ext x
  simp only [quadraticChirpMul_apply, dilateSchwartz_apply]
  have harg : β * x ^ 2 = (β * L ^ 2) * (L⁻¹ * x) ^ 2 := by field_simp
  rw [harg]

/-- Scale-aware Fresnel transform. The profile parameter is `β*L^2`, which
is at least one precisely in the high-frequency branch of the argument. -/
theorem fourier_quadratic_dilate (f : 𝓢(ℝ, ℂ)) {L β : ℝ}
    (hL : 0 < L) (hβ : 0 < β) (k : ℝ) :
    𝓕 (quadraticChirpMul β (dilateSchwartz f L⁻¹ (inv_ne_zero hL.ne'))) k =
      (L : ℂ) * fresnelPrefactor (β * L ^ 2) * phase (-(k ^ 2) / (4 * β)) *
        fresnelProfile f (β * L ^ 2) (k / (2 * β * L)) := by
  rw [quadraticChirpMul_dilate f hL.ne', fourier_dilateSchwartz,
    fourier_quadraticChirpMul f (mul_pos hβ (pow_pos hL 2))]
  simp only [abs_inv, abs_of_pos hL, Complex.ofReal_inv, inv_inv, div_inv_eq_mul]
  have harg : -((k * L) ^ 2) / (4 * (β * L ^ 2)) = -(k ^ 2) / (4 * β) := by
    field_simp
  have hpoint : k * L / (2 * (β * L ^ 2)) = k / (2 * β * L) := by
    field_simp
  rw [harg, hpoint]
  ring

lemma norm_scaled_fresnelPrefactor {L β : ℝ} (hL : 0 < L) (hβ : 0 < β) :
    ‖(L : ℂ) * fresnelPrefactor (β * L ^ 2)‖ = 1 / Real.sqrt (2 * β) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
    norm_fresnelPrefactor (mul_pos hβ (pow_pos hL 2))]
  have hsqrt : Real.sqrt (2 * (β * L ^ 2)) = Real.sqrt (2 * β) * L := by
    rw [show 2 * (β * L ^ 2) = (2 * β) * L ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hL]
  rw [hsqrt]
  field_simp

end Erdos587
