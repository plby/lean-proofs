import ErdosProblems.Erdos587.HooleySignedChirpDecay
import ErdosProblems.Erdos587.HooleyShiftedLattice
import ErdosProblems.Erdos587.GaussReciprocity

/-!
# Smooth quadratic major arcs without a logarithmic loss

Poisson completion, the square-root Gauss bound, and the stationary-phase
envelope are combined with a shifted lattice sum. The real linear phase
is arbitrary; only the rational denominator and chirp scale are restricted.
-/

open MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap

namespace Erdos587

noncomputable def deltaLinearPhaseMul (θ : ℝ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => phase (θ * x)) f

lemma deltaLinearPhaseMul_apply (θ : ℝ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    deltaLinearPhaseMul θ f x = phase (θ * x) * f x := by
  simp only [deltaLinearPhaseMul, SchwartzMap.smulLeftCLM_apply_apply
    (hasTemperateGrowth_phase_comp (show (fun x : ℝ => θ * x).HasTemperateGrowth by fun_prop)),
    smul_eq_mul]

lemma delta_fourier_linearPhaseMul (θ ξ : ℝ) (f : 𝓢(ℝ, ℂ)) :
    𝓕 (deltaLinearPhaseMul θ f) ξ = 𝓕 f (ξ - θ) := by
  simp only [SchwartzMap.fourier_coe, fourier_eq_phase_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [deltaLinearPhaseMul_apply, ← mul_assoc, ← phase_add]
  congr 1
  congr 1
  ring

theorem delta_smooth_major_arc_norm_bound_of_decay (f : 𝓢(ℝ, ℂ))
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hdecay : ∀ A ξ : ℝ, ‖𝓕 (quadraticChirpMul A f) ξ‖ ≤
      C₀ / Real.sqrt (1 + |A|) / (1 + |ξ| / (1 + |A|)) ^ 2)
    (q : ℕ) (hq : 0 < q) (a : ℤ) (ha : IsUnit (a : ZMod q))
    (K A θ : ℝ) (hK : 0 < K) (hscale : (q : ℝ) * (1 + |A|) ≤ 4 * K) :
    ‖∑' n : ℤ, quadraticResiduePhase q a n *
      (phase (θ * n) * (phase (A * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n)))‖ ≤
        (41 * C₀) * K * Real.sqrt (2 * (q : ℝ)) /
          ((q : ℝ) * Real.sqrt (1 + |A|)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let H : ℝ := 1 + |A|
  have hH : 0 < H := by dsimp only [H]; positivity
  have hroot : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  let σ : ℝ := K / ((q : ℝ) * H)
  have hσ : (1 / 4 : ℝ) ≤ σ := by
    apply (le_div_iff₀ (mul_pos hqR hH)).mpr
    change (q : ℝ) * H ≤ 4 * K at hscale
    linarith
  obtain ⟨hkernel, hkernelBound⟩ := delta_shifted_lattice_decay_bound hσ ((q : ℝ) * θ)
  let w : 𝓢(ℝ, ℂ) := deltaLinearPhaseMul θ
    (dilateSchwartz (quadraticChirpMul A f) K⁻¹ (inv_ne_zero hK.ne'))
  have hfourier (ξ : ℝ) : 𝓕 w ξ = (K : ℂ) * 𝓕 (quadraticChirpMul A f) (K * (ξ - θ)) := by
    dsimp only [w]
    rw [delta_fourier_linearPhaseMul, fourier_dilateSchwartz]
    simp only [abs_inv, abs_of_pos hK, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, mul_comm K]
  let E : ℝ := Real.sqrt (2 * (q : ℝ)) * K * C₀ / Real.sqrt H
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hpoint (n : ℤ) :
      ‖completeQuadraticGaussSum q a n * 𝓕 w ((n : ℝ) / q)‖ ≤
        E * (1 / (1 + σ * |(n : ℝ) - (q : ℝ) * θ|) ^ 2) := by
    have harg : |K * ((n : ℝ) / q - θ)| / H = σ * |(n : ℝ) - (q : ℝ) * θ| := by
      rw [abs_mul, abs_of_pos hK]
      have heq : (n : ℝ) / q - θ = ((n : ℝ) - (q : ℝ) * θ) / q := by field_simp
      rw [heq, abs_div, abs_of_pos hqR]
      dsimp only [σ]
      ring_nf
    have hbound := hdecay A (K * ((n : ℝ) / q - θ))
    change ‖𝓕 (quadraticChirpMul A f) (K * ((n : ℝ) / q - θ))‖ ≤
      C₀ / Real.sqrt H / (1 + |K * ((n : ℝ) / q - θ)| / H) ^ 2 at hbound
    rw [harg] at hbound
    rw [norm_mul, hfourier, norm_mul, Complex.norm_real, Real.norm_of_nonneg hK.le]
    calc
      _ ≤ Real.sqrt (2 * (q : ℝ)) *
          (K * (C₀ / Real.sqrt H / (1 + σ * |(n : ℝ) - (q : ℝ) * θ|) ^ 2)) :=
        mul_le_mul (norm_completeQuadraticGaussSum_le_sqrt hq a n ha)
          (mul_le_mul_of_nonneg_left hbound hK.le) (by positivity) (by positivity)
      _ = _ := by dsimp only [E]; ring
  have hnormsum := (summable_gauss_fourier_lattice w hq a).norm
  have hsumBound : (∑' n : ℤ, ‖completeQuadraticGaussSum q a n * 𝓕 w ((n : ℝ) / q)‖) ≤ E * 41 := by
    calc
      _ ≤ ∑' n : ℤ, E * (1 / (1 + σ * |(n : ℝ) - (q : ℝ) * θ|) ^ 2) :=
        hnormsum.tsum_le_tsum hpoint (hkernel.mul_left E)
      _ = E * ∑' n : ℤ, 1 / (1 + σ * |(n : ℝ) - (q : ℝ) * θ|) ^ 2 := tsum_mul_left
      _ ≤ E * 41 := mul_le_mul_of_nonneg_left hkernelBound hE
  have hweight (n : ℤ) : w n =
      phase (θ * n) * (phase (A * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n)) := by
    simp only [w, deltaLinearPhaseMul_apply, dilateSchwartz_apply, quadraticChirpMul_apply]
  calc
    _ = ‖∑' n : ℤ, quadraticResiduePhase q a n * w n‖ := by simp only [hweight]
    _ = ‖(q : ℂ)⁻¹ * ∑' n : ℤ, completeQuadraticGaussSum q a n * 𝓕 w ((n : ℝ) / q)‖ := by
      rw [poisson_quadratic_weight w hq a]
    _ ≤ (q : ℝ)⁻¹ * (E * 41) := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left
        ((norm_tsum_le_tsum_norm hnormsum).trans hsumBound) (by positivity)
    _ = _ := by dsimp only [E, H]; ring

theorem exists_delta_smooth_major_arc_norm_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ, IsUnit (a : ZMod q) →
      ∀ K A θ : ℝ, 0 < K → (q : ℝ) * (1 + |A|) ≤ 4 * K →
      ‖∑' n : ℤ, quadraticResiduePhase q a n *
        (phase (θ * n) * (phase (A * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n)))‖ ≤
          C * K * Real.sqrt (2 * (q : ℝ)) / ((q : ℝ) * Real.sqrt (1 + |A|)) := by
  obtain ⟨C₀, hC₀, hdecay⟩ := exists_delta_chirp_fourier_decay f
  exact ⟨41 * C₀, by positivity, delta_smooth_major_arc_norm_bound_of_decay f hC₀ hdecay⟩

theorem delta_smooth_major_arc_sq_bound_of_norm (f : 𝓢(ℝ, ℂ))
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hbound : ∀ q : ℕ, 0 < q → ∀ a : ℤ, IsUnit (a : ZMod q) →
      ∀ K A θ : ℝ, 0 < K → (q : ℝ) * (1 + |A|) ≤ 4 * K →
      ‖∑' n : ℤ, quadraticResiduePhase q a n *
        (phase (θ * n) * (phase (A * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n)))‖ ≤
          C₀ * K * Real.sqrt (2 * (q : ℝ)) / ((q : ℝ) * Real.sqrt (1 + |A|)))
    (q : ℕ) (hq : 0 < q) (a : ℤ) (ha : IsUnit (a : ZMod q))
    (K β θ : ℝ) (hK : 0 < K) (hqK : (q : ℝ) ≤ K)
    (hβ : |β| ≤ 2 / ((q : ℝ) * K)) :
    ‖∑' n : ℤ, phase ((((a : ℝ) / q + β) * (n : ℝ) ^ 2) + θ * n) * f (K⁻¹ * n)‖ ^ 2 ≤
      (2 * C₀ ^ 2) * K ^ 2 / ((q : ℝ) * (1 + K ^ 2 * |β|)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hchirp : |β * K ^ 2| = K ^ 2 * |β| := by
    rw [abs_mul, abs_pow, abs_of_pos hK, mul_comm]
  have hscale : (q : ℝ) * (1 + |β * K ^ 2|) ≤ 4 * K := by
    have hmul := mul_le_mul_of_nonneg_right ((le_div_iff₀ (mul_pos hqR hK)).mp hβ) hK.le
    rw [hchirp]
    nlinarith
  have h := hbound q hq a ha K (β * K ^ 2) θ hK hscale
  have hpoint (n : ℤ) : quadraticResiduePhase q a n *
      (phase (θ * n) * (phase ((β * K ^ 2) * (K⁻¹ * n) ^ 2) * f (K⁻¹ * n))) =
        phase ((((a : ℝ) / q + β) * (n : ℝ) ^ 2) + θ * n) * f (K⁻¹ * n) := by
    simp only [quadraticResiduePhase, ← mul_assoc, ← phase_add]
    congr 1
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hpoint] at h
  rw [hchirp] at h
  have hH : 0 < 1 + K ^ 2 * |β| := by positivity
  calc
    _ ≤ (C₀ * K * Real.sqrt (2 * (q : ℝ)) / ((q : ℝ) * Real.sqrt (1 + K ^ 2 * |β|))) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
    _ = C₀ ^ 2 * K ^ 2 * (Real.sqrt (2 * (q : ℝ))) ^ 2 /
        ((q : ℝ) ^ 2 * (Real.sqrt (1 + K ^ 2 * |β|)) ^ 2) := by ring
    _ = _ := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * (q : ℝ)), Real.sq_sqrt hH.le]
      field_simp

theorem exists_delta_smooth_major_arc_sq_bound (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 0 < q → ∀ a : ℤ, IsUnit (a : ZMod q) →
      ∀ K β θ : ℝ, 0 < K → (q : ℝ) ≤ K → |β| ≤ 2 / ((q : ℝ) * K) →
      ‖∑' n : ℤ, phase ((((a : ℝ) / q + β) * (n : ℝ) ^ 2) + θ * n) * f (K⁻¹ * n)‖ ^ 2 ≤
        C * K ^ 2 / ((q : ℝ) * (1 + K ^ 2 * |β|)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_delta_smooth_major_arc_norm_bound f
  exact ⟨2 * C₀ ^ 2, by positivity, delta_smooth_major_arc_sq_bound_of_norm f hC₀ hbound⟩

end Erdos587
