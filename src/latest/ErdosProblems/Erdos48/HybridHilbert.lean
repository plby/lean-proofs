/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import BoundedGaps.BombieriVinogradov.Analytic.CosecantHilbert
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The real-frequency Hilbert inequality

The hybrid large sieve used in Gallagher's density estimate needs the
Montgomery--Vaughan Hilbert inequality for real (rather than circular)
frequencies.  The `BoundedGaps` dependency contains the sharp circular
cosecant inequality.  This file records the limiting bridge: after scaling
all real frequencies by `h`, multiplication by `pi * h` turns the cosecant
kernel into the reciprocal kernel as `h` tends to zero.
-/

open scoped BigOperators ComplexConjugate Topology
open Filter Metric

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

/-- The off-diagonal reciprocal kernel in the real-frequency Hilbert
inequality. -/
noncomputable def reciprocalBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ) : ℂ :=
  ∑ r, ∑ s ∈ Finset.univ.erase r,
    u r * star (u s) * (((x r - x s)⁻¹ : ℝ) : ℂ)

/-- A single scaled cosecant kernel converges to the corresponding
reciprocal kernel.  The punctured neighbourhood is used because the raw
cosecant expression has a pole at the scaling parameter `h = 0`. -/
theorem tendsto_scaled_cosecant_kernel {d : ℝ} (hd : d ≠ 0) :
    Tendsto (fun h : ℝ ↦
      (Real.pi * h) * (Real.sin (Real.pi * (h * d)))⁻¹)
      (𝓝[≠] 0) (𝓝 d⁻¹) := by
  have hsinc : Tendsto (fun h : ℝ ↦ Real.sinc (Real.pi * (h * d)))
      (𝓝[≠] 0) (𝓝 1) := by
    have harg : Tendsto (fun h : ℝ ↦ Real.pi * (h * d))
        (𝓝[≠] 0) (𝓝 0) := by
      have hid : Tendsto (fun h : ℝ ↦ h) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      simpa [mul_assoc] using (hid.const_mul Real.pi).mul_const d
    have hs := Real.continuous_sinc.continuousAt.tendsto.comp harg
    rw [Real.sinc_zero] at hs
    exact hs
  have hlim : Tendsto (fun h : ℝ ↦
      d⁻¹ * (Real.sinc (Real.pi * (h * d)))⁻¹)
      (𝓝[≠] 0) (𝓝 d⁻¹) := by
    simpa using (hsinc.inv₀ one_ne_zero).const_mul d⁻¹
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := hh
  have harg0 : Real.pi * (h * d) ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (mul_ne_zero hh0 hd)
  rw [Real.sinc_of_ne_zero harg0]
  field_simp

/-- The whole scaled finite cosecant form converges to the real reciprocal
form. -/
theorem tendsto_scaled_cosecantBilinearForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ)
    (hx : Function.Injective x) :
    Tendsto (fun h : ℝ ↦
      ((Real.pi * h : ℝ) : ℂ) *
        cosecantBilinearForm (fun r ↦ h * x r) u)
      (𝓝[≠] 0) (𝓝 (reciprocalBilinearForm x u)) := by
  unfold cosecantBilinearForm reciprocalBilinearForm
  simp_rw [Finset.mul_sum]
  apply tendsto_finsetSum
  intro r _
  apply tendsto_finsetSum
  intro s hs
  have hrs : r ≠ s := Ne.symm (Finset.ne_of_mem_erase hs)
  have hdiff : x r - x s ≠ 0 := sub_ne_zero.mpr (hx.ne hrs)
  have hk := tendsto_scaled_cosecant_kernel hdiff
  have hk' : Tendsto (fun h : ℝ ↦
      (((Real.pi * h) *
        (Real.sin (Real.pi * (h * (x r - x s))))⁻¹ : ℝ) : ℂ))
      (𝓝[≠] 0) (𝓝 (((x r - x s)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hk
  have hconst₁ : Tendsto (fun _ : ℝ ↦ u r) (𝓝[≠] 0) (𝓝 (u r)) :=
    tendsto_const_nhds
  have hconst₂ : Tendsto (fun _ : ℝ ↦ star (u s))
      (𝓝[≠] 0) (𝓝 (star (u s))) := tendsto_const_nhds
  have hmul := (hconst₁.mul hconst₂).mul hk'
  apply hmul.congr'
  filter_upwards with h
  rw [show h * x r - h * x s = h * (x r - x s) by ring]
  push_cast
  ring

/-- Montgomery--Vaughan's Hilbert inequality for a finite family of
separated real frequencies, obtained from the circular cosecant theorem by
letting the common scale tend to zero. -/
theorem norm_reciprocalBilinearForm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |x r - x s|)
    (u : ι → ℂ) :
    ‖reciprocalBilinearForm x u‖ ≤
      Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  have hx : Function.Injective x := by
    intro r s hrs
    by_contra hne
    have := hsep r s hne
    rw [hrs, sub_self, abs_zero] at this
    linarith
  let F : ℝ → ℂ := fun h ↦
    ((Real.pi * h : ℝ) : ℂ) *
      cosecantBilinearForm (fun r ↦ h * x r) u
  have hF : Tendsto F (𝓝[>] 0) (𝓝 (reciprocalBilinearForm x u)) := by
    exact (tendsto_scaled_cosecantBilinearForm x u hx).mono_left <| by
      apply nhdsWithin_mono
      intro h hh
      exact ne_of_gt hh
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ∀ r s : ι, |h * (x r - x s)| ≤ 1 / 2 := by
    apply Filter.eventually_all.mpr
    intro r
    apply Filter.eventually_all.mpr
    intro s
    have hlim : Tendsto (fun h : ℝ ↦ h * (x r - x s))
        (𝓝[>] 0) (𝓝 0) := by
      have hid : Tendsto (fun h : ℝ ↦ h) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left inf_le_left
      simpa using hid.mul_const (x r - x s)
    have hev := (Metric.tendsto_nhds.mp hlim) (1 / 2) (by norm_num)
    filter_upwards [hev] with h hh
    simpa [Real.dist_eq] using hh.le
  have hbound : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ‖F h‖ ≤ Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hhpos hhsmall
    have hh : 0 < h := hhpos
    have hcircle : ∀ r s, r ≠ s →
        h * δ ≤ dist ((h * x r : ℝ) : UnitAddCircle)
          ((h * x s : ℝ) : UnitAddCircle) := by
      intro r s hrs
      rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
      change h * δ ≤ ‖((h * x r - h * x s : ℝ) : UnitAddCircle)‖
      rw [(AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) one_ne_zero).2]
      · rw [show h * x r - h * x s = h * (x r - x s) by ring,
          abs_mul, abs_of_pos hh]
        exact mul_le_mul_of_nonneg_left (hsep r s hrs) hh.le
      · simpa [show h * x r - h * x s = h * (x r - x s) by ring]
          using hhsmall r s
    have hcsc := norm_cosecantBilinearForm_le
      (fun r ↦ h * x r) (mul_pos hh hδ) hcircle u
    change ‖((Real.pi * h : ℝ) : ℂ) *
        cosecantBilinearForm (fun r ↦ h * x r) u‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]
    calc
      (Real.pi * h) * ‖cosecantBilinearForm (fun r ↦ h * x r) u‖ ≤
          (Real.pi * h) * ((h * δ)⁻¹ * ∑ r, ‖u r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcsc (mul_nonneg Real.pi_pos.le hh.le)
      _ = Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
        field_simp
  exact le_of_tendsto hF.norm hbound

/-- A finite exponential sum with arbitrary real frequencies. -/
noncomputable def realFrequencyPolynomial
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (u : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ r, u r * Complex.exp (Complex.I * ((t * x r : ℝ) : ℂ))

theorem continuous_realFrequencyPolynomial
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (u : ι → ℂ) :
    Continuous (realFrequencyPolynomial x u) := by
  unfold realFrequencyPolynomial
  fun_prop

private theorem realFrequencyPolynomial_normSq_expand
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (u : ι → ℂ) (t : ℝ) :
    (((‖realFrequencyPolynomial x u t‖ ^ 2 : ℝ) : ℂ)) =
      ∑ r, ∑ s,
        u r * star (u s) *
          Complex.exp (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)) := by
  let P : ℂ := realFrequencyPolynomial x u t
  calc
    (((‖P‖ ^ 2 : ℝ) : ℂ)) = P * star P := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      simp only [Complex.star_def]
      ring
    _ = ∑ r, ∑ s,
        (u r * Complex.exp (Complex.I * ((t * x r : ℝ) : ℂ))) *
          star (u s * Complex.exp
            (Complex.I * ((t * x s : ℝ) : ℂ))) := by
      dsimp [P, realFrequencyPolynomial]
      simp only [map_sum]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [star_mul']
      simp only [Complex.star_def]
      rw [← Complex.exp_conj]
      push_cast
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      calc
        u r * Complex.exp (Complex.I * (t * x r)) *
            ((starRingEnd ℂ) (u s) *
              Complex.exp (-Complex.I * (t * x s))) =
            u r * (starRingEnd ℂ) (u s) *
              (Complex.exp (Complex.I * (t * x r)) *
                Complex.exp (-Complex.I * (t * x s))) := by
          ring
        _ = u r * (starRingEnd ℂ) (u s) *
              Complex.exp
                (Complex.I * (t * x r) +
                  (-Complex.I * (t * x s))) := by
          rw [Complex.exp_add]
        _ = _ := by
          congr 2
          ring

private theorem intervalIntegral_exp_imul_frequency
    {T d : ℝ} (hd : d ≠ 0) :
    (∫ t in (0 : ℝ)..T,
      Complex.exp (Complex.I * ((t * d : ℝ) : ℂ))) =
      (Complex.exp (Complex.I * ((T * d : ℝ) : ℂ)) - 1) *
        Complex.I⁻¹ * (((d : ℂ))⁻¹) := by
  have hc : Complex.I * (d : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hd)
  calc
    (∫ t in (0 : ℝ)..T,
        Complex.exp (Complex.I * ((t * d : ℝ) : ℂ))) =
        ∫ t in (0 : ℝ)..T,
          Complex.exp ((Complex.I * (d : ℂ)) * (t : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t _
      push_cast
      ring_nf
    _ = (Complex.exp ((Complex.I * (d : ℂ)) * (T : ℂ)) -
          Complex.exp ((Complex.I * (d : ℂ)) * (0 : ℂ))) /
          (Complex.I * (d : ℂ)) :=
      integral_exp_mul_complex hc
    _ = _ := by
      rw [mul_zero, Complex.exp_zero, div_eq_mul_inv, mul_inv_rev]
      push_cast
      ring_nf

private theorem reciprocalBilinearForm_phase_twist
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ) (T : ℝ) :
    reciprocalBilinearForm x
        (fun r ↦ u r *
          Complex.exp (Complex.I * ((T * x r : ℝ) : ℂ))) =
      ∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * star (u s) *
          Complex.exp
            (Complex.I * ((T * (x r - x s) : ℝ) : ℂ)) *
          (((x r - x s)⁻¹ : ℝ) : ℂ) := by
  unfold reciprocalBilinearForm
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  rw [star_mul']
  simp only [Complex.star_def]
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  calc
    (u r * Complex.exp (Complex.I * ((T * x r : ℝ) : ℂ))) *
        ((starRingEnd ℂ) (u s) *
          Complex.exp (-Complex.I * ((T * x s : ℝ) : ℂ))) *
        (((x r - x s)⁻¹ : ℝ) : ℂ) =
      u r * (starRingEnd ℂ) (u s) *
        (Complex.exp (Complex.I * ((T * x r : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * ((T * x s : ℝ) : ℂ))) *
        (((x r - x s)⁻¹ : ℝ) : ℂ) := by ring
    _ = u r * (starRingEnd ℂ) (u s) *
        Complex.exp
          (Complex.I * ((T * x r : ℝ) : ℂ) +
            -Complex.I * ((T * x s : ℝ) : ℂ)) *
        (((x r - x s)⁻¹ : ℝ) : ℂ) := by rw [Complex.exp_add]
    _ = _ := by
      congr 2
      congr 1
      push_cast
      ring

/-- Exact complex-valued mean-square expansion.  The diagonal is elementary;
the two endpoint terms are precisely reciprocal Hilbert forms. -/
theorem intervalIntegral_realFrequencyPolynomial_norm_sq_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ) (hx : Function.Injective x) (T : ℝ) :
    (∫ t in (0 : ℝ)..T,
        (((‖realFrequencyPolynomial x u t‖ ^ 2 : ℝ) : ℂ))) =
      ((T : ℂ) * ∑ r, ((‖u r‖ ^ 2 : ℝ) : ℂ)) +
        Complex.I⁻¹ *
          (reciprocalBilinearForm x
              (fun r ↦ u r *
                Complex.exp (Complex.I * ((T * x r : ℝ) : ℂ))) -
            reciprocalBilinearForm x u) := by
  calc
    (∫ t in (0 : ℝ)..T,
        (((‖realFrequencyPolynomial x u t‖ ^ 2 : ℝ) : ℂ))) =
        ∫ t in (0 : ℝ)..T, ∑ r, ∑ s,
          u r * star (u s) *
            Complex.exp (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t _
      exact realFrequencyPolynomial_normSq_expand x u t
    _ = ∑ r, ∑ s,
          u r * star (u s) *
            (∫ t in (0 : ℝ)..T,
              Complex.exp
                (Complex.I * ((t * (x r - x s) : ℝ) : ℂ))) := by
      rw [intervalIntegral.integral_finsetSum (fun r _ ↦
        (by fun_prop : Continuous (fun t : ℝ ↦ ∑ s,
          u r * star (u s) * Complex.exp
            (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)))).intervalIntegrable 0 T)]
      apply Finset.sum_congr rfl
      intro r _
      rw [intervalIntegral.integral_finsetSum (fun s _ ↦
        (by fun_prop : Continuous (fun t : ℝ ↦
          u r * star (u s) * Complex.exp
            (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)))).intervalIntegrable 0 T)]
      apply Finset.sum_congr rfl
      intro s _
      rw [intervalIntegral.integral_const_mul]
    _ = _ := by
      -- Separate the diagonal before applying the nonzero-frequency
      -- integral formula to every off-diagonal pair.
      calc
        (∑ r, ∑ s,
            u r * star (u s) *
              (∫ t in (0 : ℝ)..T,
                Complex.exp
                  (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)))) =
            ∑ r, (u r * star (u r) *
                (∫ t in (0 : ℝ)..T, (1 : ℂ)) +
              ∑ s ∈ Finset.univ.erase r,
                u r * star (u s) *
                  (∫ t in (0 : ℝ)..T,
                    Complex.exp
                      (Complex.I * ((t * (x r - x s) : ℝ) : ℂ)))) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [add_comm]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
          congr 1
          simp
        _ = ((T : ℂ) * ∑ r, ((‖u r‖ ^ 2 : ℝ) : ℂ)) +
            ∑ r, ∑ s ∈ Finset.univ.erase r,
              u r * star (u s) *
                ((Complex.exp
                    (Complex.I * ((T * (x r - x s) : ℝ) : ℂ)) - 1) *
                  Complex.I⁻¹ * (((x r - x s : ℝ) : ℂ))⁻¹) := by
          rw [Finset.sum_add_distrib]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r _
            rw [intervalIntegral.integral_const]
            simp only [sub_zero, Algebra.smul_def, mul_one]
            change u r * star (u r) * (T : ℂ) = _
            rw [← Complex.normSq_eq_norm_sq,
              Complex.normSq_eq_conj_mul_self]
            simp only [Complex.star_def]
            ring
          · apply Finset.sum_congr rfl
            intro r _
            apply Finset.sum_congr rfl
            intro s hs
            rw [intervalIntegral_exp_imul_frequency]
            exact sub_ne_zero.mpr (hx.ne
              (Ne.symm (Finset.ne_of_mem_erase hs)))
        _ = _ := by
          rw [reciprocalBilinearForm_phase_twist]
          unfold reciprocalBilinearForm
          simp only [sub_mul, mul_sub, Finset.sum_sub_distrib,
            Finset.mul_sum]
          simp only [mul_comm, mul_left_comm, mul_assoc]
          push_cast
          simp

/-- Continuous Montgomery--Vaughan mean-value theorem for a finite
Dirichlet polynomial with separated real frequencies. -/
theorem intervalIntegral_realFrequencyPolynomial_norm_sq_le
    {ι : Type*} [Fintype ι]
    (x : ι → ℝ) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r s, r ≠ s → δ ≤ |x r - x s|)
    (u : ι → ℂ) :
    (∫ t in (0 : ℝ)..T, ‖realFrequencyPolynomial x u t‖ ^ 2) ≤
      (T + 2 * Real.pi * δ⁻¹) * ∑ r, ‖u r‖ ^ 2 := by
  classical
  let E : ℝ := ∑ r, ‖u r‖ ^ 2
  let v : ι → ℂ := fun r ↦ u r *
    Complex.exp (Complex.I * ((T * x r : ℝ) : ℂ))
  have hx : Function.Injective x := by
    intro r s hrs
    by_contra hne
    have h := hsep r s hne
    rw [hrs, sub_self, abs_zero] at h
    linarith
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hvnorm (r : ι) : ‖v r‖ = ‖u r‖ := by
    dsimp [v]
    rw [norm_mul, Complex.norm_exp]
    simp
  have hvenergy : (∑ r, ‖v r‖ ^ 2) = E := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hvnorm]
  have hA : ‖reciprocalBilinearForm x v‖ ≤
      Real.pi * δ⁻¹ * E := by
    simpa only [hvenergy] using
      norm_reciprocalBilinearForm_le x hδ hsep v
  have hB : ‖reciprocalBilinearForm x u‖ ≤
      Real.pi * δ⁻¹ * E := by
    exact norm_reciprocalBilinearForm_le x hδ hsep u
  let I : ℝ := ∫ t in (0 : ℝ)..T,
    ‖realFrequencyPolynomial x u t‖ ^ 2
  have hI : 0 ≤ I := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    exact sq_nonneg _
  have hexact := intervalIntegral_realFrequencyPolynomial_norm_sq_eq
    x u hx T
  have hsumcast : (∑ r, ((‖u r‖ ^ 2 : ℝ) : ℂ)) = (E : ℂ) := by
    exact_mod_cast (show (∑ r, ‖u r‖ ^ 2) = E from rfl)
  rw [hsumcast] at hexact
  rw [intervalIntegral.integral_ofReal] at hexact
  change ((I : ℝ) : ℂ) = _ at hexact
  have hnorm := congrArg norm hexact
  rw [Complex.norm_real, Real.norm_of_nonneg hI] at hnorm
  calc
    I = ‖(T : ℂ) * (E : ℂ) +
        Complex.I⁻¹ *
          (reciprocalBilinearForm x v -
            reciprocalBilinearForm x u)‖ := by
      simpa only [v] using hnorm
    _ ≤ ‖(T : ℂ) * (E : ℂ)‖ +
        ‖Complex.I⁻¹ *
          (reciprocalBilinearForm x v -
            reciprocalBilinearForm x u)‖ := norm_add_le _ _
    _ = T * E +
        ‖reciprocalBilinearForm x v -
          reciprocalBilinearForm x u‖ := by
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_I,
        inv_one, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hT, Real.norm_of_nonneg hE]
    _ ≤ T * E +
        (‖reciprocalBilinearForm x v‖ +
          ‖reciprocalBilinearForm x u‖) :=
      add_le_add le_rfl (norm_sub_le _ _)
    _ ≤ T * E +
        (Real.pi * δ⁻¹ * E + Real.pi * δ⁻¹ * E) := by
      gcongr
    _ = (T + 2 * Real.pi * δ⁻¹) * E := by ring

end Erdos48
