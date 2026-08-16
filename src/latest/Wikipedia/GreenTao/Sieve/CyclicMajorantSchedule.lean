import Wikipedia.GreenTao.Parameters
import Wikipedia.GreenTao.Sieve.CFZCanonicalCyclicBoundaryLimit

/-!
# The Green--Tao cyclic-majorant scale

This file verifies that the concrete sieve level chosen in
`GreenTao.Parameters` has enough power saving for the complete cyclic
boundary estimate.  The calculation is independent of all Fourier and
residue parameters.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real Topology

/-- The ambient CFZ family has exactly the coarse cardinality used when the
Green--Tao sieve exponent was chosen. -/
theorem card_CFZFormIndex_eq_maxAPForms (k : ℕ) :
    Fintype.card (CFZFormIndex k) = maxAPForms k := by
  simp [CFZFormIndex, DeletedCube, maxAPForms]

/-- The boundary power uses exactly one twentieth of the ambient modulus
power available in the chosen sieve scale. -/
theorem sieveExponent_mul_cfzCanonicalCyclicBoundaryExponent
    {k : ℕ} (hk : 3 ≤ k) :
    sieveExponent k *
        (cfzCanonicalCyclicBoundaryExponent k : ℝ) =
      1 / 20 := by
  have hforms : (maxAPForms k : ℝ) ≠ 0 := by
    exact_mod_cast (maxAPForms_pos hk).ne'
  rw [sieveExponent, cfzCanonicalCyclicBoundaryExponent,
    card_CFZFormIndex_eq_maxAPForms]
  push_cast
  field_simp [hforms]
  ring

/-- The concrete Green--Tao sieve level has more than enough power saving
for the complete cyclic-to-Euler boundary. -/
theorem tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun N : ℕ =>
        (sieveLevel k N : ℝ) ^
            cfzCanonicalCyclicBoundaryExponent k /
          (N : ℝ))
      atTop (𝓝 0) := by
  let A := cfzCanonicalCyclicBoundaryExponent k
  have hgap :
      0 < 1 - sieveExponent k * (A : ℝ) := by
    rw [show sieveExponent k * (A : ℝ) = 1 / 20 by
      exact sieveExponent_mul_cfzCanonicalCyclicBoundaryExponent hk]
    norm_num
  have hmodel :
      Tendsto
        (fun N : ℕ =>
          (N : ℝ) ^ (sieveExponent k * (A : ℝ) - 1))
        atTop (𝓝 0) := by
    have h :=
      (tendsto_rpow_neg_atTop hgap).comp
        tendsto_natCast_atTop_atTop
    convert h using 1
    funext N
    congr 1
    ring
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun N =>
      div_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 0] with N hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast hN
    have hfloor :
        (sieveLevel k N : ℝ) ≤
          (N : ℝ) ^ sieveExponent k := by
      exact Nat.floor_le
        (Real.rpow_nonneg hNpos.le _)
    have hpow :
        (sieveLevel k N : ℝ) ^ A ≤
          ((N : ℝ) ^ sieveExponent k) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor A
    calc
      (sieveLevel k N : ℝ) ^ A / (N : ℝ) ≤
          ((N : ℝ) ^ sieveExponent k) ^ A /
            (N : ℝ) :=
        div_le_div_of_nonneg_right hpow hNpos.le
      _ =
          (N : ℝ) ^
            (sieveExponent k * (A : ℝ) - 1) := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul hNpos.le,
          div_eq_mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_add hNpos]
        congr 1
  · exact hmodel

/-- Shifted form matching the nonzero cyclic modulus `M + 1`. -/
theorem tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div_succ
    {k : ℕ} (hk : 3 ≤ k) :
    Tendsto
      (fun M : ℕ =>
        (sieveLevel k (M + 1) : ℝ) ^
            cfzCanonicalCyclicBoundaryExponent k /
          (M + 1 : ℕ))
      atTop (𝓝 0) := by
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div hk).comp
      (tendsto_add_atTop_nat 1)

/-- The cyclic boundary vanishes for the exact Green--Tao sieve level and
every fixed primorial/residue pair. -/
theorem
    SmoothSieveCutoff.tendsto_norm_cyclicMajorant_sub_canonicalEulerFourierMainTerm_sieveLevel
    {k w b : ℕ}
    (χ : SmoothSieveCutoff)
    (hk : 3 ≤ k)
    (hb : 0 < b)
    (e : LinearFormsExponent k) :
    Tendsto
      (fun M : ℕ =>
        letI : NeZero (M + 1) := ⟨Nat.succ_ne_zero M⟩
        ‖(mean
              (linearFormsProduct k (M + 1)
                (χ.cyclicMajorant
                  (sieveLevel k (M + 1))
                  (primorial w) b) e) : ℂ) -
            χ.selectedCFZCanonicalEulerFourierMainTerm
              (N := M + 1) (sieveLevel k (M + 1))
              (primorial w) b e‖)
      atTop (𝓝 0) := by
  have hRtop :
      Tendsto (fun M : ℕ => sieveLevel k (M + 1))
        atTop atTop :=
    (tendsto_sieveLevel_atTop hk).comp
      (tendsto_add_atTop_nat 1)
  have hR :
      ∀ᶠ M : ℕ in atTop,
        2 ≤ sieveLevel k (M + 1) :=
    hRtop (eventually_ge_atTop 2)
  simpa using
    χ.tendsto_norm_mean_linearFormsProduct_cyclicMajorant_sub_canonicalEulerFourierMainTerm_primorial_zero_of_power_schedule
      (show 2 ≤ k by omega) e
      (fun M => sieveLevel k (M + 1))
      (fun M => M + 1)
      (fun _M => w)
      (fun _M => b)
      (fun M => Nat.succ_ne_zero M)
      hR
      (Filter.Eventually.of_forall fun _M => hb)
      (tendsto_sieveLevel_cfzCanonicalCyclicBoundaryPower_div_succ hk)

end Wikipedia.SzemeredisTheorem
