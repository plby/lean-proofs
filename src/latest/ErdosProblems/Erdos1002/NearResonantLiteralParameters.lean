import ErdosProblems.Erdos1002.NearResonantLiteralL2
import ErdosProblems.Erdos1002.NearResonantLiteralMerge
import ErdosProblems.Erdos1002.NaturalCutoffReconstructionReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Explicit parameters for the literal smooth near shot

This file combines the independently constructed zero and nonzero carrier
estimates only after proving that their Hilbert-space sum is the literal
physical smooth shot.  In particular, no estimate for a formal Fourier
coefficient sequence is substituted for an estimate of the physical
function.
-/

open Filter MeasureTheory Set AddCircle
open scoped BigOperators ComplexConjugate ENNReal Real Topology

namespace Erdos1002

noncomputable section

/-- The explicit normalized zero-carrier energy appearing after the
manuscript scaling `a=A/L`. -/
def nearLiteralZeroNormalizedEnergyBound (A L : ℝ) : ℝ :=
  2 * nearZeroFixedEnergyConstant / L ^ 2 +
    2 * nearZeroReciprocalEnergyConstant / (A * L) +
    4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2) +
    4 * nearZeroPrincipalScaleConstant ^ 2 / (A * L)

/-- The explicit normalized norm bound for all nonzero Bernoulli carriers. -/
def nearLiteralNonzeroNormalizedNormBound (A L : ℝ) : ℝ :=
  windowCarrierMassConstant * Real.sqrt
      (8 * nearCarrierBinaryLogLinearConstant *
          nearCarrierNonzeroEnergyConstant / A +
        2 * nearCarrierBinaryLogLinearConstant ^ 2 *
          Real.exp (-(5 / 2 : ℝ) * L)) +
    (windowCarrierMassConstant * Real.sqrt
        (9 * nearCarrierNonzeroEnergyConstant / A) +
      windowCarrierMassConstant * Real.sqrt
        (nearCarrierNonzeroEnergyConstant / A))

/-- Combined normalized norm bound for the literal smooth near shot. -/
def nearLiteralNormalizedNormBound (A L : ℝ) : ℝ :=
  (1 / 12 : ℝ) * Real.sqrt (nearLiteralZeroNormalizedEnergyBound A L) +
    nearLiteralNonzeroNormalizedNormBound A L

/-- The fixed-`A` limit of the preceding explicit bound as `L → ∞`. -/
def nearLiteralAsymptoticNormBound (A : ℝ) : ℝ :=
  (1 / 12 : ℝ) * Real.sqrt
      (4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2)) +
    (windowCarrierMassConstant * Real.sqrt
        (8 * nearCarrierBinaryLogLinearConstant *
          nearCarrierNonzeroEnergyConstant / A) +
      (windowCarrierMassConstant * Real.sqrt
          (9 * nearCarrierNonzeroEnergyConstant / A) +
        windowCarrierMassConstant * Real.sqrt
          (nearCarrierNonzeroEnergyConstant / A)))

/-- The normalized literal smooth near shot at the exact inner smoothing
scale used by the hard-window decomposition.  This is the generic analytic
profile with its threshold parameter specialized to `A / 2`: its plateau
therefore starts at `2 * (A / (2 * log N)) = A / log N`, exactly at the
hard threshold. -/
def normalizedSmoothNearLiteralShotTail
    (N : ℕ) (A ε : ℝ) (alpha : ℝ) : ℂ :=
  smoothNearLiteralShotTail N
      (A / (2 * Real.log (N : ℝ))) ε 2 N alpha /
    Real.log (N : ℝ)

/-- Exact sign-and-scale bridge to the hard-window decomposition.  This
locks the analytic estimate to the same `A/(2 log N)` smoothing scale and
the same open denominator endpoint `2 < p ≤ N` used by
`NearResonantLiteralMerge`; no proof irrelevance or asymptotic rewrite is
involved. -/
theorem normalizedSmoothNearLiteralShotTail_eq_merge_terms
    (N : ℕ) (A ε alpha : ℝ) :
    normalizedSmoothNearLiteralShotTail N A ε alpha =
      (nearMinorHardNearSum N A ε alpha -
          nearMinorSmallDenominatorSum N A ε alpha +
          nearMinorLowerTransitionSum N A ε alpha +
          nearMinorUpperTransitionSum N A ε alpha) /
        Real.log (N : ℝ) := by
  unfold normalizedSmoothNearLiteralShotTail
  rw [nearMinorHardNearSum_eq_endpoint_add_smooth_sub_transitions]
  ring

private theorem sqrt_div_le_sqrt_of_div_sq_le_literal
    {B C L : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 0 < L)
    (h : B / L ^ 2 ≤ C) :
    Real.sqrt B / L ≤ Real.sqrt C := by
  apply (sq_le_sq₀ (div_nonneg (Real.sqrt_nonneg B) hL.le)
    (Real.sqrt_nonneg C)).mp
  rw [div_pow, Real.sq_sqrt hB, Real.sq_sqrt hC]
  exact h

theorem nearLiteralZeroNormalizedEnergyBound_nonneg
    (A L : ℝ) (hA : 0 < A) (hL : 0 < L) :
    0 ≤ nearLiteralZeroNormalizedEnergyBound A L := by
  have hfixed := nearZeroFixedEnergyConstant_nonneg
  have hreciprocal := nearZeroReciprocalEnergyConstant_nonneg
  have hprincipal : 0 ≤ nearZeroPrincipalScaleConstant ^ 2 := sq_nonneg _
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold nearLiteralZeroNormalizedEnergyBound
  positivity

/-- Pulling the literal smooth-shot `L²` representative back to `(0,1)`
recovers the literal finite physical sum almost everywhere. -/
theorem unitCircleL2Pullback_smoothNearLiteralShotTail_ae
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    unitCircleL2Pullback
        (smoothNearLiteralShotTailL2 N a ε Q U ha haε) =ᵐ[uniform01Measure]
      smoothNearLiteralShotTail N a ε Q U := by
  have hcoe :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (smoothNearLiteralShotTailL2_coe_ae N a ε Q U ha haε)
  have hIoo : ∀ᵐ alpha : ℝ ∂uniform01Measure,
      alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [uniform01Measure]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hcoe, hIoo] with alpha hrepresentative halpha
  change
    (smoothNearLiteralShotTailL2 N a ε Q U ha haε :
        AddCircle (1 : ℝ) → ℂ) (alpha : AddCircle (1 : ℝ)) = _
  rw [hrepresentative]
  unfold smoothNearLiteralShotTailCircle
  exact AddCircle.liftIoc_coe_apply
    (by simpa using! (show alpha ∈ Ioc (0 : ℝ) 1 from
      ⟨halpha.1, halpha.2.le⟩))

theorem eLpNorm_smoothNearLiteralShotTail_eq_enorm
    (N : ℕ) (a ε : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) :
    eLpNorm (smoothNearLiteralShotTail N a ε Q U) 2 uniform01Measure =
      ‖smoothNearLiteralShotTailL2 N a ε Q U ha haε‖ₑ := by
  rw [← eLpNorm_unitCircleL2Pullback]
  exact eLpNorm_congr_ae
    (unitCircleL2Pullback_smoothNearLiteralShotTail_ae
      N a ε Q U ha haε).symm

theorem eLpNorm_smoothNearLiteralShotTail_div_eq_ofReal
    (N : ℕ) (a ε L : ℝ) (Q U : ℕ)
    (ha : 0 < a) (haε : a ≤ ε / 4) (hL : 0 < L) :
    eLpNorm
        (fun alpha ↦ smoothNearLiteralShotTail N a ε Q U alpha / L)
        2 uniform01Measure =
      ENNReal.ofReal
        (‖smoothNearLiteralShotTailL2 N a ε Q U ha haε‖ / L) := by
  have hfun :
      (fun alpha ↦ smoothNearLiteralShotTail N a ε Q U alpha / L) =
        ((L : ℂ)⁻¹ • smoothNearLiteralShotTail N a ε Q U) := by
    funext alpha
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hfun, eLpNorm_const_smul,
    eLpNorm_smoothNearLiteralShotTail_eq_enorm N a ε Q U ha haε]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_mul (norm_nonneg ((L : ℂ)⁻¹))]
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  field_simp [hL.ne']

/-- Pointwise quantitative assembly.  The summability hypothesis is stated
explicitly because it is exactly what licenses the Fourier-uniqueness
identification of the literal shot with the carrier `tsum`. -/
theorem norm_smoothNearLiteralShotTailL2_div_log_le
    (A L ε : ℝ) (N : ℕ)
    (hA : 0 < A) (hL : 0 < L) (hε : 0 < ε)
    (haε : A / L ≤ ε / 4) (hεhalf : ε < 1 / 2)
    (hNfour : 4 ≤ N) (hNL : Real.exp L = (N : ℝ))
    (hzeroRoom : 16 < (A / L) * (((N - 1 : ℕ) : ℝ) ^ 2))
    (hs : Summable
      (smoothNearNonzeroCarrierL2Term N (A / L) ε 2 N
        (div_pos hA hL) haε))
    (hnonzero :
      ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L ≤
        nearLiteralNonzeroNormalizedNormBound A L) :
    ‖smoothNearLiteralShotTailL2 N (A / L) ε 2 N
        (div_pos hA hL) haε‖ / L ≤
      nearLiteralNormalizedNormBound A L := by
  have hzeroSq :=
    norm_sq_smoothNearPrimitivePoleTailL2_div_log_sq_le
      A L ε N hA hL hε haε hεhalf hNfour hNL hzeroRoom
  have hzeroBoundNonneg :
      0 ≤ nearLiteralZeroNormalizedEnergyBound A L :=
    nearLiteralZeroNormalizedEnergyBound_nonneg A L hA hL
  have hpoleNorm :
      ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L ≤
        Real.sqrt (nearLiteralZeroNormalizedEnergyBound A L) := by
    have hsqrt := sqrt_div_le_sqrt_of_div_sq_le_literal
      (sq_nonneg ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
        (div_pos hA hL) haε‖)
      hzeroBoundNonneg hL
      (by simpa only [nearLiteralZeroNormalizedEnergyBound] using! hzeroSq)
    simpa only [Real.sqrt_sq_eq_abs, abs_norm] using! hsqrt
  have hzeroNorm :
      ‖smoothNearPrimitivePoleCarrierTailL2 N 0 (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L ≤
        (1 / 12 : ℝ) *
          Real.sqrt (nearLiteralZeroNormalizedEnergyBound A L) := by
    rw [smoothNearPrimitivePoleCarrierTailL2_zero, norm_smul]
    have hcoeff : ‖(1 / 12 : ℂ)‖ = (1 / 12 : ℝ) := by norm_num
    rw [hcoeff]
    calc
      (1 / 12 : ℝ) *
            ‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
              (div_pos hA hL) haε‖ / L =
          (1 / 12 : ℝ) *
            (‖smoothNearPrimitivePoleTailL2 (A / L) ε 2 N
              (div_pos hA hL) haε‖ / L) := by ring
      _ ≤ (1 / 12 : ℝ) *
          Real.sqrt (nearLiteralZeroNormalizedEnergyBound A L) :=
        mul_le_mul_of_nonneg_left hpoleNorm (by norm_num)
  rw [smoothNearLiteralShotTailL2_eq_zero_add_infiniteNonzero
    N (A / L) ε 2 N (by norm_num) (div_pos hA hL) hε haε
      hεhalf.le hs]
  calc
    ‖smoothNearPrimitivePoleCarrierTailL2 N 0 (A / L) ε 2 N
          (div_pos hA hL) haε +
        smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L ≤
      (‖smoothNearPrimitivePoleCarrierTailL2 N 0 (A / L) ε 2 N
          (div_pos hA hL) haε‖ +
        ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N
          (div_pos hA hL) haε‖) / L :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hL.le
    _ = ‖smoothNearPrimitivePoleCarrierTailL2 N 0 (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L +
        ‖smoothNearInfiniteNonzeroCarrierL2 N (A / L) ε 2 N
          (div_pos hA hL) haε‖ / L := by ring
    _ ≤ (1 / 12 : ℝ) *
          Real.sqrt (nearLiteralZeroNormalizedEnergyBound A L) +
        nearLiteralNonzeroNormalizedNormBound A L :=
      add_le_add hzeroNorm hnonzero
    _ = nearLiteralNormalizedNormBound A L := rfl

/-- Eventual quantitative estimate for the actual physical smooth near shot.
All side conditions used by the explicit carrier split remain visible; the
next parameter lemma may discharge them from `L → ∞`. -/
theorem eventually_norm_smoothNearLiteralShotTailL2_div_log_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) → 1 ≤ L →
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N →
      16 < (A / L) * (((N - 1 : ℕ) : ℝ) ^ 2) →
      ‖smoothNearLiteralShotTailL2 N (A / L) ε 2 N ha haε‖ / L ≤
        nearLiteralNormalizedNormBound A L := by
  filter_upwards [
      eventually_summable_smoothNearNonzeroCarrierL2Term_full
        A ε hA hε hεhalf,
      eventually_norm_smoothNearInfiniteNonzeroCarrierL2_div_log_le
        A ε hA hε hεhalf] with L hs hnonzero
  intro N ha haε hN hNL hL hcarrierRoom hzeroRoom
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs' := hs N ha haε hN hNL hL hcarrierRoom
  have hnonzero' := hnonzero N ha haε hN hNL hL hcarrierRoom
  have hmain := norm_smoothNearLiteralShotTailL2_div_log_le
    A L ε N hA hLpos hε haε hεhalf hN hNL hzeroRoom hs' hnonzero'
  simpa only [show ha = div_pos hA hLpos from Subsingleton.elim _ _,
    show haε = haε from rfl] using hmain

/-- The carrier-gap and zero-carrier room conditions in the preceding
theorem follow automatically from `exp L = N` once `L` is large.  Thus no
analytic side condition survives in the eventual physical estimate. -/
theorem eventually_norm_smoothNearLiteralShotTailL2_div_log_le_no_room
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ)
      (ha : 0 < A / L) (haε : A / L ≤ ε / 4),
      4 ≤ N → Real.exp L = (N : ℝ) →
      ‖smoothNearLiteralShotTailL2 N (A / L) ε 2 N ha haε‖ / L ≤
        nearLiteralNormalizedNormBound A L := by
  have hpoly : ∀ᶠ L : ℝ in atTop,
      (128 / A) * L ^ 1 ≤ Real.exp (2 * L) :=
    eventually_const_mul_pow_le_exp (128 / A) 1 2
      (by positivity) (by norm_num)
  filter_upwards [
      eventually_norm_smoothNearLiteralShotTailL2_div_log_le
        A ε hA hε hεhalf,
      eventually_ge_atTop (16 : ℝ), hpoly] with L hmain hLlarge hpolyL
  intro N ha haε hN hNL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLlarge
  have hLone : 1 ≤ L := by linarith
  have hNpos : 0 < N := by omega
  have hcarrierRoom :
      nearCarrierGapWidth L + 1 ≤ nearCarrierLogExponent N :=
    nearCarrierGapWidth_add_one_le_logExponent
      N L hNpos hLlarge hNL
  have hexpTwo : Real.exp (2 * L) = (N : ℝ) ^ 2 := by
    calc
      Real.exp (2 * L) = Real.exp (L + L) := by ring_nf
      _ = Real.exp L * Real.exp L := Real.exp_add L L
      _ = (N : ℝ) ^ 2 := by rw [hNL]; ring
  have hpolyN : (128 / A) * L ≤ (N : ℝ) ^ 2 := by
    simpa only [pow_one, hexpTwo] using! hpolyL
  have hscaleNonneg : 0 ≤ A / (4 * L) := by positivity
  have hscaled :
      (32 : ℝ) ≤ (A / L) * ((N : ℝ) / 2) ^ 2 := by
    calc
      (32 : ℝ) = (A / (4 * L)) * ((128 / A) * L) := by
        field_simp [hA.ne', hLpos.ne']
        ring
      _ ≤ (A / (4 * L)) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hpolyN hscaleNonneg
      _ = (A / L) * ((N : ℝ) / 2) ^ 2 := by
        field_simp [hLpos.ne']
        ring
  have hnatHalf : N ≤ 2 * (N - 1) := by omega
  have hcastHalf : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnatHalf
  have hhalf : (N : ℝ) / 2 ≤ ((N - 1 : ℕ) : ℝ) := by
    linarith
  have hsq : ((N : ℝ) / 2) ^ 2 ≤ (((N - 1 : ℕ) : ℝ) ^ 2) :=
    pow_le_pow_left₀ (by positivity) hhalf 2
  have hzeroUpper := mul_le_mul_of_nonneg_left hsq (div_nonneg hA.le hLpos.le)
  have hzeroRoom : 16 < (A / L) * (((N - 1 : ℕ) : ℝ) ^ 2) :=
    (by norm_num : (16 : ℝ) < 32).trans_le (hscaled.trans hzeroUpper)
  exact hmain N ha haε hN hNL hLone hcarrierRoom hzeroRoom

/-- On the natural integer parameter, the actual normalized physical
smooth shot has `eLpNorm` bounded by the explicit carrier envelope with the
hard-window scale `A/2`. -/
theorem eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_le
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      eLpNorm (normalizedSmoothNearLiteralShotTail N A ε)
          2 uniform01Measure ≤
        ENNReal.ofReal
          (nearLiteralNormalizedNormBound (A / 2)
            (Real.log (N : ℝ))) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hboundN := hlog.eventually
    (eventually_norm_smoothNearLiteralShotTailL2_div_log_le_no_room
      (A / 2) ε (by positivity) hε hεhalf)
  have hlarge : ∀ᶠ N : ℕ in atTop,
      max 1 (2 * A / ε) ≤ Real.log (N : ℝ) :=
    hlog.eventually (eventually_ge_atTop (max 1 (2 * A / ε)))
  filter_upwards [hboundN, hlarge, eventually_ge_atTop 4] with
      N hbound hLlarge hN
  let L : ℝ := Real.log (N : ℝ)
  let A₀ : ℝ := A / 2
  let a : ℝ := A₀ / L
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_left _ _) hLlarge)
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hscale : a = A / (2 * L) := by
    dsimp [A₀, a]
    field_simp [hLpos.ne']
  have ha : 0 < a := by dsimp [a]; positivity
  have haε : a ≤ ε / 4 := by
    have hthreshold : 2 * A / ε ≤ L :=
      (le_max_right _ _).trans hLlarge
    rw [hscale]
    apply (div_le_iff₀ (mul_pos (by norm_num) hLpos)).2
    have hεnonneg : 0 ≤ ε := hε.le
    have hmul := mul_le_mul_of_nonneg_left hthreshold hεnonneg
    field_simp [hε.ne'] at hmul ⊢
    nlinarith
  have haε₀ : A₀ / L ≤ ε / 4 := by simpa only [a] using! haε
  have hNL : Real.exp L = (N : ℝ) := by
    dsimp [L]
    rw [Real.exp_log]
    positivity
  have ha₀ : 0 < A₀ / L := div_pos hA₀ hLpos
  have hnorm := hbound N
    (by simpa only [A₀, L] using! ha₀)
    (by simpa only [A₀, L] using! haε₀) hN
    (by simpa only [L] using! hNL)
  change
    ‖smoothNearLiteralShotTailL2 N (A₀ / L) ε 2 N _ _‖ / L ≤
      nearLiteralNormalizedNormBound A₀ L at hnorm
  have hnorm' :
      ‖smoothNearLiteralShotTailL2 N a ε 2 N ha haε‖ / L ≤
        nearLiteralNormalizedNormBound A₀ L := by
    simpa only [a, show ha = _ from Subsingleton.elim _ _,
      show haε = _ from Subsingleton.elim _ _] using hnorm
  rw [show normalizedSmoothNearLiteralShotTail N A ε =
      fun alpha ↦ smoothNearLiteralShotTail N a ε 2 N alpha / L by
    funext alpha
    unfold normalizedSmoothNearLiteralShotTail
    dsimp only [L]
    rw [hscale]]
  rw [eLpNorm_smoothNearLiteralShotTail_div_eq_ofReal
    N a ε L 2 N ha haε hLpos]
  exact ENNReal.ofReal_le_ofReal (by simpa only [A₀, L] using! hnorm')

/-- For fixed positive `A`, every finite-`L` remainder in the explicit
literal-shot estimate vanishes and the bound converges to its displayed
`O(A⁻¹/²)` envelope. -/
theorem tendsto_nearLiteralNormalizedNormBound_atTop
    (A : ℝ) (hA : 0 < A) :
    Tendsto (nearLiteralNormalizedNormBound A) atTop
      (nhds (nearLiteralAsymptoticNormBound A)) := by
  have hpowTwo : Tendsto (fun L : ℝ ↦ L ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hAL : Tendsto (fun L : ℝ ↦ A * L) atTop atTop :=
    tendsto_id.const_mul_atTop hA
  have hzFixed : Tendsto
      (fun L : ℝ ↦ 2 * nearZeroFixedEnergyConstant / L ^ 2)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hpowTwo
  have hzReciprocal : Tendsto
      (fun L : ℝ ↦ 2 * nearZeroReciprocalEnergyConstant / (A * L))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hAL
  have hzLast : Tendsto
      (fun L : ℝ ↦ 4 * nearZeroPrincipalScaleConstant ^ 2 / (A * L))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hAL
  have hzConst : Tendsto
      (fun _L : ℝ ↦
        4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2))
      atTop
      (nhds (4 * nearZeroPrincipalScaleConstant ^ 2 /
        (A * Real.log 2))) := tendsto_const_nhds
  have hzero : Tendsto
      (nearLiteralZeroNormalizedEnergyBound A) atTop
      (nhds (4 * nearZeroPrincipalScaleConstant ^ 2 /
        (A * Real.log 2))) := by
    have hsum := ((hzFixed.add hzReciprocal).add hzConst).add hzLast
    simpa only [nearLiteralZeroNormalizedEnergyBound, zero_add, add_zero] using! hsum
  have hlinear : Tendsto (fun L : ℝ ↦ (5 / 2 : ℝ) * L) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hexp : Tendsto
      (fun L : ℝ ↦ Real.exp (-(5 / 2 : ℝ) * L)) atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear
    convert! h using 1
    funext L
    dsimp only [Function.comp_apply]
    congr 1
    ring
  have hleak : Tendsto
      (fun L : ℝ ↦
        2 * nearCarrierBinaryLogLinearConstant ^ 2 *
          Real.exp (-(5 / 2 : ℝ) * L)) atTop (nhds 0) := by
    have hc : Tendsto
        (fun _L : ℝ ↦ 2 * nearCarrierBinaryLogLinearConstant ^ 2)
        atTop (nhds (2 * nearCarrierBinaryLogLinearConstant ^ 2)) :=
      tendsto_const_nhds
    simpa only [mul_zero] using! hc.mul hexp
  have hinside : Tendsto
      (fun L : ℝ ↦
        8 * nearCarrierBinaryLogLinearConstant *
            nearCarrierNonzeroEnergyConstant / A +
          2 * nearCarrierBinaryLogLinearConstant ^ 2 *
            Real.exp (-(5 / 2 : ℝ) * L)) atTop
      (nhds (8 * nearCarrierBinaryLogLinearConstant *
        nearCarrierNonzeroEnergyConstant / A)) := by
    simpa only [add_zero] using! tendsto_const_nhds.add hleak
  have hnonzero : Tendsto
      (nearLiteralNonzeroNormalizedNormBound A) atTop
      (nhds
        (windowCarrierMassConstant * Real.sqrt
            (8 * nearCarrierBinaryLogLinearConstant *
              nearCarrierNonzeroEnergyConstant / A) +
          (windowCarrierMassConstant * Real.sqrt
              (9 * nearCarrierNonzeroEnergyConstant / A) +
            windowCarrierMassConstant * Real.sqrt
              (nearCarrierNonzeroEnergyConstant / A)))) := by
    simpa only [nearLiteralNonzeroNormalizedNormBound] using!
      (tendsto_const_nhds.mul hinside.sqrt).add tendsto_const_nhds
  simpa only [nearLiteralNormalizedNormBound,
    nearLiteralAsymptoticNormBound] using!
    (tendsto_const_nhds.mul hzero.sqrt).add hnonzero

/-- The surviving fixed-`A` envelope itself vanishes as the hard resonance
threshold tends to infinity. -/
theorem tendsto_nearLiteralAsymptoticNormBound_atTop :
    Tendsto nearLiteralAsymptoticNormBound atTop (nhds 0) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hAlog : Tendsto (fun A : ℝ ↦ A * Real.log 2) atTop atTop :=
    tendsto_id.atTop_mul_const hlogTwo
  have hzBase : Tendsto
      (fun A : ℝ ↦
        4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hAlog
  have hz : Tendsto
      (fun A : ℝ ↦ (1 / 12 : ℝ) * Real.sqrt
        (4 * nearZeroPrincipalScaleConstant ^ 2 / (A * Real.log 2)))
      atTop (nhds 0) := by
    have hc : Tendsto (fun _A : ℝ ↦ (1 / 12 : ℝ)) atTop
        (nhds (1 / 12 : ℝ)) := tendsto_const_nhds
    simpa only [Real.sqrt_zero, mul_zero] using! hc.mul hzBase.sqrt
  have hfirstBase : Tendsto
      (fun A : ℝ ↦
        8 * nearCarrierBinaryLogLinearConstant *
          nearCarrierNonzeroEnergyConstant / A) atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hsecondBase : Tendsto
      (fun A : ℝ ↦ 9 * nearCarrierNonzeroEnergyConstant / A)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hthirdBase : Tendsto
      (fun A : ℝ ↦ nearCarrierNonzeroEnergyConstant / A)
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hwindow : Tendsto
      (fun _A : ℝ ↦ windowCarrierMassConstant) atTop
      (nhds windowCarrierMassConstant) := tendsto_const_nhds
  have hfirst : Tendsto
      (fun A : ℝ ↦ windowCarrierMassConstant * Real.sqrt
        (8 * nearCarrierBinaryLogLinearConstant *
          nearCarrierNonzeroEnergyConstant / A)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using! hwindow.mul hfirstBase.sqrt
  have hsecond : Tendsto
      (fun A : ℝ ↦ windowCarrierMassConstant * Real.sqrt
        (9 * nearCarrierNonzeroEnergyConstant / A)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using! hwindow.mul hsecondBase.sqrt
  have hthird : Tendsto
      (fun A : ℝ ↦ windowCarrierMassConstant * Real.sqrt
        (nearCarrierNonzeroEnergyConstant / A)) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using! hwindow.mul hthirdBase.sqrt
  simpa only [nearLiteralAsymptoticNormBound, zero_add, add_zero] using!
    hz.add (hfirst.add (hsecond.add hthird))

/-- Fixed-`A` epsilon form of the smooth-shot estimate: after `N` is large,
the physical `eLpNorm` lies below the asymptotic envelope plus an arbitrary
positive error. -/
theorem eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_le_asymptotic_add
    (A ε η : ℝ) (hA : 0 < A) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      eLpNorm (normalizedSmoothNearLiteralShotTail N A ε)
          2 uniform01Measure ≤
        ENNReal.ofReal (nearLiteralAsymptoticNormBound (A / 2) + η) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hboundLimit :=
    (tendsto_nearLiteralNormalizedNormBound_atTop (A / 2) (by positivity)).comp hlog
  have hupper : ∀ᶠ N : ℕ in atTop,
      nearLiteralNormalizedNormBound (A / 2) (Real.log (N : ℝ)) <
        nearLiteralAsymptoticNormBound (A / 2) + η :=
    (tendsto_order.1 hboundLimit).2 _ (lt_add_of_pos_right _ hη)
  filter_upwards [
      eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_le
        A ε hA hε hεhalf,
      hupper] with N hnorm hstrict
  exact hnorm.trans (ENNReal.ofReal_le_ofReal hstrict.le)

/-- The literal smooth component is negligible in the required iterated
cutoff limit, with the outer cutoff indexed by natural numbers exactly as in
the final assembly. -/
theorem iterated_eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_lt
    (ε η : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) (hη : 0 < η) :
    ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      eLpNorm
          (normalizedSmoothNearLiteralShotTail N (A : ℝ) ε)
          2 uniform01Measure ≤ ENNReal.ofReal η := by
  have hscale : Tendsto (fun A : ℕ ↦ (A : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hasymptotic := tendsto_nearLiteralAsymptoticNormBound_atTop.comp hscale
  have hsmall : ∀ᶠ A : ℕ in atTop,
      nearLiteralAsymptoticNormBound ((A : ℝ) / 2) < η / 2 :=
    (tendsto_order.1 hasymptotic).2 _ (by positivity)
  filter_upwards [hsmall, eventually_ge_atTop 1] with A hAasymptotic hA
  have hinner :=
    eventually_eLpNorm_normalizedSmoothNearLiteralShotTail_le_asymptotic_add
      (A : ℝ) ε (η / 2) (by exact_mod_cast (show 0 < A by omega))
      hε hεhalf (by positivity)
  filter_upwards [hinner] with N hN
  exact hN.trans (ENNReal.ofReal_le_ofReal (by linarith))

end

end Erdos1002
