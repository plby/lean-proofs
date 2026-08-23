/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166Core
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Parameters

/-!
The near-critical deterministic-horizon bridge used before HLOZ
Propositions 4.5 and 4.7.  This file deliberately isolates the only input
from the maximal-local-time lower-tail theorem: summability of its named
lower-tail events at the rounded horizons below.
-/

namespace Erdos1166.HLOZNearCriticalBridge

open Filter MeasureTheory Set
open scoped ENNReal

open HLOZProp47Parameters

/-! ### The rounded near-critical horizon -/

/-- With the corrected source value `κ₁ = 17/50`, the horizon correction
exponent is `r = 1 - 2κ₁ = 8/25`. -/
noncomputable def horizonExponent : ℝ := 1 - 2 * kappaOne

theorem horizonExponent_eq : horizonExponent = (8 : ℝ) / 25 := by
  norm_num [horizonExponent, kappaOne]

theorem horizonExponent_pos : 0 < horizonExponent := by
  norm_num [horizonExponent_eq]

theorem horizonExponent_lt_one_third : horizonExponent < (1 : ℝ) / 3 := by
  norm_num [horizonExponent_eq]

/-- HLOZ's choice `δ = 7/5 - 4κ₁ = 1/25`. -/
noncomputable def lowerTailDelta : ℝ := 7 / 5 - 4 * kappaOne

noncomputable def lowerTailExponent : ℝ := 8 / 5 + lowerTailDelta

theorem lowerTailDelta_eq : lowerTailDelta = (1 : ℝ) / 25 := by
  norm_num [lowerTailDelta, kappaOne]

theorem lowerTailExponent_eq : lowerTailExponent = (41 : ℝ) / 25 := by
  norm_num [lowerTailExponent, lowerTailDelta_eq]

theorem lowerTailExponent_pos : 0 < lowerTailExponent := by
  norm_num [lowerTailExponent_eq]

theorem lowerTail_power_identity :
    (1 : ℝ) / 2 * lowerTailExponent = (1 : ℝ) / 2 + horizonExponent := by
  norm_num [lowerTailExponent_eq, horizonExponent_eq]

/-- The coefficient `π^(2-2κ₁) = π^(33/25)` in HLOZ (4.10). -/
noncomputable def horizonCoefficient : ℝ := Real.pi ^ (2 - 2 * kappaOne)

theorem horizonCoefficient_eq : horizonCoefficient = Real.pi ^ ((33 : ℝ) / 25) := by
  norm_num [horizonCoefficient, kappaOne]

theorem horizonCoefficient_pos : 0 < horizonCoefficient := by
  exact Real.rpow_pos_of_pos Real.pi_pos _

/-- The exact real logarithm in HLOZ (4.10). -/
noncomputable def nearCriticalLogHorizon (m : ℕ) : ℝ :=
  Real.sqrt Real.pi * Real.sqrt (m : ℝ) +
    horizonCoefficient * (m : ℝ) ^ horizonExponent

/-- HLOZ's near-critical time horizon, rounded upward to a natural time. -/
noncomputable def nearCriticalHorizon (m : ℕ) : ℕ :=
  Nat.ceil (Real.exp (nearCriticalLogHorizon m))

theorem nearCriticalHorizon_pos (m : ℕ) : 0 < nearCriticalHorizon m := by
  rw [nearCriticalHorizon, Nat.ceil_pos]
  exact Real.exp_pos _

/-! ### Rounding and real-power estimates for the source horizon -/

/-- A fixed multiple of a smaller real power of `m` is eventually bounded
by any positive fixed multiple of a larger power. -/
theorem eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    {C d p q : ℝ} (_hC : 0 ≤ C) (hd : 0 < d) (hpq : p < q) :
    ∀ᶠ m : ℕ in atTop,
      C * (m : ℝ) ^ p ≤ d * (m : ℝ) ^ q := by
  have hpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (q - p)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C / d))
  filter_upwards [hlarge, eventually_ge_atTop 1] with m hm hm1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hratio : C ≤ d * (m : ℝ) ^ (q - p) := by
    simpa only [mul_comm] using (div_le_iff₀ hd).mp hm
  calc
    C * (m : ℝ) ^ p ≤ (d * (m : ℝ) ^ (q - p)) * (m : ℝ) ^ p := by
      gcongr
    _ = d * ((m : ℝ) ^ (q - p) * (m : ℝ) ^ p) := by ring
    _ = d * (m : ℝ) ^ q := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

theorem nearCriticalLogHorizon_nonneg (m : ℕ) :
    0 ≤ nearCriticalLogHorizon m := by
  unfold nearCriticalLogHorizon
  exact add_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_nonneg horizonCoefficient_pos.le
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Upward rounding gives the lower logarithmic comparison needed for the
positive square term in Proposition 1.3. -/
theorem nearCriticalLogHorizon_le_log_horizon (m : ℕ) :
    nearCriticalLogHorizon m ≤
      Real.log (nearCriticalHorizon m : ℝ) := by
  apply (Real.le_log_iff_exp_le (by
    exact_mod_cast nearCriticalHorizon_pos m)).2
  exact Nat.le_ceil _

/-- The ceiling changes the logarithm by at most `log 2`. -/
theorem log_horizon_le_nearCriticalLogHorizon_add_log_two (m : ℕ) :
    Real.log (nearCriticalHorizon m : ℝ) ≤
      nearCriticalLogHorizon m + Real.log 2 := by
  apply (Real.log_le_iff_le_exp (by
    exact_mod_cast nearCriticalHorizon_pos m)).2
  have hceil : (nearCriticalHorizon m : ℝ) <
      Real.exp (nearCriticalLogHorizon m) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_nonneg _)
  calc
    (nearCriticalHorizon m : ℝ) ≤
        Real.exp (nearCriticalLogHorizon m) + 1 := hceil.le
    _ ≤ 2 * Real.exp (nearCriticalLogHorizon m) := by
      have := Real.one_le_exp (nearCriticalLogHorizon_nonneg m)
      linarith
    _ = Real.exp (nearCriticalLogHorizon m + Real.log 2) := by
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring

theorem eventually_horizon_correction_le_sixth_leading :
    ∀ᶠ m : ℕ in atTop,
      horizonCoefficient * (m : ℝ) ^ horizonExponent ≤
        ((1 : ℝ) / 6) * Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by
  have h := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := horizonCoefficient) (d := (1 / 6) * Real.sqrt Real.pi)
    (p := horizonExponent) (q := 1 / 2) horizonCoefficient_pos.le
    (by positivity) (by norm_num [horizonExponent_eq])
  filter_upwards [h] with m hm
  simpa only [Real.sqrt_eq_rpow, mul_assoc] using hm

theorem eventually_log_two_le_sixth_leading :
    ∀ᶠ m : ℕ in atTop,
      Real.log 2 ≤
        ((1 : ℝ) / 6) * Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by
  have h := eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
    (C := Real.log 2) (d := (1 / 6) * Real.sqrt Real.pi)
    (p := 0) (q := 1 / 2) (Real.log_nonneg (by norm_num))
    (by positivity) (by norm_num)
  filter_upwards [h, eventually_ge_atTop 1] with m hm hm1
  simpa only [Real.rpow_zero, mul_one, Real.sqrt_eq_rpow] using hm

/-- A rounding-safe upper comparison.  The constant `4/3` is chosen because
`(4/3)^(41/25) < (4/3)^2 = 16/9 < 2`. -/
theorem eventually_log_horizon_le_four_thirds_leading :
    ∀ᶠ m : ℕ in atTop,
      Real.log (nearCriticalHorizon m : ℝ) ≤
        ((4 : ℝ) / 3) *
          (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) := by
  filter_upwards [eventually_horizon_correction_le_sixth_leading,
    eventually_log_two_le_sixth_leading] with m hc hlog
  have hu := log_horizon_le_nearCriticalLogHorizon_add_log_two m
  unfold nearCriticalLogHorizon at hu
  linarith

theorem leading_rpow_eq (m : ℕ) :
    (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^ lowerTailExponent =
      Real.pi ^ ((41 : ℝ) / 50) *
        (m : ℝ) ^ ((41 : ℝ) / 50) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    Real.mul_rpow (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ← Real.rpow_mul Real.pi_pos.le,
    ← Real.rpow_mul (Nat.cast_nonneg m)]
  norm_num [lowerTailExponent_eq]

/-- This is the upper half of the exact cancellation in HLOZ (4.11): the
rounded logarithmic error is strictly below twice the leading
`m^(41/50)` term. -/
theorem eventually_log_horizon_rpow_lt_two_leading_rpow :
    ∀ᶠ m : ℕ in atTop,
      Real.log (nearCriticalHorizon m : ℝ) ^ lowerTailExponent <
        2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^ lowerTailExponent := by
  filter_upwards [eventually_log_horizon_le_four_thirds_leading,
    eventually_ge_atTop 1] with m hlog hm1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hleadpos :
      0 < Real.sqrt Real.pi * Real.sqrt (m : ℝ) := by positivity
  have hbase : (1 : ℝ) ≤ 4 / 3 := by norm_num
  have hbeta2 : lowerTailExponent < 2 := by
    norm_num [lowerTailExponent_eq]
  have hpow := Real.rpow_le_rpow
    (Real.log_natCast_nonneg (nearCriticalHorizon m)) hlog
    lowerTailExponent_pos.le
  calc
    Real.log (nearCriticalHorizon m : ℝ) ^ lowerTailExponent ≤
        (((4 : ℝ) / 3) *
          (Real.sqrt Real.pi * Real.sqrt (m : ℝ))) ^
            lowerTailExponent := hpow
    _ = ((4 : ℝ) / 3) ^ lowerTailExponent *
          (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^
            lowerTailExponent := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4 / 3) hleadpos.le]
    _ ≤ ((4 : ℝ) / 3) ^ (2 : ℝ) *
          (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^
            lowerTailExponent := by
      gcongr
    _ < 2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^
          lowerTailExponent := by
      rw [show ((4 : ℝ) / 3) ^ (2 : ℝ) = (16 : ℝ) / 9 by
        norm_num [Real.rpow_two]]
      nlinarith [Real.rpow_pos_of_pos hleadpos lowerTailExponent]

theorem pi_inverse_mul_sqrt_mul_horizonCoefficient :
    Real.pi⁻¹ * (Real.sqrt Real.pi * horizonCoefficient) =
      Real.pi ^ ((41 : ℝ) / 50) := by
  calc
    Real.pi⁻¹ * (Real.sqrt Real.pi * horizonCoefficient) =
        (Real.pi ^ (-1 : ℝ) * Real.pi ^ ((1 : ℝ) / 2)) *
          Real.pi ^ ((33 : ℝ) / 25) := by
      rw [Real.rpow_neg_one, Real.sqrt_eq_rpow, horizonCoefficient_eq]
      ring
    _ = Real.pi ^ ((-1 : ℝ) + 1 / 2) *
          Real.pi ^ ((33 : ℝ) / 25) := by
      rw [← Real.rpow_add Real.pi_pos]
    _ = Real.pi ^ (((-1 : ℝ) + 1 / 2) + 33 / 25) := by
      rw [← Real.rpow_add Real.pi_pos]
    _ = Real.pi ^ ((41 : ℝ) / 50) := by norm_num

theorem sqrt_mul_rpow_horizonExponent (m : ℕ) (hm : 0 < m) :
    Real.sqrt (m : ℝ) * (m : ℝ) ^ horizonExponent =
      (m : ℝ) ^ ((41 : ℝ) / 50) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by exact_mod_cast hm)]
  congr 1
  norm_num [horizonExponent_eq]

/-- Exact source cancellation: the cross term in `π⁻¹ L_m²` is twice the
leading `41/25`-power term. -/
theorem horizon_cross_term_eq_two_leading_rpow (m : ℕ) (hm : 0 < m) :
    Real.pi⁻¹ *
        (2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) *
          (horizonCoefficient * (m : ℝ) ^ horizonExponent)) =
      2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^
        lowerTailExponent := by
  rw [leading_rpow_eq, ← pi_inverse_mul_sqrt_mul_horizonCoefficient,
    ← sqrt_mul_rpow_horizonExponent m hm]
  ring

theorem pi_inverse_mul_leading_sq (m : ℕ) :
    Real.pi⁻¹ * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) ^ 2 =
      (m : ℝ) := by
  rw [mul_pow, Real.sq_sqrt Real.pi_pos.le,
    Real.sq_sqrt (Nat.cast_nonneg m)]
  field_simp

theorem pi_inverse_mul_logHorizon_sq_ge_baseline_add_cross (m : ℕ) :
    (m : ℝ) +
        Real.pi⁻¹ *
          (2 * (Real.sqrt Real.pi * Real.sqrt (m : ℝ)) *
            (horizonCoefficient * (m : ℝ) ^ horizonExponent)) ≤
      Real.pi⁻¹ * nearCriticalLogHorizon m ^ 2 := by
  have hpiInv : 0 ≤ Real.pi⁻¹ := (inv_pos.mpr Real.pi_pos).le
  have hsquare :
      0 ≤ (horizonCoefficient * (m : ℝ) ^ horizonExponent) ^ 2 :=
    sq_nonneg _
  rw [nearCriticalLogHorizon]
  nlinarith [pi_inverse_mul_leading_sq m,
    mul_nonneg hpiInv hsquare]

/-! ### Stopping-time and lower-tail events -/

/-- The event that `T_m^k` lies beyond a deterministic horizon. -/
def lateThresholdEvent (ψ : ℕ → ℕ) (m k : ℕ) : Set (ℕ → Site) :=
  {s | (ψ m : WithTop ℕ) < firstKSitesReachLevel m k s}

/-- The `k`-site version of HLOZ's event `M_m^k`.  It is repeated here so
this bridge depends only on the core stopping-time API. -/
def thresholdTimeEventK (m k : ℕ) : Set (ℕ → Site) :=
  {s | firstKSitesReachLevel m k s < firstKSitesReachLevel (m + 1) 1 s}

theorem thresholdTimeEventK_four (m : ℕ) :
    thresholdTimeEventK m 4 = hlozThresholdTimeEvent m := rfl

/-- The late-threshold part of HLOZ's event `M_m^k`. -/
def lateOnThresholdEvent (ψ : ℕ → ℕ) (m k : ℕ) : Set (ℕ → Site) :=
  lateThresholdEvent ψ m k ∩ thresholdTimeEventK m k

/-- The only maximal-local-time event needed to remove a late horizon. -/
def lowerMaxEvent (ψ : ℕ → ℕ) (m : ℕ) : Set (ℕ → Site) :=
  {s | maxLocalTime s (ψ m) ≤ m}

theorem measurableSet_lateThresholdEvent (ψ : ℕ → ℕ) (m k : ℕ) :
    MeasurableSet (lateThresholdEvent ψ m k) := by
  apply HLOZFoundation.canonicalFiltration.le (ψ m)
  exact (isStoppingTime_firstKSitesReachLevel m k).measurableSet_gt (ψ m)

theorem measurableSet_lowerMaxEvent (ψ : ℕ → ℕ) (m : ℕ) :
    MeasurableSet (lowerMaxEvent ψ m) := by
  exact measurableSet_le (measurable_maxLocalTime_eval (ψ m)) measurable_const

/-- Pathwise horizon bridge.  On `M_m^k`, if `T_m^k` has not occurred by
time `ψ_m`, then no site can yet have reached level `m+1`. -/
theorem lateOnThresholdEvent_subset_lowerMaxEvent
    (ψ : ℕ → ℕ) (m k : ℕ) :
    lateOnThresholdEvent ψ m k ⊆ lowerMaxEvent ψ m := by
  intro s hs
  rcases hs with ⟨hlate, hM⟩
  change (ψ m : WithTop ℕ) < firstKSitesReachLevel m k s at hlate
  change firstKSitesReachLevel m k s <
    firstKSitesReachLevel (m + 1) 1 s at hM
  change maxLocalTime s (ψ m) ≤ m
  by_contra hnot
  have hmax : m + 1 ≤ maxLocalTime s (ψ m) := by omega
  have hcardNe : (sitesAtLeastLevel s (ψ m) (m + 1)).card ≠ 0 := by
    exact (card_sitesAtLeastLevel_eq_zero_iff_max_lt s (ψ m) (m + 1)).not.mpr
      (by omega)
  have hmem : (sitesAtLeastLevel s (ψ m) (m + 1)).card ∈ Set.Ici 1 := by
    change 1 ≤ (sitesAtLeastLevel s (ψ m) (m + 1)).card
    omega
  have hnext : firstKSitesReachLevel (m + 1) 1 s ≤ (ψ m : WithTop ℕ) := by
    exact hittingAfter_le_of_mem
      (u := fun n s ↦ (sitesAtLeastLevel s n (m + 1)).card)
      (s := Set.Ici 1) (n := 0) (i := ψ m) (ω := s)
      (Nat.zero_le _) hmem
  have : firstKSitesReachLevel m k s < (ψ m : WithTop ℕ) :=
    hM.trans_le hnext
  exact (not_lt_of_ge hlate.le) this

/-- The large-horizon subevent appearing after the six-pairing reduction. -/
def pairingLateHorizonEvent (ψ : ℕ → ℕ) (m : ℕ) (i : Fin 6) :
    Set (ℕ → Site) :=
  HLOZPairing.pairingEvent m i ∩ lateThresholdEvent ψ m 4

/-- Each paired large-horizon event is contained in the generic late part
of `M_m^4`. -/
theorem pairingLateHorizonEvent_subset_lateOnThresholdEvent
    (ψ : ℕ → ℕ) (m : ℕ) (i : Fin 6) :
    pairingLateHorizonEvent ψ m i ⊆ lateOnThresholdEvent ψ m 4 := by
  rintro s ⟨hpair, hlate⟩
  have hdirect : s ∈ hlozFourSitesReachLevelFirst m :=
    HLOZPairing.pairingEvent_subset_hlozFourSitesReachLevelFirst m i hpair
  have hM : s ∈ hlozThresholdTimeEvent m := by
    rw [hlozThresholdTimeEvent_eq]
    exact hdirect
  exact ⟨hlate, by
    simpa only [thresholdTimeEventK_four] using hM⟩

theorem measure_lateOnThresholdEvent_le_lowerMaxEvent
    (μ : Measure (ℕ → Site)) (ψ : ℕ → ℕ) (m k : ℕ) :
    μ (lateOnThresholdEvent ψ m k) ≤ μ (lowerMaxEvent ψ m) :=
  measure_mono (lateOnThresholdEvent_subset_lowerMaxEvent ψ m k)

/-- Finite initial segments do not affect ENNReal summability.  This version
is convenient when a source estimate and its deterministic threshold
comparison hold only eventually. -/
theorem ennreal_tsum_ne_top_of_eventually_le
    (f g : ℕ → ℝ≥0∞) (hf : ∀ m, f m ≠ ∞)
    (hfg : ∀ᶠ m : ℕ in atTop, f m ≤ g m)
    (hg : (∑' m : ℕ, g m) ≠ ∞) :
    (∑' m : ℕ, f m) ≠ ∞ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hfg
  have htail : (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≤
      ∑' m : ℕ, g m := by
    calc
      (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≤
          ∑' i : {i : ℕ // i ∉ Finset.range N}, g i := by
        apply ENNReal.tsum_le_tsum
        intro i
        apply hN i
        simpa only [Finset.mem_range, not_lt] using i.property
      _ ≤ ∑' m : ℕ, g m :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.coe_injective g
  have htailFinite :
      (∑' i : {i : ℕ // i ∉ Finset.range N}, f i) ≠ ∞ :=
    ne_top_of_le_ne_top hg htail
  rw [← ENNReal.sum_add_tsum_compl (Finset.range N) f]
  exact ENNReal.add_ne_top.mpr
    ⟨ENNReal.sum_ne_top.mpr (fun i _hi ↦ hf i), htailFinite⟩

/-- Summability of the lower-tail probabilities gives the summable
bad-horizon contribution used in the finite-union estimates. -/
theorem tsum_lateOnThresholdEvent_ne_top
    (μ : Measure (ℕ → Site)) (ψ : ℕ → ℕ) (k : ℕ)
    (hlower : (∑' m : ℕ, μ (lowerMaxEvent ψ m)) ≠ ∞) :
    (∑' m : ℕ, μ (lateOnThresholdEvent ψ m k)) ≠ ∞ := by
  have hle : (∑' m : ℕ, μ (lateOnThresholdEvent ψ m k)) ≤
      ∑' m : ℕ, μ (lowerMaxEvent ψ m) :=
    ENNReal.tsum_le_tsum fun m ↦
      measure_lateOnThresholdEvent_le_lowerMaxEvent μ ψ m k
  exact ne_top_of_le_ne_top hlower hle

/-- Consequently, every one of the six paired bad-horizon contributions is
summable under the same lower-tail input. -/
theorem tsum_pairingLateHorizonEvent_ne_top
    (μ : Measure (ℕ → Site)) (ψ : ℕ → ℕ) (i : Fin 6)
    (hlower : (∑' m : ℕ, μ (lowerMaxEvent ψ m)) ≠ ∞) :
    (∑' m : ℕ, μ (pairingLateHorizonEvent ψ m i)) ≠ ∞ := by
  have hle : (∑' m : ℕ, μ (pairingLateHorizonEvent ψ m i)) ≤
      ∑' m : ℕ, μ (lateOnThresholdEvent ψ m 4) :=
    ENNReal.tsum_le_tsum fun m ↦ measure_mono
      (pairingLateHorizonEvent_subset_lateOnThresholdEvent ψ m i)
  exact ne_top_of_le_ne_top
    (tsum_lateOnThresholdEvent_ne_top μ ψ 4 hlower) hle

/-- First Borel--Cantelli turns the same summability input into the eventual
cutoff `T_m^k ≤ ψ_m` on every occurrence of `M_m^k`. -/
theorem ae_eventually_threshold_le_horizon_on_M
    (μ : Measure (ℕ → Site)) (ψ : ℕ → ℕ) (k : ℕ)
    (hlower : (∑' m : ℕ, μ (lowerMaxEvent ψ m)) ≠ ∞) :
    ∀ᵐ s ∂μ, ∀ᶠ m : ℕ in atTop,
      s ∈ thresholdTimeEventK m k →
        firstKSitesReachLevel m k s ≤ (ψ m : WithTop ℕ) := by
  have hae := MeasureTheory.ae_eventually_notMem
    (tsum_lateOnThresholdEvent_ne_top μ ψ k hlower)
  filter_upwards [hae] with s hs
  filter_upwards [hs] with m hm
  intro hM
  by_contra hnot
  have hlate : (ψ m : WithTop ℕ) < firstKSitesReachLevel m k s := by
    simpa only [not_le] using hnot
  exact hm ⟨hlate, hM⟩

/-- The concrete `k=4` form consumed by the four-favourite screening. -/
theorem ae_eventually_fourth_threshold_le_nearCriticalHorizon
    (hlower : (∑' m : ℕ,
      simpleRandomWalkLaw (lowerMaxEvent nearCriticalHorizon m)) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ hlozThresholdTimeEvent m →
        firstKSitesReachLevel m 4 s ≤
          (nearCriticalHorizon m : WithTop ℕ) := by
  simpa only [thresholdTimeEventK_four] using
    (ae_eventually_threshold_le_horizon_on_M simpleRandomWalkLaw
      nearCriticalHorizon 4 hlower)

/-! ### The named Proposition-1.3 lower-tail event -/

/-- The threshold in HLOZ Proposition 1.3, with our fixed positive `δ`. -/
noncomputable def proposition13Threshold (n : ℕ) : ℝ :=
  Real.pi⁻¹ * Real.log (n : ℝ) ^ 2 -
    Real.log (n : ℝ) ^ lowerTailExponent

/-- The exact source horizon eventually puts level `m` strictly below the
Proposition-1.3 lower-tail threshold.  This includes both the real-power
comparison and the upward-rounding error. -/
theorem eventually_level_lt_proposition13Threshold_nearCriticalHorizon :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < proposition13Threshold (nearCriticalHorizon m) := by
  filter_upwards [eventually_log_horizon_rpow_lt_two_leading_rpow,
    eventually_ge_atTop 1] with m hpow hm1
  have hmpos : 0 < m := by omega
  have hLnonneg := nearCriticalLogHorizon_nonneg m
  have hlognonneg := Real.log_natCast_nonneg (nearCriticalHorizon m)
  have hLlog := nearCriticalLogHorizon_le_log_horizon m
  have hsq : nearCriticalLogHorizon m ^ 2 ≤
      Real.log (nearCriticalHorizon m : ℝ) ^ 2 := by
    nlinarith
  have hscaled : Real.pi⁻¹ * nearCriticalLogHorizon m ^ 2 ≤
      Real.pi⁻¹ * Real.log (nearCriticalHorizon m : ℝ) ^ 2 := by
    gcongr
  have hcross := horizon_cross_term_eq_two_leading_rpow m hmpos
  have hexpand :=
    pi_inverse_mul_logHorizon_sq_ge_baseline_add_cross m
  unfold proposition13Threshold
  rw [hcross] at hexpand
  nlinarith

/-- The exact event bounded in the lower-tail theorem. -/
def proposition13LowerTailEvent (n : ℕ) : Set (ℕ → Site) :=
  {s | (maxLocalTime s n : ℝ) < proposition13Threshold n}

theorem measurableSet_proposition13LowerTailEvent (n : ℕ) :
    MeasurableSet (proposition13LowerTailEvent n) := by
  exact measurableSet_lt
    ((measurable_of_countable (fun k : ℕ ↦ (k : ℝ))).comp
      (measurable_maxLocalTime_eval n)) measurable_const

/-- Once the deterministic threshold exceeds level `m`, the elementary
event `M_{ψ_m} ≤ m` is a subevent of the named Proposition-1.3 event. -/
theorem lowerMaxEvent_subset_proposition13LowerTailEvent
    (ψ : ℕ → ℕ) (m : ℕ)
    (hthreshold : (m : ℝ) < proposition13Threshold (ψ m)) :
    lowerMaxEvent ψ m ⊆ proposition13LowerTailEvent (ψ m) := by
  intro s hs
  change maxLocalTime s (ψ m) ≤ m at hs
  change (maxLocalTime s (ψ m) : ℝ) < proposition13Threshold (ψ m)
  exact (Nat.cast_le.mpr hs).trans_lt hthreshold

/-- The named Proposition-1.3 events control the elementary lower-maximum
events even though the analytic threshold comparison is only eventual. -/
theorem tsum_lowerMaxEvent_of_proposition13_lower_tail
    (μ : Measure (ℕ → Site)) [IsFiniteMeasure μ] (ψ : ℕ → ℕ)
    (hthreshold : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < proposition13Threshold (ψ m))
    (hprop13 : (∑' m : ℕ,
      μ (proposition13LowerTailEvent (ψ m))) ≠ ∞) :
    (∑' m : ℕ, μ (lowerMaxEvent ψ m)) ≠ ∞ := by
  apply ennreal_tsum_ne_top_of_eventually_le
    (fun m ↦ μ (lowerMaxEvent ψ m))
    (fun m ↦ μ (proposition13LowerTailEvent (ψ m)))
  · intro m
    exact measure_ne_top μ _
  · filter_upwards [hthreshold] with m hm
    exact measure_mono
      (lowerMaxEvent_subset_proposition13LowerTailEvent ψ m hm)
  · exact hprop13

/-- An eventually valid Proposition-1.3 estimate by any summable majorant
already implies the whole-tsum formulation above; finite exceptional levels
are absorbed using finiteness of the measure. -/
theorem tsum_proposition13LowerTailEvent_of_eventually_bound
    (μ : Measure (ℕ → Site)) [IsFiniteMeasure μ] (ψ : ℕ → ℕ)
    (q : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ m : ℕ in atTop,
      μ (proposition13LowerTailEvent (ψ m)) ≤ q m)
    (hq : (∑' m : ℕ, q m) ≠ ∞) :
    (∑' m : ℕ, μ (proposition13LowerTailEvent (ψ m))) ≠ ∞ := by
  exact ennreal_tsum_ne_top_of_eventually_le
    (fun m ↦ μ (proposition13LowerTailEvent (ψ m))) q
    (fun m ↦ measure_ne_top μ _) hbound hq

/-- A summable sequence of the named lower-tail probabilities therefore
supplies both the HLOZ bad-horizon summation and Borel--Cantelli cutoff. -/
theorem tsum_late_of_proposition13_lower_tail
    (μ : Measure (ℕ → Site)) [IsFiniteMeasure μ] (ψ : ℕ → ℕ) (k : ℕ)
    (hthreshold : ∀ᶠ m : ℕ in atTop,
      (m : ℝ) < proposition13Threshold (ψ m))
    (hprop13 : (∑' m : ℕ, μ (proposition13LowerTailEvent (ψ m))) ≠ ∞) :
    (∑' m : ℕ, μ (lateOnThresholdEvent ψ m k)) ≠ ∞ := by
  apply tsum_lateOnThresholdEvent_ne_top μ ψ k
  exact tsum_lowerMaxEvent_of_proposition13_lower_tail
    μ ψ hthreshold hprop13

/-- Direct source specialization using the exact horizon (4.10). -/
theorem tsum_late_nearCritical_of_proposition13_lower_tail
    (k : ℕ)
    (hprop13 : (∑' m : ℕ,
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m))) ≠ ∞) :
    (∑' m : ℕ,
      simpleRandomWalkLaw
        (lateOnThresholdEvent nearCriticalHorizon m k)) ≠ ∞ :=
  tsum_late_of_proposition13_lower_tail simpleRandomWalkLaw
    nearCriticalHorizon k
    eventually_level_lt_proposition13Threshold_nearCriticalHorizon hprop13

/-- Source-facing six-pairing form of the summable bad-horizon contribution. -/
theorem tsum_pairingLate_nearCritical_of_proposition13_lower_tail
    (i : Fin 6)
    (hprop13 : (∑' m : ℕ,
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m))) ≠ ∞) :
    (∑' m : ℕ,
      simpleRandomWalkLaw
        (pairingLateHorizonEvent nearCriticalHorizon m i)) ≠ ∞ := by
  apply tsum_pairingLateHorizonEvent_ne_top
  exact tsum_lowerMaxEvent_of_proposition13_lower_tail
    simpleRandomWalkLaw nearCriticalHorizon
    eventually_level_lt_proposition13Threshold_nearCriticalHorizon hprop13

/-- Eventual-bound version of the six-pairing bad-horizon summation. -/
theorem tsum_pairingLate_nearCritical_of_eventually_prop13_bound
    (i : Fin 6) (q : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m)) ≤ q m)
    (hq : (∑' m : ℕ, q m) ≠ ∞) :
    (∑' m : ℕ,
      simpleRandomWalkLaw
        (pairingLateHorizonEvent nearCriticalHorizon m i)) ≠ ∞ := by
  apply tsum_pairingLate_nearCritical_of_proposition13_lower_tail
  exact tsum_proposition13LowerTailEvent_of_eventually_bound
    simpleRandomWalkLaw nearCriticalHorizon q hbound hq

/-- The same exact input yields the pathwise eventual stopping cutoff needed
before the Proposition-4.5/4.7 finite-horizon arguments. -/
theorem ae_eventually_threshold_le_nearCriticalHorizon_of_proposition13
    (k : ℕ)
    (hprop13 : (∑' m : ℕ,
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m))) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ thresholdTimeEventK m k →
        firstKSitesReachLevel m k s ≤
          (nearCriticalHorizon m : WithTop ℕ) := by
  apply ae_eventually_threshold_le_horizon_on_M
  exact tsum_lowerMaxEvent_of_proposition13_lower_tail
    simpleRandomWalkLaw nearCriticalHorizon
    eventually_level_lt_proposition13Threshold_nearCriticalHorizon hprop13

/-- Strongest source-facing form: only an eventually valid lower-tail bound
at the exact rounded horizons, together with summability of its majorant, is
needed for the almost-sure cutoff. -/
theorem ae_eventually_threshold_le_nearCriticalHorizon_of_eventually_prop13_bound
    (k : ℕ) (q : ℕ → ℝ≥0∞)
    (hbound : ∀ᶠ m : ℕ in atTop,
      simpleRandomWalkLaw
        (proposition13LowerTailEvent (nearCriticalHorizon m)) ≤ q m)
    (hq : (∑' m : ℕ, q m) ≠ ∞) :
    ∀ᵐ s ∂simpleRandomWalkLaw, ∀ᶠ m : ℕ in atTop,
      s ∈ thresholdTimeEventK m k →
        firstKSitesReachLevel m k s ≤
          (nearCriticalHorizon m : WithTop ℕ) := by
  apply ae_eventually_threshold_le_nearCriticalHorizon_of_proposition13
  exact tsum_proposition13LowerTailEvent_of_eventually_bound
    simpleRandomWalkLaw nearCriticalHorizon q hbound hq

end Erdos1166.HLOZNearCriticalBridge
