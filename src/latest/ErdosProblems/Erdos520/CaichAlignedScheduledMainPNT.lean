import ErdosProblems.Erdos520.CaichScheduledMainCleanup
import ErdosProblems.Erdos520.AlignedClampedSchedule
import ErdosProblems.Erdos520.AlignedSmoothContribution
import ErdosProblems.Erdos520.CaichWoverX

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Effective-PNT input on the aligned capped schedule

This file specializes the floor-safe short-prime estimate to the aligned
integer schedule.  The literal near predicate is the one used in Caich's
long-ratio split.  Its size is of order `100 K ell log ell`; consequently
the honest coefficient is a fixed multiple of `K * ell * log ell`, rather
than the unscaled `ell * log ell`.
-/

/-- The literal near/active predicate on the clamped aligned schedule. -/
def caichAlignedCappedNear
    (K S ell x j : ℕ) : Prop :=
  alignedThinEndpoint K (clampedAlignedScale S ell) j < x ∧
    Real.log (x : ℝ) ≤
      (ell : ℝ) ^ (100 * K) *
        Real.log
          (alignedThinEndpoint K (clampedAlignedScale S ell) j : ℝ)

/-- A power-of-two baseline exactly one binary exponent below the left
endpoint.  It is floor-safe and loses at most a factor two in logarithms. -/
def caichAlignedPNTBaseline (K L j : ℕ) : ℕ :=
  2 ^ (alignedThinExponent K L j - 1)

theorem two_mul_caichAlignedPNTBaseline
    (K L j : ℕ) :
    2 * caichAlignedPNTBaseline K L j =
      alignedThinEndpoint K L j := by
  have hE : 1 ≤ alignedThinExponent K L j :=
    alignedThinExponent_pos K L j
  unfold caichAlignedPNTBaseline alignedThinEndpoint
  calc
    2 * 2 ^ (alignedThinExponent K L j - 1) =
        2 ^ (alignedThinExponent K L j - 1) * 2 := by omega
    _ = 2 ^ ((alignedThinExponent K L j - 1) + 1) := by
      rw [pow_succ]
    _ = 2 ^ alignedThinExponent K L j := by congr 1 <;> omega

theorem two_le_caichAlignedPNTBaseline
    {K L j : ℕ} (hL : 4 ≤ L) (hK : 1 ≤ K) :
    2 ≤ caichAlignedPNTBaseline K L j := by
  have hscale : L ≤ alignedThinExponent K L j := by
    exact (scale_le_alignedInitialExponent hK hL).trans
      (ceilThinGrow_seed_le L (alignedOuterExponent K (L - 2)) j)
  unfold caichAlignedPNTBaseline
  change 2 ^ 1 ≤ 2 ^ (alignedThinExponent K L j - 1)
  apply Nat.pow_le_pow_right (by norm_num)
  omega

theorem log_caichAlignedPNTBaseline
    {K L j : ℕ} (hL : 4 ≤ L) (hK : 1 ≤ K) :
    Real.log (caichAlignedPNTBaseline K L j : ℝ) =
      ((alignedThinExponent K L j - 1 : ℕ) : ℝ) * Real.log 2 := by
  unfold caichAlignedPNTBaseline
  rw [show (((2 ^ (alignedThinExponent K L j - 1) : ℕ) : ℝ)) =
      (2 : ℝ) ^ (alignedThinExponent K L j - 1) by norm_cast,
    Real.log_pow]

/-- The baseline logarithm is at least half the left-endpoint logarithm. -/
theorem half_log_alignedThinEndpoint_le_log_baseline
    {K L j : ℕ} (hL : 4 ≤ L) (hK : 1 ≤ K) :
    (1 / 2 : ℝ) *
        Real.log (alignedThinEndpoint K L j : ℝ) ≤
      Real.log (caichAlignedPNTBaseline K L j : ℝ) := by
  have hscale : L ≤ alignedThinExponent K L j := by
    exact (scale_le_alignedInitialExponent hK hL).trans
      (ceilThinGrow_seed_le L (alignedOuterExponent K (L - 2)) j)
  rw [log_alignedThinEndpoint,
    log_caichAlignedPNTBaseline hL hK]
  have hlog : 0 ≤ Real.log (2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  rw [show (1 / 2 : ℝ) *
      ((alignedThinExponent K L j : ℝ) * Real.log 2) =
      ((alignedThinExponent K L j : ℝ) / 2) * Real.log 2 by ring]
  apply mul_le_mul_of_nonneg_right _ hlog
  have hnat : alignedThinExponent K L j ≤
      2 * (alignedThinExponent K L j - 1) := by omega
  have hreal : (alignedThinExponent K L j : ℝ) ≤
      2 * (alignedThinExponent K L j - 1 : ℕ) := by
    exact_mod_cast hnat
  linarith

/-- Generic floor geometry: throughout a capped block, a baseline at most
half the left endpoint lies below the moving lower cutoff. -/
theorem baseline_le_caichLambdaLowerCutoff_of_two_mul_le_left
    {x X left baseline : ℕ} {z : ℝ}
    (hX : 2 ≤ X) (hz : 0 < z)
    (hzUpper : z ≤ (x : ℝ) / (left : ℝ))
    (hleft : 0 < left) (hhalf : 2 * baseline ≤ left) :
    baseline ≤ caichLambdaLowerCutoff x X z := by
  unfold caichLambdaLowerCutoff
  apply Nat.le_floor
  have hxz : (left : ℝ) ≤ (x : ℝ) / z := by
    have hleftR : (0 : ℝ) < left := by exact_mod_cast hleft
    have hmul : z * (left : ℝ) ≤ (x : ℝ) :=
      (le_div_iff₀ hleftR).mp hzUpper
    exact (le_div_iff₀ hz).2 (by
      simpa only [mul_comm] using! hmul)
  have hXR : (2 : ℝ) ≤ X := by exact_mod_cast hX
  have hfactorPos : (0 : ℝ) < 1 + 1 / (X : ℝ) := by positivity
  have hfactor : 1 + 1 / (X : ℝ) ≤ 3 / 2 := by
    have hXpos : (0 : ℝ) < X := by positivity
    have hinv : 1 / (X : ℝ) ≤ 1 / 2 := by
      exact one_div_le_one_div_of_le (by norm_num) hXR
    linarith
  have hhalfR : (baseline : ℝ) ≤ (left : ℝ) / 2 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
      have : (2 : ℝ) * baseline ≤ left := by exact_mod_cast hhalf
      simpa only [mul_comm] using! this)
  calc
    (baseline : ℝ) ≤ (left : ℝ) / 2 := hhalfR
    _ ≤ ((x : ℝ) / z) / (1 + 1 / (X : ℝ)) := by
      apply (le_div_iff₀ hfactorPos).2
      calc
        (left : ℝ) / 2 * (1 + 1 / (X : ℝ)) ≤
            (left : ℝ) / 2 * (3 / 2) := by
          gcongr
        _ ≤ (left : ℝ) := by nlinarith
        _ ≤ (x : ℝ) / z := hxz
    _ = (x : ℝ) / (z * (1 + 1 / (X : ℝ))) := by rw [div_div]

/-- One aligned step increases the ordinary endpoint logarithm by at most
a factor `3/2`. -/
theorem log_alignedThinEndpoint_succ_le_three_halves
    {K L j : ℕ} (hK : 1 ≤ K) (hL : 4 ≤ L) :
    Real.log (alignedThinEndpoint K L (j + 1) : ℝ) ≤
      (3 / 2 : ℝ) * Real.log (alignedThinEndpoint K L j : ℝ) := by
  let E := alignedThinExponent K L j
  have hEpos : 0 < E := alignedThinExponent_pos K L j
  have hseed : L ≤ alignedOuterExponent K (L - 2) :=
    scale_le_alignedInitialExponent hK hL
  have hElarge : L ≤ E :=
    hseed.trans (ceilThinGrow_seed_le L
      (alignedOuterExponent K (L - 2)) j)
  have hratio := cast_ceilThinStep_div_le
    (show 0 < L by omega) hEpos hElarge
  have hLpos : (0 : ℝ) < L := by positivity
  have hone : 1 + 2 / (L : ℝ) ≤ (3 / 2 : ℝ) := by
    have hLR : (4 : ℝ) ≤ L := by exact_mod_cast hL
    have hdiv : 2 / (L : ℝ) ≤ 1 / 2 := by
      exact (div_le_iff₀ hLpos).2 (by nlinarith)
    linarith
  have hratio' : (ceilThinStep L E : ℝ) / (E : ℝ) ≤
      (3 / 2 : ℝ) := hratio.trans hone
  have hstep : (ceilThinStep L E : ℝ) ≤
      (3 / 2 : ℝ) * (E : ℝ) := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < E)).mp hratio'
  rw [log_alignedThinEndpoint, log_alignedThinEndpoint]
  change (ceilThinStep L E : ℝ) * Real.log 2 ≤
    (3 / 2 : ℝ) * ((E : ℝ) * Real.log 2)
  nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

/-- The capped right endpoint costs at most a factor three against the
floor-safe PNT baseline. -/
theorem log_cappedAlignedRight_le_three_mul_log_baseline
    {K L j x : ℕ} (hK : 1 ≤ K) (hL : 4 ≤ L)
    (hright : 2 ≤ caichCappedThinEndpoint x
      (alignedThinEndpoint K L) (j + 1)) :
    Real.log (caichCappedThinEndpoint x
        (alignedThinEndpoint K L) (j + 1) : ℝ) ≤
      3 * Real.log (caichAlignedPNTBaseline K L j : ℝ) := by
  let b := caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1)
  have hbpos : (0 : ℝ) < b := by positivity
  have hbendpoint : b ≤ alignedThinEndpoint K L (j + 1) := by
    exact min_le_left _ _
  have hlogCap : Real.log (b : ℝ) ≤
      Real.log (alignedThinEndpoint K L (j + 1) : ℝ) := by
    apply Real.log_le_log hbpos
    exact_mod_cast hbendpoint
  have hstep := log_alignedThinEndpoint_succ_le_three_halves
    (K := K) (L := L) (j := j) hK hL
  have hhalf := half_log_alignedThinEndpoint_le_log_baseline
    (K := K) (L := L) (j := j) hL hK
  dsimp only [b] at hlogCap ⊢
  linarith

/-- Pointwise aligned short-window estimate once the uniform effective-PNT
statement has reached the chosen baseline and the two elementary smoothing
inequalities have been verified. -/
theorem caichAlignedCappedShortWindow_le_of_PNTBaseline
    {K L j x X A : ℕ}
    (hK : 1 ≤ K) (hL : 4 ≤ L) (hx : 0 < x)
    (hactive : alignedThinEndpoint K L j < x)
    (hX : 2 ≤ X)
    (hfour : 4 * X ≤ alignedThinEndpoint K L j)
    (hpoly : (X : ℝ) ≤
      Real.log (caichAlignedPNTBaseline K L j : ℝ) ^ A)
    (hprime : ∀ {x' X' a b : ℕ} {z : ℝ},
      0 < z → 2 ≤ X' →
      caichAlignedPNTBaseline K L j ≤
        caichLambdaLowerCutoff x' X' z →
      (X' : ℝ) ≤
        Real.log (caichAlignedPNTBaseline K L j : ℝ) ^ A →
      2 * X' ≤ caichLambdaLowerCutoff x' X' z →
      caichShortWindowReciprocalMass (X' : ℝ) x' a b z ≤
        3 / ((X' : ℝ) *
          Real.log (caichAlignedPNTBaseline K L j : ℝ))) :
    ∀ z ∈ Ioc
      ((x : ℝ) /
        (caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1) : ℝ))
      ((x : ℝ) /
        (caichCappedThinEndpoint x (alignedThinEndpoint K L) j : ℝ)),
      caichShortWindowReciprocalMass (X : ℝ) x
          (caichCappedThinEndpoint x (alignedThinEndpoint K L) j)
          (caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1)) z ≤
        9 / ((X : ℝ) * Real.log
          (caichCappedThinEndpoint x
            (alignedThinEndpoint K L) (j + 1) : ℝ)) := by
  intro z hz
  have hleftEq : caichCappedThinEndpoint x
      (alignedThinEndpoint K L) j = alignedThinEndpoint K L j := by
    exact caichCappedThinEndpoint_eq_left hactive.le
  have hright : 2 ≤ caichCappedThinEndpoint x
      (alignedThinEndpoint K L) (j + 1) := by
    unfold caichCappedThinEndpoint
    exact le_min (two_le_alignedThinEndpoint K L (j + 1)) (by omega)
  have hzpos : 0 < z := by
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hbR : (0 : ℝ) < caichCappedThinEndpoint x
        (alignedThinEndpoint K L) (j + 1) := by positivity
    exact (div_pos hxR hbR).trans hz.1
  have hbaseLower : caichAlignedPNTBaseline K L j ≤
      caichLambdaLowerCutoff x X z := by
    apply baseline_le_caichLambdaLowerCutoff_of_two_mul_le_left
      hX hzpos
    · simpa only [hleftEq] using! hz.2
    · have := two_le_alignedThinEndpoint K L j
      omega
    · rw [two_mul_caichAlignedPNTBaseline]
  have hlarge : 2 * X ≤ caichLambdaLowerCutoff x X z := by
    apply (show 2 * X ≤ caichAlignedPNTBaseline K L j by
      have hdouble := two_mul_caichAlignedPNTBaseline K L j
      omega).trans hbaseLower
  have hp := hprime
    (a := caichCappedThinEndpoint x (alignedThinEndpoint K L) j)
    (b := caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1))
    hzpos hX hbaseLower hpoly hlarge
  have hlogRight := log_cappedAlignedRight_le_three_mul_log_baseline
    (K := K) (L := L) (j := j) (x := x) hK hL hright
  have hlogBase : 0 < Real.log (caichAlignedPNTBaseline K L j : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < caichAlignedPNTBaseline K L j by
        exact lt_of_lt_of_le Nat.one_lt_two
          (two_le_caichAlignedPNTBaseline hL hK)))
  have hlogRightPos : 0 < Real.log
      (caichCappedThinEndpoint x
        (alignedThinEndpoint K L) (j + 1) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 <
      caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1) by omega))
  have hXR : (0 : ℝ) < X := by positivity
  calc
    caichShortWindowReciprocalMass (X : ℝ) x
        (caichCappedThinEndpoint x (alignedThinEndpoint K L) j)
        (caichCappedThinEndpoint x (alignedThinEndpoint K L) (j + 1)) z ≤
      3 / ((X : ℝ) *
        Real.log (caichAlignedPNTBaseline K L j : ℝ)) := hp
    _ ≤ 9 / ((X : ℝ) * Real.log
        (caichCappedThinEndpoint x
          (alignedThinEndpoint K L) (j + 1) : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hXR hlogBase)
        (mul_pos hXR hlogRightPos)).2
      nlinarith

/-- Uncapped version used by the least-overshoot endpoint chain. -/
theorem caichAlignedShortWindow_le_of_PNTBaseline
    {K L j x X A : ℕ}
    (hK : 1 ≤ K) (hL : 4 ≤ L) (hx : 0 < x)
    (hX : 2 ≤ X)
    (hfour : 4 * X ≤ alignedThinEndpoint K L j)
    (hpoly : (X : ℝ) ≤
      Real.log (caichAlignedPNTBaseline K L j : ℝ) ^ A)
    (hprime : ∀ {x' X' a b : ℕ} {z : ℝ},
      0 < z → 2 ≤ X' →
      caichAlignedPNTBaseline K L j ≤
        caichLambdaLowerCutoff x' X' z →
      (X' : ℝ) ≤
        Real.log (caichAlignedPNTBaseline K L j : ℝ) ^ A →
      2 * X' ≤ caichLambdaLowerCutoff x' X' z →
      caichShortWindowReciprocalMass (X' : ℝ) x' a b z ≤
        3 / ((X' : ℝ) *
          Real.log (caichAlignedPNTBaseline K L j : ℝ))) :
    ∀ z ∈ Ioc
      ((x : ℝ) / (alignedThinEndpoint K L (j + 1) : ℝ))
      ((x : ℝ) / (alignedThinEndpoint K L j : ℝ)),
      caichShortWindowReciprocalMass (X : ℝ) x
          (alignedThinEndpoint K L j)
          (alignedThinEndpoint K L (j + 1)) z ≤
        9 / ((X : ℝ) *
          Real.log (alignedThinEndpoint K L (j + 1) : ℝ)) := by
  intro z hz
  have hzpos : 0 < z := by
    have hxR : (0 : ℝ) < x := by exact_mod_cast hx
    have hrightR : (0 : ℝ) < alignedThinEndpoint K L (j + 1) := by
      exact_mod_cast (show 0 < alignedThinEndpoint K L (j + 1) by
        have := two_le_alignedThinEndpoint K L (j + 1)
        omega)
    exact (div_pos hxR hrightR).trans hz.1
  have hbaseLower : caichAlignedPNTBaseline K L j ≤
      caichLambdaLowerCutoff x X z := by
    apply baseline_le_caichLambdaLowerCutoff_of_two_mul_le_left
      hX hzpos hz.2
    · have := two_le_alignedThinEndpoint K L j
      omega
    · rw [two_mul_caichAlignedPNTBaseline]
  have hlarge : 2 * X ≤ caichLambdaLowerCutoff x X z := by
    apply (show 2 * X ≤ caichAlignedPNTBaseline K L j by
      have hdouble := two_mul_caichAlignedPNTBaseline K L j
      omega).trans hbaseLower
  have hp := hprime
    (a := alignedThinEndpoint K L j)
    (b := alignedThinEndpoint K L (j + 1))
    hzpos hX hbaseLower hpoly hlarge
  have hstep := log_alignedThinEndpoint_succ_le_three_halves
    (K := K) (L := L) (j := j) hK hL
  have hhalf := half_log_alignedThinEndpoint_le_log_baseline
    (K := K) (L := L) (j := j) hL hK
  have hlogRight : Real.log (alignedThinEndpoint K L (j + 1) : ℝ) ≤
      3 * Real.log (caichAlignedPNTBaseline K L j : ℝ) := by
    linarith
  have hlogBase : 0 < Real.log (caichAlignedPNTBaseline K L j : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < caichAlignedPNTBaseline K L j by
        exact lt_of_lt_of_le Nat.one_lt_two
          (two_le_caichAlignedPNTBaseline hL hK)))
  have hlogRightPos : 0 <
      Real.log (alignedThinEndpoint K L (j + 1) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 <
      alignedThinEndpoint K L (j + 1) by
        exact Nat.one_lt_two.trans_le
          (two_le_alignedThinEndpoint K L (j + 1))))
  have hXR : (0 : ℝ) < X := by positivity
  calc
    caichShortWindowReciprocalMass (X : ℝ) x
        (alignedThinEndpoint K L j) (alignedThinEndpoint K L (j + 1)) z ≤
      3 / ((X : ℝ) *
        Real.log (caichAlignedPNTBaseline K L j : ℝ)) := hp
    _ ≤ 9 / ((X : ℝ) *
        Real.log (alignedThinEndpoint K L (j + 1) : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hXR hlogBase)
        (mul_pos hXR hlogRightPos)).2
      nlinarith

/-- Exponent supplied to the effective PNT after transporting Caich's
smoothing parameter across the literal near relation. -/
def caichAlignedEffectivePNTExponent (r K : ℕ) : ℕ :=
  (200 * K + 2) * caichWSmoothingExponent r

theorem caichWSmoothingParameterNat_cast_le
    {r x : ℕ} (hlog : 1 ≤ Real.log (x : ℝ)) :
    (caichWSmoothingParameterNat r x : ℝ) ≤
      caichWSmoothingParameter r x := by
  have hW : 1 ≤ caichWSmoothingParameter r x := by
    unfold caichWSmoothingParameter
    exact one_le_pow₀ hlog
  have hfloor : 1 ≤ Nat.floor (caichWSmoothingParameter r x) :=
    Nat.le_floor (by simpa using! hW)
  unfold caichWSmoothingParameterNat
  rw [max_eq_right hfloor]
  exact Nat.floor_le (zero_le_one.trans hW)

theorem two_le_caichWSmoothingParameterNat
    {r x : ℕ} (hlog : 2 ≤ Real.log (x : ℝ)) :
    2 ≤ caichWSmoothingParameterNat r x := by
  have hW : (2 : ℝ) ≤ caichWSmoothingParameter r x := by
    unfold caichWSmoothingParameter caichWSmoothingExponent
    have hexp : 1 ≤ 8 * r ^ 2 - 8 * r + 4 := by omega
    exact hlog.trans (le_self_pow₀ (one_le_two.trans hlog) (by omega))
  have hfloor : 2 ≤ Nat.floor (caichWSmoothingParameter r x) :=
    Nat.le_floor hW
  unfold caichWSmoothingParameterNat
  omega

/-- The literal near relation transports the natural smoothing parameter
to a fixed power of the local PNT baseline. -/
theorem caichAlignedNear_smoothing_polylog
    {r K L x j : ℕ} (hK : 1 ≤ K) (hL : 5 ≤ L)
    (hactive : alignedThinEndpoint K L j < x)
    (hnear : Real.log (x : ℝ) ≤
      (L : ℝ) ^ (100 * K) *
        Real.log (alignedThinEndpoint K L j : ℝ)) :
    (caichWSmoothingParameterNat r x : ℝ) ≤
      Real.log (caichAlignedPNTBaseline K L j : ℝ) ^
        caichAlignedEffectivePNTExponent r K := by
  let B : ℝ := Real.log (caichAlignedPNTBaseline K L j : ℝ)
  have hleftLog : (L : ℝ) ≤
      Real.log (alignedThinEndpoint K L j : ℝ) :=
    scale_le_log_alignedThinEndpoint hK hL
  have hhalf := half_log_alignedThinEndpoint_le_log_baseline
    (K := K) (L := L) (j := j) (by omega) hK
  have hBtwo : 2 ≤ B := by
    dsimp only [B]
    have hLR : (5 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hleftB : Real.log (alignedThinEndpoint K L j : ℝ) ≤
      B ^ 2 := by
    have htwo : Real.log (alignedThinEndpoint K L j : ℝ) ≤
        2 * B := by
      dsimp only [B] at hhalf ⊢
      linarith
    exact htwo.trans (by nlinarith)
  have hLB : (L : ℝ) ≤ B ^ 2 := hleftLog.trans hleftB
  have hlogxBound : Real.log (x : ℝ) ≤
      B ^ (200 * K + 2) := by
    calc
      Real.log (x : ℝ) ≤
          (L : ℝ) ^ (100 * K) *
            Real.log (alignedThinEndpoint K L j : ℝ) := hnear
      _ ≤ (B ^ 2) ^ (100 * K) * B ^ 2 := by
        exact mul_le_mul
          (pow_le_pow_left₀ (by positivity) hLB (100 * K)) hleftB
          (Real.log_nonneg (by exact_mod_cast
            (show 1 ≤ alignedThinEndpoint K L j by
              exact one_le_two.trans (two_le_alignedThinEndpoint K L j))))
          (pow_nonneg (by positivity) _)
      _ = B ^ (200 * K + 2) := by
        rw [← pow_mul, ← pow_add]
        congr 1 <;> omega
  have hxThree : 3 ≤ x := by
    exact (two_le_alignedThinEndpoint K L j).trans_lt hactive
  have hlogxOne : 1 ≤ Real.log (x : ℝ) := by
    have hexp : Real.exp 1 < (x : ℝ) := by
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hxThree)
    simpa only [Real.exp_one_rpow] using!
      (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < x)).2 hexp.le
  calc
    (caichWSmoothingParameterNat r x : ℝ) ≤
        caichWSmoothingParameter r x :=
      caichWSmoothingParameterNat_cast_le hlogxOne
    _ = Real.log (x : ℝ) ^ caichWSmoothingExponent r := rfl
    _ ≤ (B ^ (200 * K + 2)) ^ caichWSmoothingExponent r := by
      exact pow_le_pow_left₀ (Real.log_nonneg
        (by exact_mod_cast (show 1 ≤ x by omega))) hlogxBound _
    _ = B ^ caichAlignedEffectivePNTExponent r K := by
      rw [← pow_mul]
      rfl

/-- Once a single explicit exponent inequality holds, every selected test
point has smoothing width at most one quarter of the initial aligned
endpoint. -/
theorem four_mul_caichWSmoothingParameterNat_le_alignedInitial
    {r K m ell i : ℕ} (hK : 1 ≤ K)
    (hi : i ∈ alignedRootExpTests K m ell)
    (hexponent : caichWSmoothingExponent r * ell ^ K + 2 ≤
      alignedOuterExponent K (ell - 2)) :
    4 * caichWSmoothingParameterNat r (alignedRootExpTestPoint m i) ≤
      alignedThinEndpoint K ell 0 := by
  let x := alignedRootExpTestPoint m i
  let E := alignedOuterExponent K ell
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hxUpper : x ≤ alignedOuterEndpoint K ell := by
    unfold alignedRootExpTests at hi
    rw [if_neg (by omega : ¬ell < 5)] at hi
    exact (Finset.mem_filter.mp hi).2.2
  have hxLower : alignedThinEndpoint K ell 0 < x :=
    alignedThinInitial_lt_testPoint_of_mem hi
  have hxThree : 3 ≤ x :=
    (two_le_alignedThinEndpoint K ell 0).trans_lt hxLower
  have hlogxOne : 1 ≤ Real.log (x : ℝ) := by
    have hexp : Real.exp 1 < (x : ℝ) :=
      Real.exp_one_lt_three.trans_le (by exact_mod_cast hxThree)
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < x)).2 hexp.le
  have hlogMono : Real.log (x : ℝ) ≤
      Real.log (alignedOuterEndpoint K ell : ℝ) := by
    apply Real.log_le_log (by positivity : (0 : ℝ) < x)
    exact_mod_cast hxUpper
  have hlogOuter : Real.log (alignedOuterEndpoint K ell : ℝ) ≤ E := by
    rw [log_alignedOuterEndpoint]
    dsimp only [E]
    have hE : (0 : ℝ) ≤ alignedOuterExponent K ell := by positivity
    nlinarith [Real.log_two_lt_d9]
  have hXreal : (caichWSmoothingParameterNat r x : ℝ) ≤
      (E : ℝ) ^ caichWSmoothingExponent r := by
    calc
      (caichWSmoothingParameterNat r x : ℝ) ≤
          caichWSmoothingParameter r x :=
        caichWSmoothingParameterNat_cast_le hlogxOne
      _ = Real.log (x : ℝ) ^ caichWSmoothingExponent r := rfl
      _ ≤ Real.log (alignedOuterEndpoint K ell : ℝ) ^
          caichWSmoothingExponent r :=
        pow_le_pow_left₀ (Real.log_nonneg
          (by exact_mod_cast (show 1 ≤ x by omega))) hlogMono _
      _ ≤ (E : ℝ) ^ caichWSmoothingExponent r :=
        pow_le_pow_left₀ (Real.log_nonneg
          (by exact_mod_cast (show 1 ≤ alignedOuterEndpoint K ell by
            unfold alignedOuterEndpoint
            exact one_le_pow₀ (by norm_num)))) hlogOuter _
  have hXnat : caichWSmoothingParameterNat r x ≤
      E ^ caichWSmoothingExponent r := by
    exact_mod_cast hXreal
  have hpowExponent :
      4 * E ^ caichWSmoothingExponent r ≤
        2 ^ alignedOuterExponent K (ell - 2) := by
    dsimp only [E]
    unfold alignedOuterExponent
    rw [← pow_mul, show 4 = 2 ^ 2 by norm_num, ← pow_add]
    apply Nat.pow_le_pow_right (by norm_num)
    simpa only [mul_comm, add_comm] using! hexponent
  rw [alignedThinEndpoint_zero]
  unfold alignedOuterEndpoint
  exact (Nat.mul_le_mul_left 4 hXnat).trans hpowExponent

/-- The exponent inequality needed above holds eventually for every fixed
`r` and `K`. -/
theorem eventually_four_mul_caichWSmoothingParameterNat_le_alignedInitial
    (r m : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      4 * caichWSmoothingParameterNat r (alignedRootExpTestPoint m i) ≤
        alignedThinEndpoint K ell 0 := by
  have hpoly := eventually_mul_pow_le_two_pow_sub_two_mul_log_two
    (caichWSmoothingExponent r + 2 : ℝ) K
  filter_upwards [hpoly, eventually_ge_atTop (5 : ℕ)] with ell hpolyEll hell
  intro i hi
  apply four_mul_caichWSmoothingParameterNat_le_alignedInitial hK hi
  have hpowOne : 1 ≤ ell ^ K := one_le_pow₀ (by omega)
  have hleftNat : caichWSmoothingExponent r * ell ^ K + 2 ≤
      (caichWSmoothingExponent r + 2) * ell ^ K := by
    nlinarith
  have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have htwoReal : (((2 ^ (ell - 2) : ℕ) : ℝ) * Real.log 2) ≤
      (2 ^ (ell - 2) : ℕ) := by
    have hnonneg : (0 : ℝ) ≤ (2 ^ (ell - 2) : ℕ) := by positivity
    nlinarith
  have hpolyNat : (caichWSmoothingExponent r + 2) * ell ^ K ≤
      2 ^ (ell - 2) := by
    exact_mod_cast hpolyEll.trans htwoReal
  have hsubPow : ell - 2 ≤ (ell - 2) ^ K := by
    exact le_self_pow₀ (by omega) (by omega : K ≠ 0)
  exact hleftNat.trans (hpolyNat.trans
    (Nat.pow_le_pow_right (by norm_num) hsubPow))

theorem two_le_caichWSmoothingParameterNat_alignedTest
    {r K m ell i : ℕ} (hK : 1 ≤ K)
    (hi : i ∈ alignedRootExpTests K m ell) :
    2 ≤ caichWSmoothingParameterNat r (alignedRootExpTestPoint m i) := by
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hinitial : alignedThinEndpoint K ell 0 <
      alignedRootExpTestPoint m i :=
    alignedThinInitial_lt_testPoint_of_mem hi
  have hlogMono : Real.log (alignedThinEndpoint K ell 0 : ℝ) ≤
      Real.log (alignedRootExpTestPoint m i : ℝ) := by
    apply Real.log_le_log (by
      exact_mod_cast (show 0 < alignedThinEndpoint K ell 0 by
        unfold alignedThinEndpoint
        positivity))
    exact_mod_cast hinitial.le
  have hscale : (ell : ℝ) ≤
      Real.log (alignedThinEndpoint K ell 0 : ℝ) :=
    scale_le_log_alignedThinEndpoint hK hell
  apply two_le_caichWSmoothingParameterNat
  have hellR : (5 : ℝ) ≤ ell := by exact_mod_cast hell
  linarith

/-- Every fixed effective-PNT threshold is eventually below every aligned
baseline, uniformly in the block index. -/
theorem eventually_le_caichAlignedPNTBaseline
    (Y : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∀ᶠ ell : ℕ in atTop, ∀ j : ℕ,
      Y ≤ caichAlignedPNTBaseline K ell j := by
  filter_upwards [eventually_ge_atTop (max 4 (Y + 1))] with ell hell
  intro j
  have hfour : 4 ≤ ell := (le_max_left 4 (Y + 1)).trans hell
  have hYell : Y + 1 ≤ ell := (le_max_right 4 (Y + 1)).trans hell
  have hscale : ell ≤ alignedThinExponent K ell j := by
    exact (scale_le_alignedInitialExponent hK hfour).trans
      (ceilThinGrow_seed_le ell
        (alignedOuterExponent K (ell - 2)) j)
  have hpowSelf : ell ≤ 2 ^ (ell - 1) := by
    have hsub : ell - 1 + 1 = ell := by omega
    rw [← hsub]
    exact Nat.succ_le_iff.mpr (ell - 1).lt_two_pow_self
  unfold caichAlignedPNTBaseline
  have hexponent : ell - 1 ≤ alignedThinExponent K ell j - 1 := by omega
  exact (by omega : Y ≤ ell).trans
    (hpowSelf.trans (Nat.pow_le_pow_right (by norm_num) hexponent))

/-- Effective PNT supplies the exact `hshort` hypothesis for all literal
near blocks on the selected aligned mesh, eventually and uniformly. -/
theorem eventually_caichAlignedCappedNear_shortWindow
    (hPNT : EffectivePrimeCountingStatement)
    (r m S : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    ∀ᶠ ell : ℕ in atTop, ∀ i ∈ alignedRootExpTests K m ell,
      ∀ j ∈ Finset.range (clampedAlignedThinBlockCount K S ell),
      caichAlignedCappedNear K S ell (alignedRootExpTestPoint m i) j →
      ∀ z ∈ Ioc
        ((alignedRootExpTestPoint m i : ℝ) /
          (caichCappedThinEndpoint (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K (clampedAlignedScale S ell)) (j + 1) : ℝ))
        ((alignedRootExpTestPoint m i : ℝ) /
          (caichCappedThinEndpoint (alignedRootExpTestPoint m i)
            (alignedThinEndpoint K (clampedAlignedScale S ell)) j : ℝ)),
        caichShortWindowReciprocalMass
            (caichWSmoothingParameterNat r (alignedRootExpTestPoint m i) : ℝ)
            (alignedRootExpTestPoint m i)
            (caichCappedThinEndpoint (alignedRootExpTestPoint m i)
              (alignedThinEndpoint K (clampedAlignedScale S ell)) j)
            (caichCappedThinEndpoint (alignedRootExpTestPoint m i)
              (alignedThinEndpoint K (clampedAlignedScale S ell)) (j + 1)) z ≤
          9 / ((caichWSmoothingParameterNat r
              (alignedRootExpTestPoint m i) : ℝ) *
            Real.log
              (caichCappedThinEndpoint (alignedRootExpTestPoint m i)
                (alignedThinEndpoint K (clampedAlignedScale S ell)) (j + 1) : ℝ)) := by
  let A := caichAlignedEffectivePNTExponent r K
  have hprimeEvent :=
    eventually_caichShortWindowReciprocalMass_le_of_effectiveStatement hPNT A
  rw [eventually_atTop] at hprimeEvent
  obtain ⟨Y, hprimeY⟩ := hprimeEvent
  have hbaseline := eventually_le_caichAlignedPNTBaseline Y hK
  have hfour :=
    eventually_four_mul_caichWSmoothingParameterNat_le_alignedInitial r m hK
  filter_upwards [eventually_ge_atTop S, hbaseline, hfour] with
    ell hSell hbaselineEll hfourEll
  intro i hi j hj hnear
  have hscaleEq : clampedAlignedScale S ell = ell :=
    clampedAlignedScale_eq_of_ge hSell
  have hnear' : alignedThinEndpoint K ell j < alignedRootExpTestPoint m i ∧
      Real.log (alignedRootExpTestPoint m i : ℝ) ≤
        (ell : ℝ) ^ (100 * K) *
          Real.log (alignedThinEndpoint K ell j : ℝ) := by
    simpa only [caichAlignedCappedNear, hscaleEq] using! hnear
  have hell : 5 ≤ ell := five_le_of_mem_alignedRootExpTests hi
  have hX := two_le_caichWSmoothingParameterNat_alignedTest
    (r := r) hK hi
  have hfourJ : 4 * caichWSmoothingParameterNat r
      (alignedRootExpTestPoint m i) ≤ alignedThinEndpoint K ell j :=
    (hfourEll i hi).trans (alignedThinEndpoint_mono K ell (Nat.zero_le j))
  have hpoly := caichAlignedNear_smoothing_polylog
    (r := r) hK hell hnear'.1 hnear'.2
  have hprime : ∀ {x' X' a b : ℕ} {z : ℝ},
      0 < z → 2 ≤ X' →
      caichAlignedPNTBaseline K ell j ≤
        caichLambdaLowerCutoff x' X' z →
      (X' : ℝ) ≤
        Real.log (caichAlignedPNTBaseline K ell j : ℝ) ^ A →
      2 * X' ≤ caichLambdaLowerCutoff x' X' z →
      caichShortWindowReciprocalMass (X' : ℝ) x' a b z ≤
        3 / ((X' : ℝ) *
          Real.log (caichAlignedPNTBaseline K ell j : ℝ)) := by
    exact hprimeY _ (hbaselineEll j)
  simpa only [hscaleEq, A] using!
    (caichAlignedCappedShortWindow_le_of_PNTBaseline
      (K := K) (L := ell) (j := j)
      (x := alignedRootExpTestPoint m i)
      (X := caichWSmoothingParameterNat r (alignedRootExpTestPoint m i))
      (A := A) hK (by omega) (by
        exact Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi))
      hnear'.1 hX hfourJ hpoly hprime)

/-! ## Honest cardinality of the literal near family -/

/-- A single rounded aligned step gains at least `5/(6 ell)` in the
logarithm of its binary exponent.  The scaled form avoids divisions in the
subsequent telescoping argument. -/
theorem five_le_six_mul_scale_mul_alignedExponent_log_step
    {K ell j : ℕ} (hell : 3 ≤ ell) :
    (5 : ℝ) ≤ 6 * (ell : ℝ) *
      (Real.log (alignedThinExponent K ell (j + 1) : ℝ) -
        Real.log (alignedThinExponent K ell j : ℝ)) := by
  let E := alignedThinExponent K ell j
  have hE : 0 < E := alignedThinExponent_pos K ell j
  have hellPos : (0 : ℝ) < ell := by positivity
  have hceilNat : E ≤ ell * (E ⌈/⌉ ell) := by
    simpa only [nsmul_eq_mul] using!
      (le_smul_ceilDiv (a := ell) (b := E) (by omega))
  have hceil : (E : ℝ) / (ell : ℝ) ≤ (E ⌈/⌉ ell : ℕ) := by
    apply (div_le_iff₀ hellPos).2
    have hcast : (E : ℝ) ≤ ell * (E ⌈/⌉ ell : ℕ) := by
      exact_mod_cast hceilNat
    simpa only [mul_comm] using! hcast
  have hratio : 1 + 1 / (ell : ℝ) ≤
      (ceilThinStep ell E : ℝ) / (E : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < E)).2
    unfold ceilThinStep
    rw [Nat.cast_add]
    have hscaled : (E : ℝ) / (ell : ℝ) * (E : ℝ) ≤
        (E ⌈/⌉ ell : ℕ) * (E : ℝ) :=
      mul_le_mul_of_nonneg_right hceil (by positivity)
    have hEne : (E : ℝ) ≠ 0 := by positivity
    field_simp at hscaled ⊢
    nlinarith
  have hlogRatio : Real.log (1 + 1 / (ell : ℝ)) ≤
      Real.log ((ceilThinStep ell E : ℝ) / (E : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact hratio
  have hlogLower : 5 / (6 * (ell : ℝ)) ≤
      Real.log (1 + 1 / (ell : ℝ)) := by
    have hbasic := Real.le_log_one_add_of_nonneg
      (show (0 : ℝ) ≤ 1 / (ell : ℝ) by positivity)
    have hnumeric : 5 / (6 * (ell : ℝ)) ≤
        2 / (1 + 2 * (ell : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * ell)
        (by positivity : (0 : ℝ) < 1 + 2 * ell)).2
      have hellR : (3 : ℝ) ≤ ell := by exact_mod_cast hell
      nlinarith
    apply hnumeric.trans
    convert! hbasic using 1 <;> field_simp <;> ring
  have hrewrite : Real.log ((ceilThinStep ell E : ℝ) / (E : ℝ)) =
      Real.log (alignedThinExponent K ell (j + 1) : ℝ) -
        Real.log (alignedThinExponent K ell j : ℝ) := by
    have hstepNe : (ceilThinStep ell E : ℝ) ≠ 0 := by
      exact_mod_cast (show ceilThinStep ell E ≠ 0 by
        unfold ceilThinStep
        omega)
    have hENe : (E : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
    rw [Real.log_div hstepNe hENe]
    rfl
  rw [hrewrite] at hlogRatio
  have htotal := hlogLower.trans hlogRatio
  have hscalePos : (0 : ℝ) < 6 * ell := by positivity
  have := mul_le_mul_of_nonneg_left htotal hscalePos.le
  convert! this using 1 <;> field_simp <;> ring

/-- Telescoping the preceding lower bound between any two aligned block
indices. -/
theorem five_mul_indexDiff_le_alignedExponent_logDiff
    {K ell i j : ℕ} (hell : 3 ≤ ell) (hij : i ≤ j) :
    (5 : ℝ) * (j - i : ℕ) ≤
      6 * (ell : ℝ) *
        (Real.log (alignedThinExponent K ell j : ℝ) -
          Real.log (alignedThinExponent K ell i : ℝ)) := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | @succ j hij ih =>
      have hstep := five_le_six_mul_scale_mul_alignedExponent_log_step
        (K := K) (ell := ell) (j := j) hell
      have hsub : ((j + 1 - i : ℕ) : ℝ) = (j - i : ℕ) + 1 := by
        norm_cast
        omega
      rw [hsub]
      nlinarith

/-- The literal active/near indices have the honest `O_K(ell log ell)`
cardinality.  Multiplying by the PNT coefficient `9` still fits under the
explicit scaling constant `1200 K`. -/
theorem card_alignedNear_mul_nine_le
    {K ell x N : ℕ} (hK : 1 ≤ K) (hell : 5 ≤ ell) :
    (((Finset.range N).filter fun j ↦
        alignedThinEndpoint K ell j < x ∧
          Real.log (x : ℝ) ≤
            (ell : ℝ) ^ (100 * K) *
              Real.log (alignedThinEndpoint K ell j : ℝ)).card : ℝ) * 9 ≤
      ((1200 * K : ℕ) : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) := by
  classical
  let s : Finset ℕ := (Finset.range N).filter fun j ↦
    alignedThinEndpoint K ell j < x ∧
      Real.log (x : ℝ) ≤
        (ell : ℝ) ^ (100 * K) *
          Real.log (alignedThinEndpoint K ell j : ℝ)
  change (s.card : ℝ) * 9 ≤
    ((1200 * K : ℕ) : ℝ) * (ell : ℝ) * Real.log (ell : ℝ)
  have hlogEll : 1 ≤ Real.log (ell : ℝ) := by
    have hexp : Real.exp 1 < (ell : ℝ) :=
      Real.exp_one_lt_three.trans_le (by
        exact_mod_cast (show 3 ≤ ell by omega))
    exact (Real.le_log_iff_exp_le (by positivity : (0 : ℝ) < ell)).2 hexp.le
  have hrightNonneg : 0 ≤
      ((1200 * K : ℕ) : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) := by
    positivity
  by_cases hs : s.Nonempty
  · let a := s.min' hs
    let b := s.max' hs
    have haMem : a ∈ s := by exact Finset.min'_mem s hs
    have hbMem : b ∈ s := by exact Finset.max'_mem s hs
    have hab : a ≤ b := by
      exact Finset.min'_le s b hbMem
    have hnearA : alignedThinEndpoint K ell a < x ∧
        Real.log (x : ℝ) ≤
          (ell : ℝ) ^ (100 * K) *
            Real.log (alignedThinEndpoint K ell a : ℝ) := by
      exact (Finset.mem_filter.mp haMem).2
    have hnearB : alignedThinEndpoint K ell b < x ∧
        Real.log (x : ℝ) ≤
          (ell : ℝ) ^ (100 * K) *
            Real.log (alignedThinEndpoint K ell b : ℝ) := by
      exact (Finset.mem_filter.mp hbMem).2
    have hlogBX : Real.log (alignedThinEndpoint K ell b : ℝ) <
        Real.log (x : ℝ) := by
      apply Real.strictMonoOn_log
      · show (0 : ℝ) < alignedThinEndpoint K ell b
        exact_mod_cast (show 0 < alignedThinEndpoint K ell b by
          have := two_le_alignedThinEndpoint K ell b
          omega)
      · show (0 : ℝ) < x
        exact_mod_cast (show 0 < x by
          have := (two_le_alignedThinEndpoint K ell b).trans_lt hnearB.1
          omega)
      · exact_mod_cast hnearB.1
    have hEratio : (alignedThinExponent K ell b : ℝ) <
        (ell : ℝ) ^ (100 * K) *
          (alignedThinExponent K ell a : ℝ) := by
      have hraw := hlogBX.trans_le hnearA.2
      rw [log_alignedThinEndpoint, log_alignedThinEndpoint] at hraw
      have hlogTwo : 0 < Real.log (2 : ℝ) :=
        Real.log_pos (by norm_num)
      have hmul : (alignedThinExponent K ell b : ℝ) * Real.log 2 <
          ((ell : ℝ) ^ (100 * K) *
            (alignedThinExponent K ell a : ℝ)) * Real.log 2 := by
        simpa only [mul_assoc] using! hraw
      exact lt_of_mul_lt_mul_right hmul hlogTwo.le
    have hlogEratio :
        Real.log (alignedThinExponent K ell b : ℝ) <
          Real.log ((ell : ℝ) ^ (100 * K) *
            (alignedThinExponent K ell a : ℝ)) := by
      apply Real.strictMonoOn_log
      · show (0 : ℝ) < alignedThinExponent K ell b
        exact_mod_cast alignedThinExponent_pos K ell b
      · show (0 : ℝ) < (ell : ℝ) ^ (100 * K) *
            (alignedThinExponent K ell a : ℝ)
        exact mul_pos (pow_pos (by positivity) _)
          (by exact_mod_cast alignedThinExponent_pos K ell a)
      · exact hEratio
    have hgapUpper :
        Real.log (alignedThinExponent K ell b : ℝ) -
            Real.log (alignedThinExponent K ell a : ℝ) <
          ((100 * K : ℕ) : ℝ) * Real.log (ell : ℝ) := by
      have hpowNe : (ell : ℝ) ^ (100 * K) ≠ 0 := by positivity
      have hENe : (alignedThinExponent K ell a : ℝ) ≠ 0 := by
        exact_mod_cast (alignedThinExponent_pos K ell a).ne'
      rw [Real.log_mul hpowNe hENe, Real.log_pow] at hlogEratio
      linarith
    have hcum := five_mul_indexDiff_le_alignedExponent_logDiff
      (K := K) (ell := ell) (i := a) (j := b) (by omega) hab
    have hscalePos : (0 : ℝ) < 6 * (ell : ℝ) := by positivity
    have hgapScaled := mul_lt_mul_of_pos_left hgapUpper hscalePos
    have hdistance : ((b - a : ℕ) : ℝ) <
        120 * (K : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) := by
      have hcombined := hcum.trans_lt hgapScaled
      norm_num [Nat.cast_mul] at hcombined ⊢
      nlinarith
    have hsubset : s ⊆ Finset.Icc a b := by
      intro q hq
      exact Finset.mem_Icc.mpr
        ⟨Finset.min'_le s q hq, Finset.le_max' s q hq⟩
    have hcardNat : s.card ≤ b - a + 1 := by
      have hcard := Finset.card_le_card hsubset
      rw [Nat.card_Icc] at hcard
      omega
    have hcardReal : (s.card : ℝ) ≤
        ((b - a : ℕ) : ℝ) + 1 := by exact_mod_cast hcardNat
    have hKReal : (1 : ℝ) ≤ K := by exact_mod_cast hK
    have hellReal : (5 : ℝ) ≤ ell := by exact_mod_cast hell
    have hcardBound : (s.card : ℝ) <
        120 * (K : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) + 1 :=
      hcardReal.trans_lt (by simpa only [add_comm] using!
        (add_lt_add_right hdistance 1))
    have hKE : (1 : ℝ) ≤ (K : ℝ) * (ell : ℝ) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hKReal)
        (sub_nonneg.mpr hellReal)]
    have hT : (1 : ℝ) ≤
        (K : ℝ) * (ell : ℝ) * Real.log (ell : ℝ) := by
      simpa only [one_mul] using!
        (mul_le_mul hKE hlogEll (by positivity) (by positivity))
    norm_num [Nat.cast_mul] at hcardBound ⊢
    nlinarith
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    exact hrightNonneg

/-- Clamped-schedule form of the honest near coefficient. -/
theorem card_caichAlignedCappedNear_mul_nine_le
    {K S ell x : ℕ} [DecidablePred (caichAlignedCappedNear K S ell x)]
    (hK : 1 ≤ K) (hell : 5 ≤ ell) (hSell : S ≤ ell) :
    (((Finset.range (clampedAlignedThinBlockCount K S ell)).filter
        (caichAlignedCappedNear K S ell x)).card : ℝ) * 9 ≤
      ((1200 * K : ℕ) : ℝ) * caichAuxiliaryLogFactor ell := by
  have hscaleEq : clampedAlignedScale S ell = ell :=
    clampedAlignedScale_eq_of_ge hSell
  have hbase := card_alignedNear_mul_nine_le
    (K := K) (ell := ell) (x := x)
    (N := clampedAlignedThinBlockCount K S ell) hK hell
  have hfilter :
      (Finset.range (clampedAlignedThinBlockCount K S ell)).filter
          (caichAlignedCappedNear K S ell x) =
        (Finset.range (clampedAlignedThinBlockCount K S ell)).filter
          (fun j ↦ alignedThinEndpoint K ell j < x ∧
            Real.log (x : ℝ) ≤ (ell : ℝ) ^ (100 * K) *
              Real.log (alignedThinEndpoint K ell j : ℝ)) := by
    apply Finset.filter_congr
    intro j hj
    simp only [caichAlignedCappedNear, hscaleEq]
  rw [hfilter]
  unfold caichAuxiliaryLogFactor
  simpa only [mul_assoc] using! hbase

end Problem520
end Erdos
