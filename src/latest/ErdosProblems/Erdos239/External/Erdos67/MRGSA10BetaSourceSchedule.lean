import ErdosProblems.Erdos239.External.Erdos67.MRGSA10PrimeGaussianNearRow
import ErdosProblems.Erdos239.External.Erdos67.MRTDensity
import ErdosProblems.Erdos239.External.Erdos67.EulerSubpower

/-!
# A fixed-depth beta-sieve schedule for GS A.10

For a beta-sieve constant `Cβ`, this module chooses a fixed admissible depth
and the source cutoff

`Q(y) = ceil (exp (log y / (16 S)))`.

The depth depends only on `Cβ`; all subsequent thresholds are therefore
eventual only in `y`.  The factor `16` leaves the finite-level remainder at
the fixed power scale `y^(1/8)` after squaring `Q^S`.
-/

open Filter
open scoped Topology

namespace Erdos67.MRHalaszBands

noncomputable section

/-- A fixed beta depth large enough for both the source lower cutoff and
the logarithmic beta-sieve constraint. -/
def gsA10BetaSourceDepth (Cβ : ℝ) : ℕ :=
  101 + Nat.ceil (50 * max 0 (Real.log Cβ))

/-- The logarithmic exponent used by the source cutoff. -/
def gsA10BetaSourceExponent (Cβ : ℝ) (y : ℕ) : ℝ :=
  Real.log (y : ℝ) / (16 * gsA10BetaSourceDepth Cβ : ℕ)

/-- Natural beta-sieve cutoff at the fixed source depth. -/
def gsA10BetaSourceCutoff (Cβ : ℝ) (y : ℕ) : ℕ :=
  Nat.ceil (Real.exp (gsA10BetaSourceExponent Cβ y))

theorem gsA10BetaSourceDepth_ge (Cβ : ℝ) :
    101 ≤ gsA10BetaSourceDepth Cβ := by
  unfold gsA10BetaSourceDepth
  omega

theorem gsA10BetaSourceDepth_pos (Cβ : ℝ) :
    0 < gsA10BetaSourceDepth Cβ :=
  lt_of_lt_of_le (by norm_num) (gsA10BetaSourceDepth_ge Cβ)

/-- The chosen depth satisfies the exact beta-sieve hypothesis, without an
eventual qualifier. -/
theorem log_le_two_mul_gsA10BetaSourceDepth_sub_div
    (Cβ : ℝ) :
    Real.log Cβ ≤
      2 * (gsA10BetaSourceDepth Cβ - 100 : ℕ) / 99 := by
  let L : ℝ := max 0 (Real.log Cβ)
  let N : ℕ := Nat.ceil (50 * L)
  have hL0 : 0 ≤ L := by simp [L]
  have hlogL : Real.log Cβ ≤ L := le_max_right _ _
  have hceil : 50 * L ≤ (N : ℝ) := by
    exact Nat.le_ceil _
  have hdepth : gsA10BetaSourceDepth Cβ - 100 = N + 1 := by
    simp only [gsA10BetaSourceDepth, N, L]
    omega
  rw [hdepth]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  calc
    Real.log Cβ ≤ L := hlogL
    _ ≤ 2 * ((N : ℝ) + 1) / 99 := by linarith

theorem exp_gsA10BetaSourceExponent_le_cutoff
    (Cβ : ℝ) (y : ℕ) :
    Real.exp (gsA10BetaSourceExponent Cβ y) ≤
      (gsA10BetaSourceCutoff Cβ y : ℝ) := by
  exact Nat.le_ceil _

/-- The cutoff is below `y` as soon as `y≥2`; no asymptotic argument is
needed for this half of the structural schedule. -/
theorem gsA10BetaSourceCutoff_le
    (Cβ : ℝ) {y : ℕ} (hy : 2 ≤ y) :
    gsA10BetaSourceCutoff Cβ y ≤ y := by
  have hlog0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))
  have hden : (1 : ℝ) ≤
      (16 * gsA10BetaSourceDepth Cβ : ℕ) := by
    exact_mod_cast (show 1 ≤ 16 * gsA10BetaSourceDepth Cβ by
      have := gsA10BetaSourceDepth_pos Cβ
      omega)
  have hexpLe : gsA10BetaSourceExponent Cβ y ≤ Real.log (y : ℝ) := by
    unfold gsA10BetaSourceExponent
    exact div_le_self hlog0 hden
  have hpowLe : Real.exp (gsA10BetaSourceExponent Cβ y) ≤ (y : ℝ) := by
    calc
      Real.exp (gsA10BetaSourceExponent Cβ y) ≤
          Real.exp (Real.log (y : ℝ)) := Real.exp_le_exp.mpr hexpLe
      _ = (y : ℝ) := Real.exp_log (by positivity)
  have hceil : (gsA10BetaSourceCutoff Cβ y : ℝ) <
      Real.exp (gsA10BetaSourceExponent Cβ y) + 1 := by
    unfold gsA10BetaSourceCutoff
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hlt : (gsA10BetaSourceCutoff Cβ y : ℝ) < (y : ℝ) + 1 :=
    hceil.trans_le (by simpa only [add_comm] using add_le_add_right hpowLe 1)
  have hltNat : gsA10BetaSourceCutoff Cβ y < y + 1 := by
    exact_mod_cast hlt
  omega

/-- A logarithmic threshold forcing the cutoff to contain at least the
prime `3`. -/
theorem three_le_gsA10BetaSourceCutoff
    (Cβ : ℝ) {y : ℕ}
    (hy : Real.log 2 < gsA10BetaSourceExponent Cβ y) :
    3 ≤ gsA10BetaSourceCutoff Cβ y := by
  have htwo : (2 : ℝ) <
      Real.exp (gsA10BetaSourceExponent Cβ y) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hy
  have hceil := exp_gsA10BetaSourceExponent_le_cutoff Cβ y
  exact_mod_cast (show (2 : ℝ) < (gsA10BetaSourceCutoff Cβ y : ℝ) from
    htwo.trans_le hceil)

/-- The cutoff logarithm retains the intended fraction of `log y`. -/
theorem gsA10BetaSourceExponent_le_log_cutoff
    (Cβ : ℝ) (y : ℕ) :
    gsA10BetaSourceExponent Cβ y ≤
      Real.log (gsA10BetaSourceCutoff Cβ y : ℝ) := by
  calc
    gsA10BetaSourceExponent Cβ y =
        Real.log (Real.exp (gsA10BetaSourceExponent Cβ y)) := by
      rw [Real.log_exp]
    _ ≤ Real.log (gsA10BetaSourceCutoff Cβ y : ℝ) :=
      Real.log_le_log (Real.exp_pos _)
        (exp_gsA10BetaSourceExponent_le_cutoff Cβ y)

/-- Explicit constant in the scheduled density bound. -/
def gsA10BetaSourceDensityConstant (Cβ : ℝ) : ℝ :=
  (1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^
      (gsA10BetaSourceDepth Cβ - 100)) *
    (Real.exp (2 * PrimeEstimates.mertensBound) * Real.log 2) *
      (16 * gsA10BetaSourceDepth Cβ : ℕ)

/-- Mertens scalarization of the scheduled row density. -/
theorem gsA10PrimeRowBetaDensity_source_le
    {Cβ : ℝ} (hCβ : 1 ≤ Cβ) {y : ℕ} (hy : 2 ≤ y)
    (hQ : 3 ≤ gsA10BetaSourceCutoff Cβ y) :
    gsA10PrimeRowBetaDensity Cβ (gsA10BetaSourceCutoff Cβ y)
        (gsA10BetaSourceDepth Cβ) ≤
      gsA10BetaSourceDensityConstant Cβ / Real.log (y : ℝ) := by
  let S := gsA10BetaSourceDepth Cβ
  let Q := gsA10BetaSourceCutoff Cβ y
  let A : ℝ := 1 + (4 * Cβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hSpos : 0 < S := gsA10BetaSourceDepth_pos Cβ
  have hu : 0 < gsA10BetaSourceExponent Cβ y := by
    unfold gsA10BetaSourceExponent
    exact div_pos hlogy (by positivity)
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hlogLower : gsA10BetaSourceExponent Cβ y ≤ Real.log (Q : ℝ) := by
    simpa only [Q] using gsA10BetaSourceExponent_le_log_cutoff Cβ y
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hdensity := primeBlockDensity_le_mertensRatio
    (L := 3) (U := Q) (by norm_num) hQ
  calc
    gsA10PrimeRowBetaDensity Cβ Q S =
        A * primeBlockDensity (3, Q) := rfl
    _ ≤ A * (Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log 2 / Real.log (Q : ℝ))) :=
      mul_le_mul_of_nonneg_left hdensity hA0
    _ ≤ A * (Real.exp (2 * PrimeEstimates.mertensBound) *
          (Real.log 2 / gsA10BetaSourceExponent Cβ y)) := by
      gcongr
    _ = gsA10BetaSourceDensityConstant Cβ / Real.log (y : ℝ) := by
      dsimp only [gsA10BetaSourceDensityConstant,
        gsA10BetaSourceExponent, S, A]
      field_simp

/-- The ceiling loses only a factor `2`, and the chosen `16S` exponent
therefore puts the squared beta remainder on the `y^(1/8)` scale. -/
theorem gsA10PrimeRowBetaRemainder_source_le
    (Cβ : ℝ) {y : ℕ} (hy : 1 ≤ y) :
    gsA10PrimeRowBetaRemainder (gsA10BetaSourceCutoff Cβ y)
        (gsA10BetaSourceDepth Cβ) ≤
      (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ) *
        Real.exp (Real.log (y : ℝ) / 8) := by
  let S := gsA10BetaSourceDepth Cβ
  let u := gsA10BetaSourceExponent Cβ y
  let Q := gsA10BetaSourceCutoff Cβ y
  have hlog0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hy)
  have hSpos : 0 < S := gsA10BetaSourceDepth_pos Cβ
  have hu0 : 0 ≤ u := by
    dsimp only [u, gsA10BetaSourceExponent]
    exact div_nonneg hlog0 (by positivity)
  have hone : (1 : ℝ) ≤ Real.exp u := by
    simpa only [Real.exp_zero] using Real.exp_monotone hu0
  have hceil : (Q : ℝ) < Real.exp u + 1 := by
    dsimp only [Q, gsA10BetaSourceCutoff]
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hQle : (Q : ℝ) ≤ 2 * Real.exp u := by linarith
  have hpow : (Q : ℝ) ^ (2 * S) ≤
      (2 * Real.exp u) ^ (2 * S) := by
    exact pow_le_pow_left₀ (Nat.cast_nonneg Q) hQle _
  have hueq : u * (2 * S : ℕ) = Real.log (y : ℝ) / 8 := by
    dsimp only [u, gsA10BetaSourceExponent, S]
    push_cast
    have hSne : (gsA10BetaSourceDepth Cβ : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  calc
    gsA10PrimeRowBetaRemainder Q S = (Q : ℝ) ^ (2 * S) := by
      unfold gsA10PrimeRowBetaRemainder
      push_cast
      ring
    _ ≤ (2 * Real.exp u) ^ (2 * S) := hpow
    _ = (2 : ℝ) ^ (2 * S) * Real.exp (u * (2 * S : ℕ)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    _ = (2 : ℝ) ^ (2 * S) * Real.exp (Real.log (y : ℝ) / 8) := by
      rw [hueq]
    _ = _ := by rfl

/-- Requested fixed-power form of the scheduled beta remainder. -/
theorem gsA10PrimeRowBetaRemainder_source_le_rpow
    (Cβ : ℝ) {y : ℕ} (hy : 1 ≤ y) :
    gsA10PrimeRowBetaRemainder (gsA10BetaSourceCutoff Cβ y)
        (gsA10BetaSourceDepth Cβ) ≤
      (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ) *
        (y : ℝ) ^ (1 / 8 : ℝ) := by
  have hraw := gsA10PrimeRowBetaRemainder_source_le Cβ hy
  calc
    gsA10PrimeRowBetaRemainder (gsA10BetaSourceCutoff Cβ y)
        (gsA10BetaSourceDepth Cβ) ≤
        (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ) *
          Real.exp (Real.log (y : ℝ) / 8) := hraw
    _ = (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ) *
          (y : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < y)]
      congr 2
      ring

/-- All structural beta-sieve hypotheses, together with the two scalar
row bounds, hold eventually in the source cutoff variable. -/
theorem eventually_gsA10BetaSourceSchedule
    {Cβ : ℝ} (hCβ : 1 ≤ Cβ) :
    ∀ᶠ y : ℕ in atTop,
      3 ≤ gsA10BetaSourceCutoff Cβ y ∧
      gsA10BetaSourceCutoff Cβ y ≤ y ∧
      101 ≤ gsA10BetaSourceDepth Cβ ∧
      Real.log Cβ ≤
        2 * (gsA10BetaSourceDepth Cβ - 100 : ℕ) / 99 ∧
      gsA10PrimeRowBetaDensity Cβ (gsA10BetaSourceCutoff Cβ y)
          (gsA10BetaSourceDepth Cβ) ≤
        gsA10BetaSourceDensityConstant Cβ / Real.log (y : ℝ) ∧
      gsA10PrimeRowBetaRemainder (gsA10BetaSourceCutoff Cβ y)
          (gsA10BetaSourceDepth Cβ) ≤
        (2 : ℝ) ^ (2 * gsA10BetaSourceDepth Cβ : ℕ) *
          (y : ℝ) ^ (1 / 8 : ℝ) := by
  have hlog := Erdos67.EulerSubpower.tendsto_log_nat_atTop.eventually
    (eventually_gt_atTop
      (((16 * gsA10BetaSourceDepth Cβ : ℕ) : ℝ) * Real.log 2))
  filter_upwards [hlog, eventually_ge_atTop 2] with y hylog hy2
  have hden : (0 : ℝ) < (16 * gsA10BetaSourceDepth Cβ : ℕ) := by
    exact_mod_cast (show 0 < 16 * gsA10BetaSourceDepth Cβ by
      have := gsA10BetaSourceDepth_pos Cβ
      omega)
  have hthreshold : Real.log 2 < gsA10BetaSourceExponent Cβ y := by
    unfold gsA10BetaSourceExponent
    rw [lt_div_iff₀ hden]
    simpa only [mul_comm] using hylog
  have hQ := three_le_gsA10BetaSourceCutoff Cβ hthreshold
  exact ⟨hQ, gsA10BetaSourceCutoff_le Cβ hy2,
    gsA10BetaSourceDepth_ge Cβ,
    log_le_two_mul_gsA10BetaSourceDepth_sub_div Cβ,
    gsA10PrimeRowBetaDensity_source_le hCβ hy2 hQ,
    gsA10PrimeRowBetaRemainder_source_le_rpow Cβ (by omega)⟩

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.log_le_two_mul_gsA10BetaSourceDepth_sub_div
#print axioms Erdos67.MRHalaszBands.gsA10PrimeRowBetaDensity_source_le
#print axioms Erdos67.MRHalaszBands.gsA10PrimeRowBetaRemainder_source_le
#print axioms Erdos67.MRHalaszBands.gsA10PrimeRowBetaRemainder_source_le_rpow
#print axioms Erdos67.MRHalaszBands.eventually_gsA10BetaSourceSchedule
