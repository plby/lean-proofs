/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
import ErdosProblems.Erdos1165.AnnularOffspringKernelRadialExit
import ErdosProblems.Erdos1165.AnnularOffspringScan

/-!
# Integrated offspring rows at regular HLOZ radii

This module discharges the geometric hypotheses of the endpoint-integrated
annular row theorem at three consecutive regular radii.  In contrast to a
fixed-endpoint Poisson comparison, the resulting row estimate is uniform in
the entrance point and has an error that tends to zero with the scale.
-/

open Filter Set
open scoped BigOperators ENNReal Topology

namespace Erdos1165.ProfileAnnularRowRegular

open AnnularOffspringKernelRadial AnnularOffspringKernelRadialExit
open AnnularOffspringKernel
open AnnularOffspringScan AnnularProfileClocks LiteralRealAnnulusRadialExit
open AppendixFirstMoment
open PotentialEuclideanGeometry RealDiscFinite
open ThickPoint

noncomputable section

/-- Every nonnegative real-radius lattice disc has a nonempty literal vertex
boundary.  The positive-axis point at the integer floor is the witness. -/
theorem discBoundary_nonempty_of_nonneg {R : ℝ} (hR : 0 ≤ R) :
    (discBoundary 0 R).Nonempty := by
  let m : ℕ := ⌊R⌋₊
  let z : Point := ((m : ℤ), 0)
  let w : Point := (((m + 1 : ℕ) : ℤ), 0)
  have hmle : (m : ℝ) ≤ R := by
    dsimp only [m]
    exact Nat.floor_le hR
  have hRlt : R < (m : ℝ) + 1 := by
    dsimp only [m]
    exact Nat.lt_floor_add_one R
  refine ⟨z, ?_⟩
  refine ⟨?_, w, ?_, ?_⟩
  · rw [disc]
    change latticeDistance 0 z ≤ R
    unfold latticeDistance squaredDistance z m
    simp
    exact hmle
  · rw [disc]
    change ¬latticeDistance 0 w ≤ R
    unfold latticeDistance squaredDistance w m
    simp [Real.sqrt_sq_eq_abs]
    have habs : |-1 + -(m : ℝ)| = (m : ℝ) + 1 := by
      rw [abs_of_nonpos (by
        have hm0 : (0 : ℝ) ≤ m := by positivity
        linarith)]
      ring
    rw [habs]
    exact hRlt
  · unfold Adjacent z w
    simp

/-- Translation of the canonical boundary witness to an arbitrary center. -/
theorem discBoundary_center_nonempty_of_nonneg
    (center : Point) {R : ℝ} (hR : 0 ≤ R) :
    (discBoundary center R).Nonempty := by
  obtain ⟨z, hz⟩ := discBoundary_nonempty_of_nonneg hR
  refine ⟨center + z, ?_⟩
  exact (BoundaryStoppedHarnack.mem_discBoundary_translate
    center R (center + z)).2 (by simpa using hz)

theorem two_lt_regularRadius_of_le
    {n k : ℕ} (hn : 2 ≤ n) (hk : k ≤ n) :
    2 < regularRadius n k := by
  unfold regularRadius
  have hdiff : (0 : ℝ) ≤ (n : ℝ) - (k : ℝ) := by
    have hkReal : (k : ℝ) ≤ n := by exact_mod_cast hk
    linarith
  have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - (k : ℝ)) :=
    Real.one_le_exp hdiff
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ 9 ≤ (n : ℝ) ^ 9 :=
    pow_le_pow_left₀ (by norm_num) hnReal 9
  have hmul := mul_le_mul hexp hpow (by positivity) (by positivity)
  norm_num at hmul
  linarith

/-- At three consecutive nonterminal regular levels all literal annulus
geometry and the logarithmic midpoint identity are automatic. -/
theorem profile_regular_geometry
    {n k : ℕ} (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n) :
    2 < scaleRadius n (k + 1) ∧
    2 < scaleRadius n k ∧
    2 < scaleRadius n (k - 1) ∧
    scaleRadius n (k + 1) + 1 ≤ scaleRadius n k ∧
    scaleRadius n k + 1 ≤ scaleRadius n (k - 1) ∧
    0 < realBoundaryPotentialValue (scaleRadius n (k - 1)) -
      realBoundaryPotentialValue (scaleRadius n (k + 1)) ∧
    2 * realBoundaryPotentialValue (scaleRadius n k) =
      realBoundaryPotentialValue (scaleRadius n (k + 1)) +
        realBoundaryPotentialValue (scaleRadius n (k - 1)) := by
  have hinner : 2 < scaleRadius n (k + 1) := by
    rw [scaleRadius_of_le hk]
    exact two_lt_regularRadius_of_le hn hk
  have hmiddle : 2 < scaleRadius n k := by
    rw [scaleRadius_of_le (by omega : k ≤ n)]
    exact two_lt_regularRadius_of_le hn (by omega)
  have houter : 2 < scaleRadius n (k - 1) := by
    rw [scaleRadius_of_le (by omega : k - 1 ≤ n)]
    exact two_lt_regularRadius_of_le hn (by omega)
  have hinnerSep : scaleRadius n (k + 1) + 1 ≤ scaleRadius n k :=
    scaleRadius_succ_add_one_le (by omega) hk
  have houterSep : scaleRadius n k + 1 ≤ scaleRadius n (k - 1) :=
    by
      have h := scaleRadius_succ_add_one_le (n := n) (k := k - 1)
        (by omega : 1 ≤ n) (by omega : k - 1 + 1 ≤ n)
      have hkpred : k - 1 + 1 = k := by omega
      simpa only [hkpred] using h
  have hdelta : 0 < realBoundaryPotentialValue (scaleRadius n (k - 1)) -
      realBoundaryPotentialValue (scaleRadius n (k + 1)) := by
    have hlt : scaleRadius n (k + 1) < scaleRadius n (k - 1) := by
      linarith
    have hlog := Real.log_lt_log (by linarith) hlt
    unfold realBoundaryPotentialValue
    have hcoef : 0 < (2 / Real.pi : ℝ) := by positivity
    nlinarith
  have hmidpoint :
      2 * realBoundaryPotentialValue (scaleRadius n k) =
        realBoundaryPotentialValue (scaleRadius n (k + 1)) +
          realBoundaryPotentialValue (scaleRadius n (k - 1)) := by
    rw [scaleRadius_of_le (by omega : k ≤ n),
      scaleRadius_of_le hk,
      scaleRadius_of_le (by omega : k - 1 ≤ n)]
    have h := realBoundaryPotentialValue_regularRadius_midpoint n (k - 1)
      (by omega)
    have hk1 : k - 1 + 1 = k := by omega
    have hk2 : k - 1 + 2 = k + 1 := by omega
    rw [hk1, hk2] at h
    linarith
  exact ⟨hinner, hmiddle, houter, hinnerSep, houterSep,
    hdelta, hmidpoint⟩

/-- Scale-ready endpoint-integrated `1/2` row comparison for every regular
profile level.  The finite box is chosen canonically by taking the ceiling
of the outer radius. -/
theorem sum_profileAnnularCycleKernelReal_half_bounds_regular
    {n k : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n)
    (u : ProfileCycleMiddlePoint n k center) :
    let rowError := literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
    (1 - rowError) / 2 ≤
      ∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v ∧
    (∑ v : ProfileCycleMiddlePoint n k center,
        profileAnnularCycleKernelReal n k center u v) ≤
      (1 + rowError) / 2 := by
  obtain ⟨hinner, hmiddle, houter, hinnerSep, houterSep,
      hdelta, hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  let boxRadius : ℕ := ⌈scaleRadius n (k - 1)⌉₊
  have hbox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ) := by
    exact Nat.le_ceil _
  have hmiddleNonempty : (profileInnerBoundary n k center).Nonempty := by
    have hzero := discBoundary_nonempty_of_nonneg (show 0 ≤ scaleRadius n k by
      linarith)
    obtain ⟨z, hz⟩ := hzero
    refine ⟨center + z, ?_⟩
    unfold profileInnerBoundary
    exact (BoundaryStoppedHarnack.mem_discBoundary_translate
      center (scaleRadius n k) (center + z)).2 (by simpa using hz)
  exact sum_profileAnnularCycleKernelReal_half_bounds_of_radial_midpoint
    (boxRadius := boxRadius) hinner hmiddle houter hbox hinnerSep houterSep
    hmiddleNonempty hdelta hmidpoint u

/-- Explicit uniform constant for the regular-level row error. -/
def regularProfileRowErrorConstant : ℝ :=
  8 * (PotentialRadialGlobal.globalRadialConstant + 2)

theorem regularProfileRowErrorConstant_pos :
    0 < regularProfileRowErrorConstant := by
  unfold regularProfileRowErrorConstant
  linarith [PotentialRadialGlobal.globalRadialConstant_pos]

private theorem pow_nine_le_scaleRadius_of_le
    {n j : ℕ} (hn : 1 ≤ n) (hj : j ≤ n) :
    (n : ℝ) ^ 9 ≤ scaleRadius n j := by
  rw [scaleRadius_of_le hj]
  unfold regularRadius
  have hdiff : (0 : ℝ) ≤ (n : ℝ) - (j : ℝ) := by
    have hjReal : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith
  have hexp : (1 : ℝ) ≤ Real.exp ((n : ℝ) - (j : ℝ)) :=
    Real.one_le_exp hdiff
  have hpow0 : 0 ≤ (n : ℝ) ^ 9 := by positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hexp) hpow0]

private theorem boundaryPotentialError_le_two_mul_div_pow_nine
    {n j : ℕ} (hn : 2 ≤ n) (hj : j ≤ n) :
    realBoundaryPotentialError (scaleRadius n j) ≤
      2 * (PotentialRadialGlobal.globalRadialConstant + 2) / (n : ℝ) ^ 9 := by
  let N : ℝ := (n : ℝ) ^ 9
  let K : ℝ := PotentialRadialGlobal.globalRadialConstant + 2
  have hN : 2 ≤ N := by
    dsimp [N]
    have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hnReal 9
    norm_num at hp ⊢
    linarith
  have hNr : N ≤ scaleRadius n j := by
    dsimp [N]
    exact pow_nine_le_scaleRadius_of_le (by omega) hj
  have hr : 1 < scaleRadius n j := by linarith
  have hden : N / 2 ≤ scaleRadius n j - 1 := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    linarith [PotentialRadialGlobal.globalRadialConstant_pos]
  have hNpos : 0 < N := by linarith
  unfold realBoundaryPotentialError
  calc
    (PotentialRadialGlobal.globalRadialConstant + 2) /
          (scaleRadius n j - 1) ≤ K / (N / 2) := by
      apply div_le_div_of_nonneg_left hK (by linarith) hden
    _ = 2 * (PotentialRadialGlobal.globalRadialConstant + 2) /
          (n : ℝ) ^ 9 := by
      dsimp [K, N]
      field_simp

/-- The relative error in every regular integrated offspring row is
uniformly `O(n⁻⁹)`, hence much smaller than the `O(n⁻⁶)` A.6 budget. -/
theorem profileRegularRowError_le_rate
    {n k : ℕ} (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n) :
    literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)) ≤
      regularProfileRowErrorConstant / (n : ℝ) ^ 9 := by
  obtain ⟨hinner, _hmiddle, _houter, hinnerSep, houterSep,
      _hdelta, _hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  have hrow := literalRealAnnulusRowError_le_pi_mul_innerError
    (by linarith : 1 < scaleRadius n (k + 1))
    (by linarith : scaleRadius n (k + 1) ≤ scaleRadius n k)
    (by linarith : scaleRadius n k ≤ scaleRadius n (k - 1))
    (realBoundaryPotentialValue_scaleRadius_outer_sub_inner
      (by omega) (by omega) hk)
  have hinnerError := boundaryPotentialError_le_two_mul_div_pow_nine hn hk
  have hinnerError0 := realBoundaryPotentialError_nonneg
    (by linarith : 1 < scaleRadius n (k + 1))
  calc
    literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)) ≤
      Real.pi * realBoundaryPotentialError (scaleRadius n (k + 1)) := hrow
    _ ≤ 4 * realBoundaryPotentialError (scaleRadius n (k + 1)) :=
      mul_le_mul_of_nonneg_right Real.pi_le_four hinnerError0
    _ ≤ 4 * (2 * (PotentialRadialGlobal.globalRadialConstant + 2) /
        (n : ℝ) ^ 9) := mul_le_mul_of_nonneg_left hinnerError (by norm_num)
    _ = regularProfileRowErrorConstant / (n : ℝ) ^ 9 := by
      unfold regularProfileRowErrorConstant
      ring

/-- Fully automatic `HalfRowComparison` at every nonterminal regular level. -/
theorem profileAnnularCycleKernelReal_halfRowComparison_regular
    {n k : ℕ} {center : Point}
    (hn : 2 ≤ n) (hk0 : 0 < k) (hk : k + 1 ≤ n) :
    HalfRowComparison
      (literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)))
      (profileAnnularCycleKernelReal n k center) := by
  intro u
  exact sum_profileAnnularCycleKernelReal_half_bounds_regular hn hk0 hk u

/-- Eventually the explicit regular-row error is at most `n⁻⁶`, uniformly
over every nonterminal profile level. -/
theorem eventually_profileRegularRowError_le_inv_pow_six :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      literalRealAnnulusRowError
          (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)) ≤
        1 / (n : ℝ) ^ 6 := by
  have hlarge := tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop regularProfileRowErrorConstant)
  filter_upwards [hlarge, eventually_ge_atTop 2] with n hnLarge hn k hk0 hk
  have hrate := profileRegularRowError_le_rate hn hk0 hk
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hcube : regularProfileRowErrorConstant ≤ (n : ℝ) ^ 3 := by
    have hnCube : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1), sq_nonneg (n : ℝ)]
    exact hnLarge.trans hnCube
  calc
    literalRealAnnulusRowError
        (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1)) ≤
      regularProfileRowErrorConstant / (n : ℝ) ^ 9 := hrate
    _ ≤ 1 / (n : ℝ) ^ 6 := by
      rw [div_le_div_iff₀ (pow_pos hnPos 9) (pow_pos hnPos 6)]
      have hsplit : (n : ℝ) ^ 9 = (n : ℝ) ^ 3 * (n : ℝ) ^ 6 := by ring
      rw [hsplit]
      nlinarith [pow_pos hnPos 6]

/-- Eventual one-parent offspring comparison at every internal regular
profile level.  All real-radius geometry, both boundary nonemptiness
conditions, the finite containing box, and the numerical side condition
`rowError ≤ 1` are discharged here. -/
theorem eventually_integratedMarkedOffspringKernel_profile_two_sided_regular :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k + 1 ≤ n →
      ∀ (q : ℕ) (center : Point) (u : ProfileCycleMiddlePoint n k center),
        let rowError := literalRealAnnulusRowError
          (scaleRadius n (k + 1)) (scaleRadius n k) (scaleRadius n (k - 1))
        (1 - rowError) ^ (q + 1) * halfGeometricMass q ≤
          integratedMarkedOffspringKernel
            (profileAnnularCycleKernelReal n k center)
            (profileAnnularEscapeRowReal n k center) q u ∧
        integratedMarkedOffspringKernel
            (profileAnnularCycleKernelReal n k center)
            (profileAnnularEscapeRowReal n k center) q u ≤
          (1 + rowError) ^ (q + 1) * halfGeometricMass q := by
  filter_upwards [eventually_profileRegularRowError_le_inv_pow_six,
      eventually_ge_atTop 2] with n herror hn
  intro k hk0 hk q center u
  obtain ⟨hinner, hmiddle, houter, hinnerSep, houterSep,
      _hdelta, _hmidpoint⟩ := profile_regular_geometry hn hk0 hk
  let boxRadius : ℕ := ⌈scaleRadius n (k - 1)⌉₊
  have hbox : scaleRadius n (k - 1) ≤ (boxRadius : ℝ) := Nat.le_ceil _
  have hmiddleNonempty : (profileInnerBoundary n k center).Nonempty := by
    unfold profileInnerBoundary
    exact discBoundary_center_nonempty_of_nonneg center (by linarith)
  have houterNonempty : (profileOuterBoundary n k center).Nonempty := by
    unfold profileOuterBoundary
    exact discBoundary_center_nonempty_of_nonneg center (by linarith)
  have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hinv : 1 / (n : ℝ) ^ 6 ≤ 1 := by
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 6 := one_le_pow₀ hnReal
    exact (div_le_one (by positivity)).2 hpow
  have herror1 : literalRealAnnulusRowError
      (scaleRadius n (k + 1)) (scaleRadius n k)
        (scaleRadius n (k - 1)) ≤ 1 :=
    (herror k hk0 hk).trans hinv
  exact integratedMarkedOffspringKernel_profile_two_sided_regularLevel
    (boxRadius := boxRadius) (by omega) (by omega) hk
    hinner hmiddle houter hbox hinnerSep houterSep
    hmiddleNonempty houterNonempty herror1 u

end

end Erdos1165.ProfileAnnularRowRegular
