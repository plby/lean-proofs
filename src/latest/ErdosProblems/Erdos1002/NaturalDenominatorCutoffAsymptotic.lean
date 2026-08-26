import ErdosProblems.Erdos1002.NaturalDenominatorCutoffGlue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The manuscript-scale natural cutoff

This file specializes the literal `L²` cutoff to the integer outer scale

`P_N = N * ceil((1 + log N)^10)`

and proves that its error is `o(log N)`.  All statements involving logarithms
are made for `N >= 2`; the final limit is parametrized by `N = m + 2`, so no
totalization at `0` or `1` is hidden.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

/-- The real logarithmic scale used in the manuscript cutoff. -/
def manuscriptLogScale (N : ℕ) : ℝ :=
  1 + Real.log (N : ℝ)

/-- Integer ceiling of the tenth power of the logarithmic scale. -/
def manuscriptCeilScale (N : ℕ) : ℕ :=
  ⌈manuscriptLogScale N ^ 10⌉₊

/-- The explicit integer outer denominator cutoff. -/
def manuscriptOuterCutoff (N : ℕ) : ℕ :=
  N * manuscriptCeilScale N

theorem manuscriptLogScale_one_le (N : ℕ) :
    1 ≤ manuscriptLogScale N := by
  unfold manuscriptLogScale
  linarith [Real.log_natCast_nonneg N]

theorem manuscriptLogScale_pos (N : ℕ) :
    0 < manuscriptLogScale N :=
  lt_of_lt_of_le zero_lt_one (manuscriptLogScale_one_le N)

theorem manuscriptCeilScale_pos (N : ℕ) :
    0 < manuscriptCeilScale N := by
  unfold manuscriptCeilScale
  exact Nat.ceil_pos.mpr (pow_pos (manuscriptLogScale_pos N) 10)

theorem manuscriptLogScale_pow_le_ceil (N : ℕ) :
    manuscriptLogScale N ^ 10 ≤ (manuscriptCeilScale N : ℝ) := by
  exact Nat.le_ceil _

theorem manuscriptCeilScale_cast_le_two_mul_pow (N : ℕ) :
    (manuscriptCeilScale N : ℝ) ≤
      2 * manuscriptLogScale N ^ 10 := by
  have hnonneg : 0 ≤ manuscriptLogScale N ^ 10 := by positivity
  have hceil := (Nat.ceil_lt_add_one hnonneg).le
  have hpowOne : 1 ≤ manuscriptLogScale N ^ 10 := by
    exact one_le_pow₀ (manuscriptLogScale_one_le N)
  unfold manuscriptCeilScale
  linarith

theorem manuscriptOuterCutoff_pos {N : ℕ} (hN : 0 < N) :
    0 < manuscriptOuterCutoff N :=
  Nat.mul_pos hN (manuscriptCeilScale_pos N)

/-- The ceiling contributes at most eleven logarithmic scales to its own
logarithm. -/
theorem log_manuscriptCeilScale_le (N : ℕ) :
    Real.log (manuscriptCeilScale N : ℝ) ≤
      11 * manuscriptLogScale N := by
  let L : ℝ := manuscriptLogScale N
  let C : ℕ := manuscriptCeilScale N
  have hL : 1 ≤ L := manuscriptLogScale_one_le N
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hC : 0 < C := manuscriptCeilScale_pos N
  have hCReal : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCup : (C : ℝ) ≤ 2 * L ^ 10 := by
    simpa only [C, L] using! manuscriptCeilScale_cast_le_two_mul_pow N
  have hlogMono := Real.log_le_log hCReal hCup
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    nlinarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogL : Real.log L ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    linarith
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hLne : L ≠ 0 := hLpos.ne'
  rw [Real.log_mul htwo (pow_ne_zero 10 hLne), Real.log_pow] at hlogMono
  norm_num at hlogMono
  dsimp [C, L] at hlogMono ⊢
  nlinarith

/-- The logarithm of `N * P_N = N^2 ceil((1+log N)^10)` is at most thirteen
logarithmic scales. -/
theorem log_N_mul_manuscriptOuterCutoff_le
    (N : ℕ) (hN : 0 < N) :
    Real.log (((N * manuscriptOuterCutoff N : ℕ) : ℝ)) ≤
      13 * manuscriptLogScale N := by
  let C : ℕ := manuscriptCeilScale N
  have hC : 0 < C := manuscriptCeilScale_pos N
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hCR : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hlogN : Real.log (N : ℝ) ≤ manuscriptLogScale N := by
    unfold manuscriptLogScale
    linarith
  have hlogC : Real.log (C : ℝ) ≤ 11 * manuscriptLogScale N := by
    simpa only [C] using! log_manuscriptCeilScale_le N
  have hcast : (((N * manuscriptOuterCutoff N : ℕ) : ℝ)) =
      (N : ℝ) * ((N : ℝ) * (C : ℝ)) := by
    unfold manuscriptOuterCutoff
    dsimp [C]
    push_cast
    ring
  rw [hcast, Real.log_mul hNR (mul_ne_zero hNR hCR),
    Real.log_mul hNR hCR]
  linarith

theorem harmonic_N_mul_manuscriptOuterCutoff_le
    (N : ℕ) (hN : 0 < N) :
    (harmonic (N * manuscriptOuterCutoff N) : ℝ) ≤
      14 * manuscriptLogScale N := by
  have h := harmonic_le_one_add_log (N * manuscriptOuterCutoff N)
  have hL := manuscriptLogScale_one_le N
  linarith [log_N_mul_manuscriptOuterCutoff_le N hN]

theorem six_add_log_N_mul_manuscriptOuterCutoff_le
    (N : ℕ) (hN : 0 < N) :
    6 + Real.log (((N * manuscriptOuterCutoff N : ℕ) : ℝ)) ≤
      19 * manuscriptLogScale N := by
  have hL := manuscriptLogScale_one_le N
  linarith [log_N_mul_manuscriptOuterCutoff_le N hN]

private theorem outerCutoffExplicitBound_eq (N : ℕ+) :
    let n : ℕ := N
    let C : ℕ := manuscriptCeilScale n
    let P : ℕ := manuscriptOuterCutoff n
    2 *
        (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
            (((n * P : ℕ) : ℝ) *
              (harmonic (n * P) : ℝ) ^ 3) +
          (32 * ((n : ℝ) ^ 2 /
              (((n : ℕ) * P : ℕ) : ℝ)) *
            (6 + Real.log ((((n : ℕ) * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment)) =
      2 *
        ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
            (harmonic (n * P) : ℝ) ^ 3 / (C : ℝ)) +
          32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment / (C : ℝ)) := by
  dsimp only
  have hn : (N : ℝ) ≠ 0 := by positivity
  have hC : (manuscriptCeilScale (N : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (manuscriptCeilScale_pos (N : ℕ)).ne'
  unfold manuscriptOuterCutoff
  push_cast
  field_simp

private theorem outerCutoffExplicitBound_le (N : ℕ+) :
    let n : ℕ := N
    let C : ℕ := manuscriptCeilScale n
    let P : ℕ := manuscriptOuterCutoff n
    2 *
        ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
            (harmonic (n * P) : ℝ) ^ 3 / (C : ℝ)) +
          32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
            dyadicFifthMoment / (C : ℝ)) ≤
      2 *
        (((((Real.pi ^ 2 / 6) * 2) ^ 2 * 14 ^ 3) +
            32 * 19 ^ 5 * dyadicFifthMoment) *
          manuscriptLogScale n ^ 5 / (C : ℝ)) := by
  dsimp only
  let n : ℕ := N
  let L : ℝ := manuscriptLogScale n
  let C : ℕ := manuscriptCeilScale n
  let P : ℕ := manuscriptOuterCutoff n
  have hn : 0 < n := N.pos
  have hP : 0 < P := manuscriptOuterCutoff_pos hn
  have hC : (0 : ℝ) < (C : ℝ) := by
    exact_mod_cast manuscriptCeilScale_pos n
  have hL : 1 ≤ L := manuscriptLogScale_one_le n
  have hharm : (harmonic (n * P) : ℝ) ≤ 14 * L := by
    simpa only [n, L, P] using!
      harmonic_N_mul_manuscriptOuterCutoff_le n hn
  have hlog : 6 + Real.log (((n * P : ℕ) : ℝ)) ≤ 19 * L := by
    simpa only [n, L, P] using!
      six_add_log_N_mul_manuscriptOuterCutoff_le n hn
  have hharm0 : 0 ≤ (harmonic (n * P) : ℝ) := by
    have hq : (0 : ℚ) ≤ harmonic (n * P) :=
      (harmonic_pos (Nat.mul_ne_zero hn.ne' hP.ne')).le
    exact_mod_cast hq
  have hlog0 : 0 ≤ 6 + Real.log (((n * P : ℕ) : ℝ)) := by
    have hcast : (1 : ℝ) ≤ ((n * P : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero hn.ne' hP.ne')
    positivity
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
  have hL3L5 : L ^ 3 ≤ L ^ 5 := by
    calc
      L ^ 3 = L ^ 3 * 1 := by ring
      _ ≤ L ^ 3 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hL2 (pow_nonneg hL0 3)
      _ = L ^ 5 := by ring
  dsimp only [n, C, P, L] at *
  have hharmPow :
      (harmonic ((N : ℕ) * manuscriptOuterCutoff (N : ℕ)) : ℝ) ^ 3 ≤
        14 ^ 3 * manuscriptLogScale (N : ℕ) ^ 5 := by
    calc
      (harmonic ((N : ℕ) * manuscriptOuterCutoff (N : ℕ)) : ℝ) ^ 3 ≤
          (14 * manuscriptLogScale (N : ℕ)) ^ 3 :=
        pow_le_pow_left₀ hharm0 hharm 3
      _ = 14 ^ 3 * manuscriptLogScale (N : ℕ) ^ 3 := by ring
      _ ≤ 14 ^ 3 * manuscriptLogScale (N : ℕ) ^ 5 := by gcongr
  have hlogPow :
      (6 + Real.log
          ((((N : ℕ) * manuscriptOuterCutoff (N : ℕ) : ℕ) : ℝ))) ^ 5 ≤
        19 ^ 5 * manuscriptLogScale (N : ℕ) ^ 5 := by
    calc
      (6 + Real.log
          ((((N : ℕ) * manuscriptOuterCutoff (N : ℕ) : ℕ) : ℝ))) ^ 5 ≤
          (19 * manuscriptLogScale (N : ℕ)) ^ 5 :=
        pow_le_pow_left₀ hlog0 hlog 5
      _ = 19 ^ 5 * manuscriptLogScale (N : ℕ) ^ 5 := by ring
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    ((Real.pi ^ 2 / 6 * 2) ^ 2 *
          (harmonic ((N : ℕ) * manuscriptOuterCutoff (N : ℕ)) : ℝ) ^ 3 /
          (manuscriptCeilScale (N : ℕ) : ℝ) +
        32 * (6 + Real.log
          ((((N : ℕ) * manuscriptOuterCutoff (N : ℕ) : ℕ) : ℝ))) ^ 5 *
          dyadicFifthMoment / (manuscriptCeilScale (N : ℕ) : ℝ)) ≤
        ((Real.pi ^ 2 / 6 * 2) ^ 2 *
            (14 ^ 3 * manuscriptLogScale (N : ℕ) ^ 5) /
            (manuscriptCeilScale (N : ℕ) : ℝ) +
          32 * (19 ^ 5 * manuscriptLogScale (N : ℕ) ^ 5) *
            dyadicFifthMoment / (manuscriptCeilScale (N : ℕ) : ℝ)) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hharmPow
            (sq_nonneg (Real.pi ^ 2 / 6 * 2))) hC.le
      · apply div_le_div_of_nonneg_right _ hC.le
        calc
          32 * (6 + Real.log
              ((((N : ℕ) * manuscriptOuterCutoff (N : ℕ) : ℕ) : ℝ))) ^ 5 *
                dyadicFifthMoment =
              32 * ((6 + Real.log
                ((((N : ℕ) * manuscriptOuterCutoff (N : ℕ) : ℕ) : ℝ))) ^ 5 *
                  dyadicFifthMoment) := by ring
          _ ≤ 32 * ((19 ^ 5 * manuscriptLogScale (N : ℕ) ^ 5) *
                dyadicFifthMoment) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hlogPow dyadicFifthMoment_nonneg)
              (by norm_num)
          _ = 32 * (19 ^ 5 * manuscriptLogScale (N : ℕ) ^ 5) *
                dyadicFifthMoment := by ring
    _ = ((Real.pi ^ 2 / 6 * 2) ^ 2 * 14 ^ 3 +
          32 * 19 ^ 5 * dyadicFifthMoment) *
        manuscriptLogScale (N : ℕ) ^ 5 /
          (manuscriptCeilScale (N : ℕ) : ℝ) := by ring

/-- Fixed numerical factor in the outer-cutoff square bound. -/
def naturalCutoffOuterBoundConstant : ℝ :=
  2 * (((Real.pi ^ 2 / 6 * 2) ^ 2 * 14 ^ 3) +
    32 * 19 ^ 5 * dyadicFifthMoment)

theorem naturalCutoffOuterBoundConstant_nonneg :
    0 ≤ naturalCutoffOuterBoundConstant := by
  unfold naturalCutoffOuterBoundConstant
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (sq_nonneg _) (by positivity))
      (mul_nonneg (by positivity) dyadicFifthMoment_nonneg))

/-- At the manuscript's outer scale, the square of the strict-tail norm is
bounded by a fixed constant times the inverse fifth logarithmic scale. -/
theorem norm_sq_allDenominator_sub_manuscriptOuterCutoff_le
    (N : ℕ+) :
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N
          (manuscriptOuterCutoff (N : ℕ))‖ ^ 2 ≤
      naturalCutoffOuterBoundConstant /
        manuscriptLogScale (N : ℕ) ^ 5 := by
  let n : ℕ := N
  let L : ℝ := manuscriptLogScale n
  let C : ℕ := manuscriptCeilScale n
  let P : ℕ := manuscriptOuterCutoff n
  have hP : 0 < P := manuscriptOuterCutoff_pos N.pos
  have hraw := norm_sq_allDenominator_sub_naturalCutoffReconstructionL2_le
    N P hP
  have heq := outerCutoffExplicitBound_eq N
  have hcoarse := outerCutoffExplicitBound_le N
  have hfirst :
      ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N P‖ ^ 2 ≤
        naturalCutoffOuterBoundConstant * L ^ 5 / (C : ℝ) := by
    calc
      ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N P‖ ^ 2 ≤
          2 *
            (((Real.pi ^ 2 / 6) * (2 / (P : ℝ))) ^ 2 *
                (((n * P : ℕ) : ℝ) * (harmonic (n * P) : ℝ) ^ 3) +
              32 * ((n : ℝ) ^ 2 / (((n : ℕ) * P : ℕ) : ℝ)) *
                (6 + Real.log ((((n : ℕ) * P : ℕ) : ℝ))) ^ 5 *
                  dyadicFifthMoment) := by
            simpa only [n, P] using! hraw
      _ = 2 *
          ((((Real.pi ^ 2 / 6) * 2) ^ 2 *
              (harmonic (n * P) : ℝ) ^ 3 / (C : ℝ)) +
            32 * (6 + Real.log (((n * P : ℕ) : ℝ))) ^ 5 *
              dyadicFifthMoment / (C : ℝ)) := by
          simpa only [n, P, C] using! heq
      _ ≤ 2 *
          (((((Real.pi ^ 2 / 6) * 2) ^ 2 * 14 ^ 3) +
              32 * 19 ^ 5 * dyadicFifthMoment) *
            L ^ 5 / (C : ℝ)) := by
          simpa only [n, P, C, L] using! hcoarse
      _ = naturalCutoffOuterBoundConstant * L ^ 5 / (C : ℝ) := by
          unfold naturalCutoffOuterBoundConstant
          ring
  have hLpos : 0 < L := manuscriptLogScale_pos n
  have hLC : L ^ 10 ≤ (C : ℝ) := by
    simpa only [L, C] using! manuscriptLogScale_pow_le_ceil n
  have hinv : 1 / (C : ℝ) ≤ 1 / L ^ 10 :=
    one_div_le_one_div_of_le (pow_pos hLpos 10) hLC
  have hratio : L ^ 5 / (C : ℝ) ≤ 1 / L ^ 5 := by
    calc
      L ^ 5 / (C : ℝ) = L ^ 5 * (1 / (C : ℝ)) := by ring
      _ ≤ L ^ 5 * (1 / L ^ 10) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hLpos.le 5)
      _ = 1 / L ^ 5 := by
        field_simp [hLpos.ne']
  calc
    ‖allDenominatorReconstructionL2 N -
        naturalCutoffReconstructionL2 N P‖ ^ 2 ≤
        naturalCutoffOuterBoundConstant * L ^ 5 / (C : ℝ) := hfirst
    _ = naturalCutoffOuterBoundConstant * (L ^ 5 / (C : ℝ)) := by ring
    _ ≤ naturalCutoffOuterBoundConstant * (1 / L ^ 5) :=
      mul_le_mul_of_nonneg_left hratio naturalCutoffOuterBoundConstant_nonneg
    _ = naturalCutoffOuterBoundConstant / L ^ 5 := by ring

theorem tendsto_manuscriptLogScale_succ_atTop :
    Tendsto (fun m : ℕ ↦ manuscriptLogScale (m + 1)) atTop atTop := by
  have hnat : Tendsto (fun m : ℕ ↦ (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp hnat
  simpa only [manuscriptLogScale, add_comm] using!
    hlog.atTop_add (tendsto_const_nhds :
      Tendsto (fun _m : ℕ ↦ (1 : ℝ)) atTop (nhds 1))

/-- The all-denominator reconstruction and its manuscript-scale outer
cutoff converge in the literal circle `L²` norm. -/
theorem tendsto_norm_allDenominator_sub_manuscriptOuterCutoff :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N
            (manuscriptOuterCutoff (N : ℕ))‖)
      atTop (nhds 0) := by
  let E : ℕ → ℝ := fun m ↦
    let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
    ‖allDenominatorReconstructionL2 N -
      naturalCutoffReconstructionL2 N
        (manuscriptOuterCutoff (N : ℕ))‖
  let B : ℕ → ℝ := fun m ↦
    naturalCutoffOuterBoundConstant /
      manuscriptLogScale (m + 1) ^ 5
  have hL5Top : Tendsto
      (fun m : ℕ ↦ manuscriptLogScale (m + 1) ^ 5) atTop atTop := by
    have hL2 := tendsto_manuscriptLogScale_succ_atTop.atTop_mul_atTop₀
      tendsto_manuscriptLogScale_succ_atTop
    have hL4 := hL2.atTop_mul_atTop₀ hL2
    have hL5 := hL4.atTop_mul_atTop₀
      tendsto_manuscriptLogScale_succ_atTop
    convert! hL5 using 1
    funext m
    ring
  have hB : Tendsto B atTop (nhds 0) := by
    simpa only [B] using!
      hL5Top.const_div_atTop naturalCutoffOuterBoundConstant
  have hsq : Tendsto (fun m ↦ E m ^ 2) atTop (nhds 0) := by
    apply squeeze_zero
    · exact fun m ↦ sq_nonneg (E m)
    · intro m
      simpa only [E, B] using!
        norm_sq_allDenominator_sub_manuscriptOuterCutoff_le
          (⟨m + 1, Nat.succ_pos m⟩ : ℕ+)
    · exact hB
  have hsqrt := hsq.sqrt
  simpa only [E, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using! hsqrt

/-- The same outer-tail error is negligible on the manuscript's `log N`
normalization. -/
theorem tendsto_norm_allDenominator_sub_manuscriptOuterCutoff_div_log :
    Tendsto
      (fun m : ℕ ↦
        let N : ℕ+ := ⟨m + 1, Nat.succ_pos m⟩
        ‖allDenominatorReconstructionL2 N -
          naturalCutoffReconstructionL2 N
            (manuscriptOuterCutoff (N : ℕ))‖ /
          Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hlog : Tendsto
      (fun m : ℕ ↦ Real.log (((m + 1 : ℕ) : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))
  exact tendsto_norm_allDenominator_sub_manuscriptOuterCutoff.div_atTop hlog

end

end Erdos1002
