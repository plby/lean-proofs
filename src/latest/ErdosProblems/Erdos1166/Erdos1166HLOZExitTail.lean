/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos1166.Erdos1166ExitTail
import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixA

namespace Erdos1166.HLOZExitTail

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

open ExitTail HLOZAppendixA

/-- Integer square radius corresponding to the HLOZ scale `K_j`. -/
noncomputable def radius (j : ℕ) : ℕ := ⌈K j⌉₊

/-- Number of diffusive blocks used at scale `j`.  It is already enough to
obtain the Appendix-A stretched-exponential error. -/
noncomputable def blocks (ε : ℝ) (j : ℕ) : ℕ :=
  ⌊Real.log (K j) ^ (3 / 5 + ε : ℝ)⌋₊

/-- Canonical square-exit time at the HLOZ radius. -/
noncomputable def exitTime (j : ℕ) (ω : ℕ → Direction) : ℕ :=
  squareExitTimeNat (radius j) (0, 0) ω

lemma one_le_K {j : ℕ} (hj : 1 ≤ j) : 1 ≤ K j := by
  have hK := K_pos hj
  have hlog : 0 ≤ Real.log (K j) := (one_le_log_K hj).trans' zero_le_one
  calc
    1 = Real.exp 0 := by simp
    _ ≤ Real.exp (Real.log (K j)) := Real.exp_le_exp.mpr hlog
    _ = K j := Real.exp_log hK

lemma radius_cast_le_two_mul_K {j : ℕ} (hj : 1 ≤ j) :
    (radius j : ℝ) ≤ 2 * K j := by
  exact Nat.ceil_le_two_mul (by
    have := one_le_K hj
    linarith)

lemma diffusiveExitBlockLength_radius_cast_le {j : ℕ} (hj : 1 ≤ j) :
    (diffusiveExitBlockLength (radius j) : ℝ) ≤ 9248 * K j ^ 2 := by
  have hK := one_le_K hj
  have hr := radius_cast_le_two_mul_K hj
  have hr0 : 0 ≤ (radius j : ℝ) := by positivity
  have hlin : 8 * (radius j : ℝ) + 1 ≤ 17 * K j := by nlinarith
  have hsq : (8 * (radius j : ℝ) + 1) ^ 2 ≤ (17 * K j) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hlin 2
  calc
    (diffusiveExitBlockLength (radius j) : ℝ) =
        32 * (8 * (radius j : ℝ) + 1) ^ 2 := by
      norm_num [diffusiveExitBlockLength]
      ring
    _ ≤ 32 * (17 * K j) ^ 2 := mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 9248 * K j ^ 2 := by ring

lemma eventually_scale_power_ge
    {ε C : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      C ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ) := by
  have ha : 0 < 3 / 5 + ε := by positivity
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_nat_rpow_ge ha C] with j hj hjC
  exact hjC.trans (Real.rpow_le_rpow (by positivity) (nat_le_log_K hj) ha.le)

lemma blocks_cast_le_scalePower {ε : ℝ} {j : ℕ}
    (_hε : 0 < ε) (hj : 1 ≤ j) :
    (blocks ε j : ℝ) ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Real.log_nonneg (one_le_K hj)) _)

lemma half_natPower_le_blocks {ε : ℝ} {j : ℕ}
    (hε : 0 < ε) (hj : 1 ≤ j)
    (hlarge : 2 ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ)) :
    (j : ℝ) ^ (3 / 5 + ε : ℝ) / 2 ≤ blocks ε j := by
  let A := Real.log (K j) ^ (3 / 5 + ε : ℝ)
  have ha : 0 < 3 / 5 + ε := by positivity
  have hjA : (j : ℝ) ^ (3 / 5 + ε : ℝ) ≤ A := by
    exact Real.rpow_le_rpow (by positivity) (nat_le_log_K hj) ha.le
  have hfloor : A - 1 < (blocks ε j : ℝ) := by
    simpa [A, blocks] using (Nat.sub_one_lt_floor A)
  nlinarith

lemma blocks_mul_blockLength_add_one_le_Jnat
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      blocks ε j * diffusiveExitBlockLength (radius j) + 1 ≤ Jnat ε j := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_scale_power_ge (C := 9250) hε] with j hj hA
  let A := Real.log (K j) ^ (3 / 5 + ε : ℝ)
  have hK := one_le_K hj
  have hK0 : 0 ≤ K j := zero_le_one.trans hK
  have hq := blocks_cast_le_scalePower hε hj
  have hL := diffusiveExitBlockLength_radius_cast_le hj
  have hA0 : 0 ≤ A := Real.rpow_nonneg (Real.log_nonneg hK) _
  have h9250 : 9250 ≤ A := by simpa [A] using hA
  have hAexp : A ≤ Real.exp A :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp A)
  have hcoef : 9248 * A + 1 ≤ Real.exp (2 * A) := by
    have h9250exp : (9250 : ℝ) ≤ Real.exp A := h9250.trans hAexp
    calc
      9248 * A + 1 ≤ 9249 * A := by nlinarith
      _ ≤ Real.exp A * Real.exp A := by
        exact mul_le_mul (by linarith) hAexp hA0 (Real.exp_pos A).le
      _ = Real.exp (2 * A) := by rw [← Real.exp_add]; congr 1 <;> ring
  have hreal :
      ((blocks ε j * diffusiveExitBlockLength (radius j) + 1 : ℕ) : ℝ) ≤
        J ε j := by
    calc
      ((blocks ε j * diffusiveExitBlockLength (radius j) + 1 : ℕ) : ℝ) =
          (blocks ε j : ℝ) *
            (diffusiveExitBlockLength (radius j) : ℝ) + 1 := by norm_num
      _ ≤ A * (9248 * K j ^ 2) + 1 := by gcongr
      _ = (9248 * A) * K j ^ 2 + 1 := by ring
      _ ≤ (9248 * A + 1) * K j ^ 2 := by nlinarith [sq_nonneg (K j)]
      _ ≤ Real.exp (2 * A) * K j ^ 2 := by gcongr
      _ = J ε j := by
        unfold J
        rw [show Real.exp (2 * A) = (Real.exp A) ^ 2 by
          rw [← Real.exp_nat_mul]
          norm_num]
        ring
  have hceil : J ε j ≤ (Jnat ε j : ℝ) := Nat.le_ceil (J ε j)
  exact_mod_cast hreal.trans hceil

lemma quarter_pow_le_appendix_error {ε : ℝ} {j : ℕ}
    (hε : 0 < ε) (hj : 1 ≤ j)
    (hlarge : 2 ≤ Real.log (K j) ^ (3 / 5 + ε : ℝ)) :
    ((4 : ENNReal)⁻¹) ^ blocks ε j ≤
      ENNReal.ofReal
        (Real.exp (-((1 / 2 : ℝ) * (j : ℝ) ^ (3 / 5 + ε : ℝ)))) := by
  apply (ENNReal.toReal_le_toReal (by finiteness) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat]
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hlog4 : 1 ≤ Real.log 4 := by
    have : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      exact Real.exp_one_lt_d9.trans (by norm_num)
    exact this.le
  have hq := half_natPower_le_blocks hε hj hlarge
  have hexponent :
      (1 / 2 : ℝ) * (j : ℝ) ^ (3 / 5 + ε : ℝ) ≤
        (blocks ε j : ℝ) * Real.log 4 := by
    calc
      (1 / 2 : ℝ) * (j : ℝ) ^ (3 / 5 + ε : ℝ) =
          (j : ℝ) ^ (3 / 5 + ε : ℝ) / 2 := by ring
      _ ≤ blocks ε j := hq
      _ ≤ (blocks ε j : ℝ) * Real.log 4 := by
        exact le_mul_of_one_le_right (by positivity) hlog4
  calc
    ((4 : ℝ)⁻¹) ^ blocks ε j =
        Real.exp (-((blocks ε j : ℝ) * Real.log 4)) := by
      calc
        ((4 : ℝ)⁻¹) ^ blocks ε j =
            (Real.exp (-Real.log 4)) ^ blocks ε j := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
        _ = Real.exp ((blocks ε j : ℝ) * (-Real.log 4)) := by
          rw [Real.exp_nat_mul]
        _ = Real.exp (-((blocks ε j : ℝ) * Real.log 4)) := by ring_nf
    _ ≤ Real.exp (-((1 / 2 : ℝ) *
        (j : ℝ) ^ (3 / 5 + ε : ℝ))) :=
      Real.exp_le_exp.mpr (neg_le_neg hexponent)

/-- The canonical exit time satisfies exactly the stretched-exponential
hypothesis consumed by `HLOZAppendixA.scale_probability_of_disk_and_exit`,
with the explicit constant `c=1/2`. -/
theorem eventually_exitBad_measure_le
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j : ℕ in atTop,
      incrementLaw (exitBad exitTime ε j) ≤
        ENNReal.ofReal
          (Real.exp (-((1 / 2 : ℝ) *
            (j : ℝ) ^ (3 / 5 + ε : ℝ)))) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    eventually_scale_power_ge (C := 2) hε,
    blocks_mul_blockLength_add_one_le_Jnat hε] with j hj hlarge htime
  calc
    incrementLaw (exitBad exitTime ε j) =
        incrementLaw {ω | Jnat ε j ≤ squareExitTimeNat (radius j) (0, 0) ω} := by
      rfl
    _ ≤ ((4 : ENNReal)⁻¹) ^ blocks ε j :=
      squareExitTimeNat_ge_measure_le_of_blocks (0, 0) htime
    _ ≤ ENNReal.ofReal
          (Real.exp (-((1 / 2 : ℝ) *
            (j : ℝ) ^ (3 / 5 + ε : ℝ)))) :=
      quarter_pow_le_appendix_error hε hj hlarge

/-- Appendix A's full natural-time interpolation with the exit-tail input
discharged for the canonical walk.  The remaining hypothesis is precisely
the paper's disk-exit local-time lower estimate (A.1). -/
theorem natural_time_probability_of_disk
    (M : (ℕ → Direction) → ℕ → ℕ)
    (hmono : ∀ ω, Monotone (M ω))
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        incrementLaw (diskGood M exitTime ε j)) :
    ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-(Real.log (n : ℝ) ^ (3 / 5 + ε / 2 : ℝ)))) <
        incrementLaw (naturalGood M ε n) := by
  exact natural_time_probability_of_disk_and_exit incrementLaw M exitTime hmono
    hε hεsmall (by norm_num : (0 : ℝ) < 1 / 2) hdisk
    (eventually_exitBad_measure_le hε)

/-- The full Proposition-1.3-shaped lower-deviation estimate with the
diffusive exit-time input discharged.  Thus the only remaining Appendix-A
premise is the successful-point estimate (A.1) inside the growing disk. -/
theorem eventually_prop13_lower_deviation_of_disk
    {ε : ℝ} (hε : 0 < ε) (hεsmall : ε < 2 / 15)
    (hdisk : ∀ᶠ j : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-((j : ℝ) ^ (3 / 5 + ε / 3 : ℝ)))) <
        incrementLaw
          (diskGood
            (fun ω n ↦ maxLocalTime (simpleRandomWalk ω) n)
            exitTime ε j)) :
    ∀ᶠ n : ℕ in atTop,
      simpleRandomWalkLaw
          {s | (maxLocalTime s n : ℝ) <
            1 / Real.pi * Real.log (n : ℝ) ^ 2 -
              Real.log (n : ℝ) ^ (8 / 5 + 4 * ε : ℝ)} ≤
        ENNReal.ofReal
          (Real.exp
            (-Real.exp (Real.log (n : ℝ) ^ (3 / 5 : ℝ)))) := by
  exact eventually_prop13_lower_deviation_of_disk_and_exit exitTime
    hε hεsmall (by norm_num : (0 : ℝ) < 1 / 2) hdisk
    (eventually_exitBad_measure_le hε)

end Erdos1166.HLOZExitTail
