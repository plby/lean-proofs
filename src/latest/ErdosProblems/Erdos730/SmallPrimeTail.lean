/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.FullDensityBudget
import ErdosProblems.Erdos730.PrimeBands

/-!
# Erdős 730: uniform fixed-depth tail budget

The sharp fixed-depth main term uses `4⁻ʳ`.  Uniformly in the remaining
depths, the complete-block argument uses the coarser ratio `(2/3)ʳ` because
every relevant prime is at least five.  This file proves that the resulting
tail of Mertens main terms vanishes as the retained depth tends to infinity.
-/

open Filter
open scoped Topology

namespace Erdos730.SmallPrimeTail

open Erdos730.FullDensity

noncomputable section

def uniformDepthMainTerm (r : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ r * fixedDepthPrimeBandMainTerm r

def uniformDepthMainTail (R : ℕ) : ℝ :=
  ∑' n : ℕ, uniformDepthMainTerm (n + R)

theorem fixedDepthPrimeBandMainTerm_nonneg (r : ℕ) :
    0 ≤ fixedDepthPrimeBandMainTerm r := by
  unfold fixedDepthPrimeBandMainTerm
  have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  apply Real.log_nonneg
  rw [le_div_iff₀ hden]
  push_cast
  norm_num

theorem fixedDepthPrimeBandMainTerm_le_one (r : ℕ) :
    fixedDepthPrimeBandMainTerm r ≤ 1 := by
  exact (Erdos730.log_density_ratio_le_inv_succ r).trans <| by
    have hden : (0 : ℝ) < (r + 1 : ℕ) := by positivity
    exact (div_le_one hden).2 (by norm_num)

theorem uniformDepthMainTerm_nonneg (r : ℕ) :
    0 ≤ uniformDepthMainTerm r := by
  exact mul_nonneg (pow_nonneg (by norm_num) r)
    (fixedDepthPrimeBandMainTerm_nonneg r)

theorem uniformDepthMainTerm_le_geometric (r : ℕ) :
    uniformDepthMainTerm r ≤ (2 / 3 : ℝ) ^ r := by
  unfold uniformDepthMainTerm
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (fixedDepthPrimeBandMainTerm_le_one r) (pow_nonneg (by norm_num) r)

theorem uniformDepthMainTerm_summable : Summable uniformDepthMainTerm := by
  exact Summable.of_nonneg_of_le uniformDepthMainTerm_nonneg
    uniformDepthMainTerm_le_geometric
    (summable_geometric_of_lt_one (by norm_num) (by norm_num))

theorem uniformDepthMainTail_nonneg (R : ℕ) : 0 ≤ uniformDepthMainTail R := by
  unfold uniformDepthMainTail
  exact tsum_nonneg fun n ↦ uniformDepthMainTerm_nonneg (n + R)

theorem uniformDepthMainTail_le (R : ℕ) :
    uniformDepthMainTail R ≤ 3 * (2 / 3 : ℝ) ^ R := by
  have hgeom : Summable (fun n : ℕ ↦ (2 / 3 : ℝ) ^ (n + R)) := by
    simpa only [pow_add, mul_comm] using
      (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).mul_left ((2 / 3 : ℝ) ^ R)
  have hmain : Summable (fun n : ℕ ↦ uniformDepthMainTerm (n + R)) :=
    hgeom.of_nonneg_of_le
      (fun n ↦ uniformDepthMainTerm_nonneg (n + R))
      (fun n ↦ uniformDepthMainTerm_le_geometric (n + R))
  calc
    uniformDepthMainTail R ≤ ∑' n : ℕ, (2 / 3 : ℝ) ^ (n + R) := by
      unfold uniformDepthMainTail
      exact hmain.tsum_le_tsum
        (fun n ↦ uniformDepthMainTerm_le_geometric (n + R)) hgeom
    _ = 3 * (2 / 3 : ℝ) ^ R := by
      calc
        (∑' n : ℕ, (2 / 3 : ℝ) ^ (n + R)) =
            ∑' n : ℕ, (2 / 3 : ℝ) ^ n * (2 / 3 : ℝ) ^ R := by
          congr 1
          funext n
          rw [pow_add]
        _ = (∑' n : ℕ, (2 / 3 : ℝ) ^ n) * (2 / 3 : ℝ) ^ R :=
          tsum_mul_right
        _ = 3 * (2 / 3 : ℝ) ^ R := by
          rw [tsum_geometric_of_norm_lt_one
            (by norm_num : ‖(2 / 3 : ℝ)‖ < 1)]
          norm_num

theorem uniformDepthMain_sum_Ico_le_tail (R J : ℕ) :
    (∑ r ∈ Finset.Ico R J, uniformDepthMainTerm r) ≤
      uniformDepthMainTail R := by
  have hshift : Summable (fun n : ℕ ↦ uniformDepthMainTerm (n + R)) :=
    uniformDepthMainTerm_summable.comp_injective
      (fun _ _ h ↦ Nat.add_right_cancel h)
  rw [Finset.sum_Ico_eq_sum_range]
  unfold uniformDepthMainTail
  simpa only [add_comm] using
    hshift.sum_le_tsum (Finset.range (J - R))
      (fun n _ ↦ uniformDepthMainTerm_nonneg (n + R))

/-- Equation (46), at the level of the Mertens main terms: the entire
coarsely weighted fixed-depth tail tends to zero. -/
theorem tendsto_uniformDepthMainTail_zero :
    Tendsto uniformDepthMainTail atTop (𝓝 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall uniformDepthMainTail_nonneg
  · exact Eventually.of_forall uniformDepthMainTail_le
  · simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num : (2 : ℝ) / 3 < 1)).const_mul 3

/-! ## The deepest moving bands -/

/-- Natural version of the moving depth cutoff used in equation (45). -/
def movingDepthLog (X : ℕ) : ℕ := Nat.log 3 (Nat.sqrt X)

/-- Majorant for all depths beyond `movingDepthLog X - 2`. -/
def deepestBandMajorant (X : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (movingDepthLog X - 1) *
    reciprocalPrimeSum (Nat.sqrt X)

theorem tendsto_natSqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨N * N, fun X hX ↦ ?_⟩
  exact Nat.le_sqrt.mpr hX

theorem tendsto_natLog_three_atTop :
    Tendsto (Nat.log 3) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro N
  refine ⟨3 ^ N, fun X hX ↦ ?_⟩
  exact Nat.le_log_of_pow_le (by norm_num) hX

theorem tendsto_movingDepthLog_atTop :
    Tendsto movingDepthLog atTop atTop := by
  exact tendsto_natLog_three_atTop.comp tendsto_natSqrt_atTop

def deepestDepthControl (m : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ (m - 1) *
    (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)

theorem tendsto_deepestDepthControl_zero :
    Tendsto deepestDepthControl atTop (𝓝 0) := by
  let q : ℝ := 2 / 3
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hpow : Tendsto (fun m : ℕ ↦ q ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hmulpow : Tendsto (fun m : ℕ ↦ (m : ℝ) * q ^ m)
      atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hq0 hq1
  have hinside : Tendsto (fun m : ℕ ↦
      q ^ m * (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3))
      atTop (𝓝 0) := by
    have hsum := hpow.add ((hmulpow.add hpow).const_mul (Real.log 3))
    convert hsum using 1
    · funext m
      push_cast
      ring
    · simp
  have hscaled := hinside.const_mul ((q ^ 1)⁻¹)
  have hscaled' : Tendsto (fun m : ℕ ↦
      (q ^ 1)⁻¹ *
        (q ^ m * (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hscaled
  apply hscaled'.congr'
  filter_upwards [eventually_ge_atTop 1] with m hm
  unfold deepestDepthControl
  rw [pow_sub₀ q (by norm_num [q]) hm]
  norm_num [q]
  ring

theorem deepestBandMajorant_nonneg (X : ℕ) :
    0 ≤ deepestBandMajorant X := by
  unfold deepestBandMajorant
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (reciprocalPrimeSum_nonneg _)

theorem deepestBandMajorant_le_control
    {X : ℕ} (hX : 9 ≤ X) :
    deepestBandMajorant X ≤ deepestDepthControl (movingDepthLog X) := by
  let N := Nat.sqrt X
  let m := Nat.log 3 N
  have hN3 : 3 ≤ N := by
    dsimp only [N]
    apply Nat.le_sqrt.mpr
    norm_num1
    exact hX
  have hNpos : 0 < N := by omega
  have hm1 : 1 ≤ m := by
    dsimp only [m]
    exact Nat.le_log_of_pow_le (by norm_num) hN3
  have hNpow : N < 3 ^ (m + 1) := by
    dsimp only [m]
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self (by norm_num : 1 < 3) N
  have hlogN : Real.log N < ((m + 1 : ℕ) : ℝ) * Real.log 3 := by
    have hcast : (N : ℝ) < ((3 ^ (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast hNpow
    have hlog := Real.strictMonoOn_log
      (show (N : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        exact_mod_cast hNpos)
      (show ((3 ^ (m + 1) : ℕ) : ℝ) ∈ Set.Ioi 0 by
        rw [Set.mem_Ioi]
        positivity)
      hcast
    rw [Nat.cast_pow, Real.log_pow] at hlog
    simpa [mul_comm] using hlog
  have hrec : reciprocalPrimeSum N ≤
      1 + ((m + 1 : ℕ) : ℝ) * Real.log 3 :=
    (reciprocalPrimeSum_le_one_add_log N).trans
      (add_le_add le_rfl hlogN.le)
  unfold deepestBandMajorant deepestDepthControl movingDepthLog
  change (2 / 3 : ℝ) ^ (m - 1) * reciprocalPrimeSum N ≤
    (2 / 3 : ℝ) ^ (m - 1) *
      (1 + ((m + 1 : ℕ) : ℝ) * Real.log 3)
  exact mul_le_mul_of_nonneg_left hrec (pow_nonneg (by norm_num) _)

/-- The deepest-band payment in equation (45) is `o(1)`. -/
theorem tendsto_deepestBandMajorant_zero :
    Tendsto deepestBandMajorant atTop (𝓝 0) := by
  have hcontrol : Tendsto
      (fun X ↦ deepestDepthControl (movingDepthLog X)) atTop (𝓝 0) :=
    tendsto_deepestDepthControl_zero.comp tendsto_movingDepthLog_atTop
  apply squeeze_zero'
  · exact Eventually.of_forall deepestBandMajorant_nonneg
  · filter_upwards [eventually_ge_atTop 9] with X hX
    exact deepestBandMajorant_le_control hX
  · exact hcontrol

/-! ## Summed quantitative Mertens error -/

def uniformMertensWeight (r : ℕ) : ℝ :=
  (2 / 3 : ℝ) ^ r * ((r + 2 : ℕ) : ℝ)

def uniformMertensWeightSeries : ℝ :=
  ∑' r : ℕ, uniformMertensWeight r

theorem uniformMertensWeight_nonneg (r : ℕ) :
    0 ≤ uniformMertensWeight r := by
  unfold uniformMertensWeight
  positivity

theorem uniformMertensWeight_summable :
    Summable uniformMertensWeight := by
  have hq : ‖(2 / 3 : ℝ)‖ < 1 := by norm_num
  have hlinear : Summable (fun r : ℕ ↦
      (r : ℝ) * (2 / 3 : ℝ) ^ r) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq)
  have hconst : Summable (fun r : ℕ ↦
      2 * (2 / 3 : ℝ) ^ r) :=
    (summable_geometric_of_norm_lt_one hq).mul_left 2
  convert hlinear.add hconst using 1
  funext r
  unfold uniformMertensWeight
  push_cast
  ring

theorem uniformMertensWeightSeries_nonneg :
    0 ≤ uniformMertensWeightSeries := by
  unfold uniformMertensWeightSeries
  exact tsum_nonneg uniformMertensWeight_nonneg

/-- A uniform upper bound for the sum of all quantitative Mertens endpoint
errors in equation (44). -/
def uniformMertensErrorMajorant (X : ℕ) : ℝ :=
  2 * reciprocalPrimeMertensErrorConstant * uniformMertensWeightSeries /
    Real.log (X : ℝ)

theorem tendsto_uniformMertensErrorMajorant_zero :
    Tendsto uniformMertensErrorMajorant atTop (𝓝 0) := by
  have hlogInv : Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ))⁻¹)
      atTop (𝓝 0) :=
    Real.tendsto_log_atTop.inv_tendsto_atTop.comp
      tendsto_natCast_atTop_atTop
  have hscaled := hlogInv.const_mul
    (2 * reciprocalPrimeMertensErrorConstant * uniformMertensWeightSeries)
  simpa only [uniformMertensErrorMajorant, div_eq_mul_inv, mul_zero] using! hscaled

/-- Quantitative equation (44), after multiplying by the uniform geometric
depth weight. -/
theorem weightedFixedDepthReciprocalPrimeBand_le
    (r : ℕ) {X : ℝ} (hX : 1 < X)
    (hlower : 2 ≤ fixedDepthPrimeBandLower r X) :
    (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r X ≤
      uniformDepthMainTerm r +
        (2 * reciprocalPrimeMertensErrorConstant / Real.log X) *
          uniformMertensWeight r := by
  have hband := fixedDepthReciprocalPrimeBand_le r hX hlower
  have hq : 0 ≤ (2 / 3 : ℝ) ^ r := pow_nonneg (by norm_num) r
  calc
    (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r X ≤
        (2 / 3 : ℝ) ^ r *
          (fixedDepthPrimeBandMainTerm r +
            2 * reciprocalPrimeMertensErrorConstant *
              (((r + 2 : ℕ) : ℝ)) / Real.log X) :=
      mul_le_mul_of_nonneg_left hband hq
    _ = uniformDepthMainTerm r +
        (2 * reciprocalPrimeMertensErrorConstant / Real.log X) *
          uniformMertensWeight r := by
      unfold uniformDepthMainTerm uniformMertensWeight
      ring

/-- Uniform summed form of equation (44) over any finite collection of
depths whose lower endpoints are at least two. -/
theorem weightedFixedDepthBand_sum_le_main_add_error
    (s : Finset ℕ) {X : ℕ} (hX : 1 < X)
    (hlower : ∀ r ∈ s,
      2 ≤ fixedDepthPrimeBandLower r (X : ℝ)) :
    (∑ r ∈ s,
      (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r (X : ℝ)) ≤
      (∑ r ∈ s, uniformDepthMainTerm r) +
        uniformMertensErrorMajorant X := by
  let coeff : ℝ :=
    2 * reciprocalPrimeMertensErrorConstant / Real.log (X : ℝ)
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hcoeff : 0 ≤ coeff := by
    dsimp only [coeff]
    positivity [reciprocalPrimeMertensErrorConstant_pos]
  have hsumWeight :
      (∑ r ∈ s, uniformMertensWeight r) ≤
        uniformMertensWeightSeries := by
    unfold uniformMertensWeightSeries
    exact uniformMertensWeight_summable.sum_le_tsum s
      (fun r _ ↦ uniformMertensWeight_nonneg r)
  calc
    (∑ r ∈ s,
        (2 / 3 : ℝ) ^ r * fixedDepthReciprocalPrimeBand r (X : ℝ)) ≤
        ∑ r ∈ s, (uniformDepthMainTerm r +
          coeff * uniformMertensWeight r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact weightedFixedDepthReciprocalPrimeBand_le r
        (by exact_mod_cast hX) (hlower r hr)
    _ = (∑ r ∈ s, uniformDepthMainTerm r) +
        coeff * ∑ r ∈ s, uniformMertensWeight r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ r ∈ s, uniformDepthMainTerm r) +
        coeff * uniformMertensWeightSeries := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hsumWeight hcoeff)
    _ = (∑ r ∈ s, uniformDepthMainTerm r) +
        uniformMertensErrorMajorant X := by
      unfold uniformMertensErrorMajorant
      dsimp only [coeff]
      ring

#print axioms uniformDepthMainTail_le
#print axioms tendsto_uniformDepthMainTail_zero
#print axioms tendsto_deepestBandMajorant_zero
#print axioms tendsto_uniformMertensErrorMajorant_zero
#print axioms weightedFixedDepthBand_sum_le_main_add_error

end

end Erdos730.SmallPrimeTail
