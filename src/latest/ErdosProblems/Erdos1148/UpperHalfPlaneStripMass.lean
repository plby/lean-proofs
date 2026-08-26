import ErdosProblems.Erdos1148.UpperHalfPlaneRectanglePacking
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Finite invariant mass of a vertical Siegel strip -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure
open scoped MatrixGroups ENNReal

theorem invariant_upper_rectangle_dilation (ν : Measure UpperHalfPlane)
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (a b c d h : ℝ) (hh : 0 < h) :
    ν (upperHalfOpenRectangle (h ^ 2 * a) (h ^ 2 * b) (h ^ 2 * c) (h ^ 2 * d)) =
      ν (upperHalfOpenRectangle a b c d) := by
  have hp : 0 < h ^ 2 := sq_pos_of_pos hh
  have heq : (fun z : UpperHalfPlane => upperTriangularFrame 0 h hh.ne' • z) ⁻¹'
      upperHalfOpenRectangle (h ^ 2 * a) (h ^ 2 * b) (h ^ 2 * c) (h ^ 2 * d) =
      upperHalfOpenRectangle a b c d := by
    ext z
    simp only [Set.mem_preimage, upperHalfOpenRectangle, Set.mem_setOf_eq,
      Set.mem_Ico, Set.mem_Icc, diagonal_frame_smul_re, diagonal_frame_smul_im,
      mul_le_mul_iff_right₀ hp, mul_lt_mul_iff_right₀ hp]
  exact (measure_preimage_smul ν (upperTriangularFrame 0 h hh.ne') _).symm.trans (congrArg ν heq)

theorem invariant_upper_integer_band_bound (ν : Measure UpperHalfPlane)
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (N : ℕ) (hN : 0 < N) :
    ν (upperHalfOpenRectangle 0 1 N (2 * N)) ≤
      ν (upperClosedRectangle 0 1 1 2) / (N : ℝ≥0∞) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale := invariant_upper_rectangle_dilation ν 0 (1 / N) 1 2
    (Real.sqrt N) (Real.sqrt_pos.mpr hNR)
  have heq : ν (upperHalfOpenRectangle 0 1 N (2 * N)) =
      ν (upperHalfOpenRectangle 0 (1 / N) 1 2) := by
    simpa only [Real.sq_sqrt hNR.le, mul_zero, mul_one, mul_one_div_cancel hNR.ne',
      mul_comm (N : ℝ) 2] using hscale
  rw [heq]
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hN.ne'))
    (Or.inl (ENNReal.natCast_ne_top N))).mpr
  simpa only [mul_comm] using invariant_upper_thin_rectangle_packing ν N hN

theorem invariant_upper_dyadic_band_bound (ν : Measure UpperHalfPlane)
    [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] (n : ℕ) :
    ν (upperHalfOpenRectangle 0 1 ((2 : ℝ) ^ n) (2 ^ (n + 1))) ≤
      ν (upperClosedRectangle 0 1 1 2) * ((2 : ℝ≥0∞)⁻¹) ^ n := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ', div_eq_mul_inv, ENNReal.inv_pow]
    using invariant_upper_integer_band_bound ν (2 ^ n) (pow_pos (by decide) n)

theorem invariant_upper_siegel_strip_finite (ν : Measure UpperHalfPlane)
    [IsFiniteMeasureOnCompacts ν] [SMulInvariantMeasure SL(2, ℝ) UpperHalfPlane ν] :
    ν {z : UpperHalfPlane | z.re ∈ Set.Ico 0 1 ∧ 1 ≤ z.im} < ∞ := by
  have hsub : {z : UpperHalfPlane | z.re ∈ Set.Ico 0 1 ∧ 1 ≤ z.im} ⊆
      ⋃ n : ℕ, upperHalfOpenRectangle 0 1 ((2 : ℝ) ^ n) (2 ^ (n + 1)) := by
    rintro z ⟨hre, him⟩
    obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near him (by norm_num : (1 : ℝ) < 2)
    exact Set.mem_iUnion.mpr ⟨n, hre, hn₁, hn₂.le⟩
  calc
    ν {z : UpperHalfPlane | z.re ∈ Set.Ico 0 1 ∧ 1 ≤ z.im} ≤
        ∑' n : ℕ, ν (upperHalfOpenRectangle 0 1 ((2 : ℝ) ^ n) (2 ^ (n + 1))) :=
      (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' n : ℕ, ν (upperClosedRectangle 0 1 1 2) * ((2 : ℝ≥0∞)⁻¹) ^ n :=
      ENNReal.tsum_le_tsum (invariant_upper_dyadic_band_bound ν)
    _ = ν (upperClosedRectangle 0 1 1 2) * 2 := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      norm_num
    _ < ∞ := ENNReal.mul_lt_top
      (isCompact_upperClosedRectangle 0 1 1 2 (by norm_num)).measure_lt_top (by norm_num)

end Erdos1148.DukeArithmetic
