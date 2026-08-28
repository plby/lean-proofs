import Wikipedia.HopfProblem.ToricCoordinates
import Mathlib.Algebra.BigOperators.Field

/-!
# Position estimates for the cusp action

The logarithmic barycentric coordinates bound the rescaled position on each
fixed chart. The small-drift estimate then bounds lattice elements whenever
a translate meets another fixed chart. All norms here are the usual sup
norms on finite function spaces.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def latticeReal (v : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (v i : ℝ)

theorem norm_latticeReal (v : Fin 2 → ℤ) : ‖latticeReal v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact (Int.norm_cast_real (v i)).le.trans (norm_le_pi_norm v i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← Int.norm_cast_real (v i)]
    exact norm_le_pi_norm (latticeReal v) i

theorem lattice_bounded_finite (R : ℝ) : {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R}.Finite := by
  have he : {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R} = Metric.closedBall 0 R := by
    ext v
    simp [norm_latticeReal, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact (isCompact_closedBall _ _).finite_of_discrete

/-- The entrywise sup norm, specified explicitly to avoid choosing a
noncanonical norm instance for matrices. -/
def entryNorm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

theorem entryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ entryNorm A := norm_nonneg _

theorem norm_cuspVector (v : Fin 2 → ℤ) : ‖latticeReal (cuspVector v)‖ = ‖latticeReal v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm (latticeReal v) 1
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal v) 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal (cuspVector v)) 1
    · exact norm_le_pi_norm (latticeReal (cuspVector v)) 0

theorem norm_matrix_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    ‖A *ᵥ v‖ ≤ 2 * entryNorm A * ‖v‖ := by
  have hA := entryNorm_nonneg A
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, entryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (A i) j).trans
          (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
        (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * entryNorm A * ‖v‖ := by simp; ring

theorem position_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) - position x = latticeReal (cuspVector v) +
      (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v) := by
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [position_twistedTranslate C v hx ht]
  simp only [latticeReal, div_eq_mul_inv, Matrix.mulVec, dotProduct]
  ring

/-- A small logarithmic multiplier cannot cancel the integral shear. -/
theorem lattice_bound_of_small_drift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ‖latticeReal v‖ ≤ 2 * ‖position (twistedTranslate C v x) - position x‖ := by
  let e := (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v)
  have hneg : 0 < -Real.log ‖time x‖ := neg_pos.mpr ht
  have he : ‖e‖ ≤ ‖latticeReal v‖ / 2 := by
    calc
      ‖e‖ = (-Real.log ‖time x‖)⁻¹ * ‖driftMatrix C (time x) *ᵥ latticeReal v‖ := by
        simp [e, norm_smul, Real.norm_eq_abs, abs_of_neg ht]
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * entryNorm (driftMatrix C (time x)) * ‖latticeReal v‖) :=
        mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity)
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * (-Real.log ‖time x‖ / 4) * ‖latticeReal v‖) := by
        gcongr
      _ = ‖latticeReal v‖ / 2 := by field_simp [ht.ne]; ring
  have htriangle := norm_add_le
    (latticeReal (cuspVector v) + e) (-e)
  have hnorm : ‖latticeReal (cuspVector v) + e‖ =
      ‖position (twistedTranslate C v x) - position x‖ := by
    rw [position_displacement C v hx ht.ne]
  simp only [add_neg_cancel_right, norm_neg, norm_cuspVector] at htriangle
  rw [hnorm] at htriangle
  linarith

def barycentric (z : CoordinateSpace 3) : Fin 3 → ℝ :=
  fun j => logNorm z j / Real.log ‖Triangle.time z‖

theorem barycentric_sum (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus)
    (ht : Real.log ‖Triangle.time z‖ ≠ 0) : ∑ j, barycentric z j = 1 := by
  simp only [barycentric, ← Finset.sum_div, logNorm_sum s hz, div_self ht]

theorem position_inclusion (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus)
    (i : Fin 2) : position (inclusion s z) i =
      ∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j := by
  simp only [position, time_inclusion, logCoordinates_inclusion s hz, Matrix.mulVec,
    dotProduct, barycentric, Finset.sum_div, mul_div_assoc]
  rfl

def chartSize (s : Triangle) : ℝ := ‖(s.a : ℝ)‖ + ‖(s.b : ℝ)‖ + 1

theorem chartSize_pos (s : Triangle) : 0 < chartSize s := by unfold chartSize; positivity

theorem ray_norm_le_chartSize (s : Triangle) (i : Fin 2) (j : Fin 3) :
    ‖(s.rays i.castSucc j : ℝ)‖ ≤ chartSize s := by
  have ha : ‖(s.a : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.b : ℝ)]
  have hb : ‖(s.b : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.a : ℝ)]
  have ha' : ‖(s.a : ℝ) + 1‖ ≤ chartSize s :=
    (norm_add_le _ _).trans (by simp [chartSize])
  have hb' : ‖(s.b : ℝ) + 1‖ ≤ chartSize s :=
    (norm_add_le _ _).trans (by simp [chartSize])
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    first
    | simpa [rays, hs] using ha
    | simpa [rays, hs] using hb
    | simpa [rays, hs] using ha'
    | simpa [rays, hs] using hb'

theorem barycentric_lower_bound {z : CoordinateSpace 3} (hz : z ∈ torus)
    {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    -(Real.log S / (-Real.log ε)) ≤ barycentric z j := by
  have hn : Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
  have hlogt : Real.log ‖Triangle.time z‖ < Real.log ε :=
    Real.log_lt_log (norm_pos_iff.mpr hn) ht
  have hη : 0 ≤ Real.log S / (-Real.log ε) :=
    div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr hlogε.le)
  have hlogz : Real.log ‖z j‖ ≤ Real.log S :=
    Real.log_le_log (norm_pos_iff.mpr (hz j)) (hzS j)
  have hmul := mul_le_mul_of_nonpos_left hlogt.le (neg_nonpos.mpr hη)
  have he : -(Real.log S / (-Real.log ε)) * Real.log ε = Real.log S := by
    field_simp [hlogε.ne]
  rw [he] at hmul
  exact (le_div_iff_of_neg (hlogt.trans hlogε)).mpr (hlogz.trans hmul)

theorem barycentric_norm_bound {z : CoordinateSpace 3} (hz : z ∈ torus)
    {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    ‖barycentric z j‖ ≤ 1 + 2 * (Real.log S / (-Real.log ε)) := by
  let η := Real.log S / (-Real.log ε)
  have hη : 0 ≤ η := div_nonneg (Real.log_nonneg hS)
    (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hlow (k : Fin 3) : -η ≤ barycentric z k :=
    barycentric_lower_bound hz hS hε hε1 ht hzS k
  have hn : Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hs := barycentric_sum referenceTriangle hz
    (Real.log_neg (norm_pos_iff.mpr hn) (ht.trans hε1)).ne
  have hsum : ∑ k : Fin 3, (barycentric z k + η) = 1 + 3 * η := by
    rw [Finset.sum_add_distrib, hs]
    simp
  have hu := Finset.single_le_sum
    (s := Finset.univ) (f := fun k : Fin 3 => barycentric z k + η)
    (fun k _ => by linarith [hlow k]) (Finset.mem_univ j)
  rw [hsum] at hu
  change ‖barycentric z j‖ ≤ 1 + 2 * η
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hlow j]

def positionBound (s : Triangle) (S ε : ℝ) : ℝ :=
  3 * chartSize s * (1 + 2 * (Real.log S / (-Real.log ε)))

theorem position_norm_bound (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus)
    {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) :
    ‖position (inclusion s z)‖ ≤ positionBound s S ε := by
  have hη : 0 ≤ Real.log S / (-Real.log ε) := div_nonneg (Real.log_nonneg hS)
    (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hsize := chartSize_pos s
  apply (pi_norm_le_iff_of_nonneg (by unfold positionBound; positivity)).mpr
  intro i
  rw [position_inclusion s hz]
  calc
    ‖∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j‖
        ≤ ∑ j, ‖(s.rays i.castSucc j : ℝ) * barycentric z j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, chartSize s * (1 + 2 * (Real.log S / (-Real.log ε))) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (ray_norm_le_chartSize s i j)
        (barycentric_norm_bound hz hS hε hε1 ht hzS j) (norm_nonneg _) (chartSize_pos s).le
    _ = positionBound s S ε := by simp [positionBound]; ring

end Wikipedia.HopfProblem.ToricSpace
