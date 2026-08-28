import Wikipedia.HopfProblem.CuspCentralHomologyBaseTorus
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverOverlap

/-!
# The actual zero-base-coordinate locus in the central overlap

The marked first base coordinate is the second honeycomb coordinate
with its sign reversed, modulo the integral lattice.  In the literal
fundamental hexagon each coordinate has absolute value at most `2/3`.
Consequently a zero first base-circle coordinate forces the unique
interior representative to lie on the horizontal axis.  This is an
identity in the actual geometric overlap, before applying homology.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspBoundaryTopVanishing

open ToricSpace CuspRetraction CuspHoneycomb CuspHoneycombTiling
open CuspCentralHomology PeriodTorusHigherHomology

/-- An integral circle-zero representative in the actual hexagon has zero second coordinate. -/
theorem hexagon_second_eq_zero_of_baseFirstZero {y : Plane} (hy : y ∈ baseCell)
    (hzero : baseTorusPoint y 0 = 0) : y 1 = 0 := by
  change ((-y 1 : ℝ) : AddCircle (1 : ℝ)) = 0 at hzero
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) = -y 1 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hb : |(n : ℝ)| < 1 := by
    rw [hn', abs_neg]
    exact (baseCell_coordinate_bound_sharp hy 1).trans_lt (by norm_num)
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hb).1
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hb).2
  have hnzero : n = 0 := by omega
  rw [hnzero, Int.cast_zero] at hn'
  linarith

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : SmallDrift C r)

/-- The original base projection on the actual annular product chart. -/
theorem baseTorusProjection_overlapPhaseHomeomorph (a : ℝ) (p : OverlapPhaseCell a) :
    baseTorusProjection C r hr
        (overlapPhaseHomeomorph C r hr hr1 hC hR a p : QuotientCentralFibre C r) =
      baseTorusPoint (p.2 : Plane) := by
  rw [overlapPhaseHomeomorph_coe, baseTorusProjection_honeycombCollapseMap]

/-- Recovering the genuine overlap chart preserves the original marked base coordinates. -/
theorem baseTorusPoint_overlapPhaseHomeomorph_symm (a : ℝ)
    (q : overlapRegion C r hr a) :
    baseTorusPoint
        (((overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2 : Plane) =
      baseTorusProjection C r hr (q : QuotientCentralFibre C r) := by
  have h := baseTorusProjection_overlapPhaseHomeomorph C r hr hr1 hC hR a
    ((overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The zero-first-base-coordinate locus has a literal horizontal annular representative. -/
theorem overlapPhaseHomeomorph_symm_second_zero (a : ℝ)
    (q : overlapRegion C r hr a)
    (hzero : baseTorusProjection C r hr (q : QuotientCentralFibre C r) 0 = 0) :
    (((overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2 : Plane) 1 = 0 := by
  apply hexagon_second_eq_zero_of_baseFirstZero
  · exact (Radial.mem_baseCell_iff _).mpr
      ((overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2.2.2.le
  · rw [baseTorusPoint_overlapPhaseHomeomorph_symm]
    exact hzero

end Wikipedia.HopfProblem.CuspBoundaryTopVanishing
