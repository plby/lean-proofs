import Wikipedia.HopfProblem.ToricBounds
import Wikipedia.HopfProblem.ToricCones

/-!
# Bounded representatives for the twisted action

The real displacement map is an invertible perturbation of the integral
quarter-turn. Rounding its inverse coordinates moves every torus point to
a uniformly bounded position. This is the reduction step in the proof of
properness of the cusp filling.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

def realCuspVector : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![v 1, -v 0]
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp

theorem realCuspVector_latticeReal (v : Fin 2 → ℤ) :
    realCuspVector (latticeReal v) = latticeReal (cuspVector v) := by
  ext i
  fin_cases i <;> simp [realCuspVector, latticeReal, cuspVector]

theorem realCuspVector_norm (v : Fin 2 → ℝ) : ‖realCuspVector v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · simpa [realCuspVector] using norm_le_pi_norm v 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [realCuspVector] using norm_le_pi_norm (realCuspVector v) 1
    · exact norm_le_pi_norm (realCuspVector v) 0

def displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  realCuspVector + (Real.log ‖t‖)⁻¹ • (driftMatrix C t).mulVecLin

theorem displacement_error_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v - realCuspVector v‖ ≤ ‖v‖ / 2 := by
  have hneg : 0 < -Real.log ‖t‖ := neg_pos.mpr ht
  have he : displacement C t v - realCuspVector v =
      (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v) := by
    simp [displacement]
  rw [he]
  calc
    ‖(Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v)‖ =
        (-Real.log ‖t‖)⁻¹ * ‖driftMatrix C t *ᵥ v‖ := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_neg ht]
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * entryNorm (driftMatrix C t) * ‖v‖) :=
      mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity)
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * (-Real.log ‖t‖ / 4) * ‖v‖) := by gcongr
    _ = ‖v‖ / 2 := by field_simp [ht.ne]; ring

theorem displacement_lower_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖v‖ ≤ 2 * ‖displacement C t v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_sub_le (displacement C t v)
    (displacement C t v - realCuspVector v)
  rw [sub_sub_cancel, realCuspVector_norm] at htri
  linarith

theorem displacement_upper_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v‖ ≤ 3 / 2 * ‖v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_add_le (realCuspVector v) (displacement C t v - realCuspVector v)
  rw [add_sub_cancel, realCuspVector_norm] at htri
  linarith

theorem displacement_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    Function.Bijective (displacement C t) := by
  have hinj : Function.Injective (displacement C t) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hb := displacement_lower_bound C ht hR v
    rw [hv, norm_zero, mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

theorem exists_integer_rounding (u : Fin 2 → ℝ) :
    ∃ v : Fin 2 → ℤ, ‖u + latticeReal v‖ ≤ 1 := by
  refine ⟨fun i => -⌊u i⌋, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [Pi.add_apply, latticeReal, Int.cast_neg, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [Int.floor_le (u i), Int.lt_floor_add_one (u i)]

theorem position_twistedTranslate_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) = position x + displacement C (time x) (latticeReal v) := by
  have he := position_displacement C v hx ht
  rw [← realCuspVector_latticeReal] at he
  change position (twistedTranslate C v x) - position x =
    displacement C (time x) (latticeReal v) at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem exists_bounded_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ, ‖position (twistedTranslate C v x)‖ ≤ 2 := by
  obtain ⟨u, hu⟩ := (displacement_bijective C ht hR).surjective (position x)
  obtain ⟨v, hv⟩ := exists_integer_rounding u
  refine ⟨v, ?_⟩
  rw [position_twistedTranslate_displacement C v hx ht.ne, ← hu, ← map_add]
  exact (displacement_upper_bound C ht hR _).trans (by nlinarith)

theorem exists_torus_chart (s : Triangle) {x : Space} (hx : x ∈ openTorus) :
    ∃ z ∈ torus, inclusion s z = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine ⟨chartChange referenceTriangle s z, monomial_mapsTo_torus _ hz, ?_⟩
  exact ((inclusion_eq_iff referenceTriangle s z _).mpr
    ⟨torus_subset_overlap _ _ hz, rfl⟩).symm

def positionPoint (y : Fin 2 → ℝ) : RealCoordinates := ![y 0, y 1, 1]

theorem generate_barycentric (s : Triangle) {z : CoordinateSpace 3} (hz : z ∈ torus)
    (ht : Real.log ‖Triangle.time z‖ ≠ 0) :
    s.generate (barycentric z) = positionPoint (position (inclusion s z)) := by
  ext i
  fin_cases i
  · exact (position_inclusion s hz 0).symm
  · exact (position_inclusion s hz 1).symm
  · simpa [generate, Matrix.mulVec, dotProduct, positionPoint] using barycentric_sum s hz ht

theorem unit_chart_of_position_mem_cone (s : Triangle) {z : CoordinateSpace 3}
    (hz : z ∈ torus) (ht : Real.log ‖Triangle.time z‖ < 0)
    (hp : positionPoint (position (inclusion s z)) ∈ s.cone) : ‖z‖ ≤ 1 := by
  rw [← generate_barycentric s hz ht.ne, mem_cone, coordinates_generate] at hp
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  apply (Real.log_nonpos_iff (norm_nonneg _)).mp
  have hj := (le_div_iff_of_neg ht).mp (hp j)
  simpa [barycentric, logNorm] using hj

def boundedTriangles : Set Triangle :=
  {s | (-3 ≤ s.a ∧ s.a ≤ 3) ∧ (-3 ≤ s.b ∧ s.b ≤ 3)}

theorem boundedTriangles_finite : boundedTriangles.Finite := by
  have hf := (Set.finite_Icc (-3 : ℤ) 3).prod
    ((Set.finite_Icc (-3 : ℤ) 3).prod (Set.finite_univ (α := Bool)))
  have hi : Function.Injective (fun s : Triangle => (s.a, s.b, s.upper)) := by
    intro s t h
    simpa only [Prod.mk.injEq, Triangle.ext_iff, and_assoc] using h
  apply (hf.preimage hi.injOn).subset
  intro s hs
  exact ⟨hs.1, hs.2, Set.mem_univ _⟩

theorem exists_bounded_cone (y : Fin 2 → ℝ) (hy : ‖y‖ ≤ 2) :
    ∃ s ∈ boundedTriangles, positionPoint y ∈ s.cone := by
  let a := ⌊y 0⌋
  let b := ⌊y 1⌋
  have ha : (a : ℝ) ≤ y 0 := Int.floor_le _
  have hb : (b : ℝ) ≤ y 1 := Int.floor_le _
  have ha' : y 0 < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hb' : y 1 < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hy0 : -(2 : ℝ) ≤ y 0 ∧ y 0 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 0).trans hy)
  have hy1 : -(2 : ℝ) ≤ y 1 ∧ y 1 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 1).trans hy)
  have haI : (-3 : ℤ) ≤ a ∧ a ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (a : ℝ) by linarith)
    · exact_mod_cast (show (a : ℝ) ≤ 3 by linarith)
  have hbI : (-3 : ℤ) ≤ b ∧ b ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (b : ℝ) by linarith)
    · exact_mod_cast (show (b : ℝ) ≤ 3 by linarith)
  by_cases hsum : y 0 + y 1 ≤ 1 + (a : ℝ) + b
  · refine ⟨⟨a, b, false⟩, ⟨haI, hbI⟩, ?_⟩
    rw [mem_cone, coordinates_lower]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith
  · refine ⟨⟨a, b, true⟩, ⟨haI, hbI⟩, ?_⟩
    rw [mem_cone, coordinates_upper]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith

theorem exists_unit_chart_of_bounded_position {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0) (hp : ‖position x‖ ≤ 2) :
    ∃ s ∈ boundedTriangles, ∃ z ∈ Metric.closedBall (0 : CoordinateSpace 3) 1,
      inclusion s z = x := by
  obtain ⟨s, hs, hp⟩ := exists_bounded_cone (position x) hp
  obtain ⟨z, hz, rfl⟩ := exists_torus_chart s hx
  refine ⟨s, hs, z, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact unit_chart_of_position_mem_cone s hz (by simpa using ht) hp

theorem exists_bounded_chart_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ, ∃ s ∈ boundedTriangles,
      ∃ z ∈ Metric.closedBall (0 : CoordinateSpace 3) 1,
        inclusion s z = twistedTranslate C v x := by
  obtain ⟨v, hv⟩ := exists_bounded_translate C hx ht hR
  refine ⟨v, ?_⟩
  apply exists_unit_chart_of_bounded_position _ (by simpa using ht) hv
  simpa only [mem_openTorus_iff, time_twistedTranslate] using hx

end Wikipedia.HopfProblem.ToricSpace
