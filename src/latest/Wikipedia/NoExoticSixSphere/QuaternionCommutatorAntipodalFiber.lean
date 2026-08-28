import Wikipedia.NoExoticSixSphere.QuaternionCommutatorAntipodal

/-!
# The unique antipodal fiber of the actual commutator projection

On the product of the interval and the two quaternionic spheres, the
first-column map takes the south pole exactly at the midpoint and the
two inputs minus one. The calculation concerns the original matrix
map. It does not assert local regularity or a degree theorem.
-/

noncomputable section

open scoped Matrix unitInterval commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorAntipodal

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorRotation QuaternionCommutatorColumns

local notation "ℍ" => Quaternion ℝ

def antipode : BaseSphere :=
  ⟨WithLp.toLp 2 (-1, 0), (mem_baseSphere_iff _).mpr (by simp)⟩

def midpoint : I := ⟨1 / 2, by norm_num⟩

theorem projection_eq_antipode_iff (g : SpTwo) :
    projection g = antipode ↔ g.val 0 0 = -1 := by
  constructor
  · exact fun h ↦ congrArg (fun v : BaseSphere ↦ v.val.fst) h
  · intro h
    have hn := column_normSq g 0
    rw [h, Quaternion.normSq_neg, map_one] at hn
    have hz : g.val 1 0 = 0 := Quaternion.normSq_eq_zero.mp (by linarith)
    apply Subtype.ext
    apply (WithLp.equiv 2 (ℍ × ℍ)).injective
    exact Prod.ext h hz

theorem commutator_top_of_neg_and_unit (q : UnitQuaternions) (g : SpTwo)
    (hq : q.val = -1) (hg : Quaternion.normSq (g.val 0 1) = 1) :
    (⁅fiberInclusion q, g⁆).val 0 0 = -1 := by
  have ha : Quaternion.normSq (g.val 0 0) = 0 := by linarith [row_normSq g]
  rw [commutator_top, hq]
  simp only [star_neg, star_one, mul_neg, mul_one, neg_mul, Quaternion.self_mul_star]
  rw [ha, hg, Quaternion.coe_zero, Quaternion.coe_one, zero_add]

theorem midpoint_offDiagonal_norm (r : UnitQuaternions) (hr : r.val = -1) :
    Quaternion.normSq ((conjugatedFiber (Real.pi / 4) r).val 0 1) = 1 := by
  rw [conjugatedFiber_matrix]
  change Quaternion.normSq (offDiagonal (Real.cos (Real.pi / 4))
    (Real.sin (Real.pi / 4)) r.val) = 1
  have hc : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hs : Real.sin (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.sin_pi_div_four, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [offDiagonal_normSq, mul_pow, hc, hs, hr]
  norm_num [Quaternion.re_one]

theorem projection_contraction_midpoint (q r : UnitQuaternions)
    (hq : q.val = -1) (hr : r.val = -1) : projection (contraction midpoint q r) = antipode := by
  apply (projection_eq_antipode_iff _).mpr
  change (⁅fiberInclusion q, conjugatedFiber ((1 / 2) * (Real.pi / 2)) r⁆).val 0 0 = -1
  rw [show (1 / 2 : ℝ) * (Real.pi / 2) = Real.pi / 4 by ring]
  exact commutator_top_of_neg_and_unit q _ hq (midpoint_offDiagonal_norm r hr)

theorem contraction_antipode_iff (t : I) (q r : UnitQuaternions) :
    projection (contraction t q r) = antipode ↔ t = midpoint ∧ q = -1 ∧ r = -1 := by
  constructor
  · intro h
    have hh := (projection_eq_antipode_iff (contraction t q r)).mp h
    have ht : 0 ≤ t.val * (Real.pi / 2) ∧ t.val * (Real.pi / 2) ≤ Real.pi / 2 := by
      constructor <;> nlinarith [t.property.1, t.property.2, Real.pi_pos]
    obtain ⟨hq, hr, hθ⟩ := rotated_antipodal_forces _ q r ht hh
    refine ⟨?_, Subtype.ext hq, Subtype.ext hr⟩
    apply Subtype.ext
    change t.val = 1 / 2
    nlinarith [Real.pi_pos]
  · rintro ⟨rfl, rfl, rfl⟩
    exact projection_contraction_midpoint _ _ rfl rfl

end NoExoticSixSphere.QuaternionCommutatorAntipodal
