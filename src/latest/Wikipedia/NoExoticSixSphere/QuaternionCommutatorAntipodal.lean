import Wikipedia.NoExoticSixSphere.QuaternionCommutatorColumns

/-!
# Constraints on the antipodal fiber of the explicit commutator projection

The real part of the literal first matrix entry forces both quaternion
inputs to be minus one and the rotation to its midpoint. This is an
actual fiber calculation; regularity and the global degree comparison
are separate obligations.
-/

noncomputable section

open scoped Matrix unitInterval commutatorElement

namespace NoExoticSixSphere.QuaternionCommutatorAntipodal

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorRotation QuaternionCommutatorColumns

local notation "ℍ" => Quaternion ℝ

theorem unit_normSq (q : UnitQuaternions) : Quaternion.normSq q.val = 1 :=
  congrArg (fun x : ℍ ↦ x.re) (Unitary.mul_star_self_of_mem q.property)

theorem unit_re_bounds (q : UnitQuaternions) : -1 ≤ q.val.re ∧ q.val.re ≤ 1 := by
  have h := unit_normSq q
  rw [Quaternion.normSq_def'] at h
  have hs : q.val.re ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg q.val.imI, sq_nonneg q.val.imJ, sq_nonneg q.val.imK]
  constructor <;> nlinarith

theorem unit_eq_neg_one_of_re (q : UnitQuaternions) (h : q.val.re = -1) : q.val = -1 := by
  have hn : Quaternion.normSq (q.val + 1) = 0 := by
    rw [Quaternion.normSq_add, unit_normSq]
    norm_num [h]
  exact eq_neg_of_add_eq_zero_left (Quaternion.normSq_eq_zero.mp hn)

theorem antipodal_forces (q : UnitQuaternions) (g : SpTwo)
    (h : (⁅fiberInclusion q, g⁆).val 0 0 = -1) :
    q.val = -1 ∧ Quaternion.normSq (g.val 0 1) = 1 := by
  have he : 1 - Quaternion.normSq (g.val 0 1) * (1 - q.val.re) = -1 :=
    (commutator_top_real_reduced q g).symm.trans (congrArg (fun x : ℍ ↦ x.re) h)
  have hb₀ : 0 ≤ Quaternion.normSq (g.val 0 1) := Quaternion.normSq_nonneg
  have hb₁ : Quaternion.normSq (g.val 0 1) ≤ 1 := by
    linarith [row_normSq g, (Quaternion.normSq_nonneg (a := g.val 0 0))]
  have hle : Quaternion.normSq (g.val 0 1) * (1 - q.val.re) ≤
      Quaternion.normSq (g.val 0 1) * 2 :=
    mul_le_mul_of_nonneg_left (by linarith [(unit_re_bounds q).1]) hb₀
  have hb : Quaternion.normSq (g.val 0 1) = 1 := by linarith
  refine ⟨unit_eq_neg_one_of_re q ?_, hb⟩
  rw [hb, one_mul] at he
  linarith

theorem normSq_one_sub (r : ℍ) :
    Quaternion.normSq (1 - r) = 1 + Quaternion.normSq r - 2 * r.re := by
  simp [Quaternion.normSq_def', Quaternion.re_one, Quaternion.imI_one,
    Quaternion.imJ_one, Quaternion.imK_one]
  ring

theorem offDiagonal_normSq (c s : ℝ) (r : UnitQuaternions) :
    Quaternion.normSq (offDiagonal c s r.val) = (c * s) ^ 2 * (2 * (1 - r.val.re)) := by
  rw [offDiagonal, map_mul, Quaternion.normSq_coe, normSq_one_sub, unit_normSq]
  ring

theorem offDiagonal_unit_forces (c s : ℝ) (r : UnitQuaternions)
    (hs : c ^ 2 + s ^ 2 = 1) (h : Quaternion.normSq (offDiagonal c s r.val) = 1) :
    r.val = -1 ∧ c ^ 2 = 1 / 2 ∧ s ^ 2 = 1 / 2 := by
  rw [offDiagonal_normSq] at h
  have hs₂ : (c ^ 2 + s ^ 2) ^ 2 = 1 := by rw [hs]; norm_num
  have hp : (c * s) ^ 2 ≤ 1 / 4 := by nlinarith [sq_nonneg (c ^ 2 - s ^ 2)]
  have hle : (c * s) ^ 2 * (2 * (1 - r.val.re)) ≤ (c * s) ^ 2 * 4 :=
    mul_le_mul_of_nonneg_left (by linarith [(unit_re_bounds r).1]) (sq_nonneg (c * s))
  have hp₁ : (c * s) ^ 2 = 1 / 4 := by linarith
  have hr : r.val.re = -1 := by rw [hp₁] at h; linarith
  have hc : c ^ 2 = 1 / 2 := by nlinarith [sq_nonneg (c ^ 2 - s ^ 2)]
  exact ⟨unit_eq_neg_one_of_re r hr, hc, by linarith⟩

theorem midpoint_of_cos_sq (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2)
    (h : Real.cos θ ^ 2 = 1 / 2) : θ = Real.pi / 4 := by
  have hc : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ.2⟩
  have hc₀ : 0 ≤ Real.cos (Real.pi / 4) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hsq : Real.cos (Real.pi / 4) ^ 2 = 1 / 2 := by
    rw [Real.cos_pi_div_four]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  apply Real.injOn_cos ⟨hθ.1, by linarith [Real.pi_pos]⟩
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  nlinarith

theorem rotated_antipodal_forces (θ : ℝ) (q r : UnitQuaternions)
    (hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2)
    (h : (⁅fiberInclusion q, conjugatedFiber θ r⁆).val 0 0 = -1) :
    q.val = -1 ∧ r.val = -1 ∧ θ = Real.pi / 4 := by
  obtain ⟨hq, hb⟩ := antipodal_forces q (conjugatedFiber θ r) h
  rw [conjugatedFiber_matrix] at hb
  change Quaternion.normSq (offDiagonal (Real.cos θ) (Real.sin θ) r.val) = 1 at hb
  obtain ⟨hr, hc, _⟩ := offDiagonal_unit_forces (Real.cos θ) (Real.sin θ) r
    (Real.cos_sq_add_sin_sq θ) hb
  exact ⟨hq, hr, midpoint_of_cos_sq θ hθ hc⟩

end NoExoticSixSphere.QuaternionCommutatorAntipodal
