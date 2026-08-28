import Wikipedia.HopfProblem.EllipticDiscPower
import Wikipedia.HopfProblem.ThreefoldFundamentalGroupGluingTopologyBase
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Topology of the source disc for a small elliptic filling

The inverse image of a disc of radius `r` under the `m`th power map is the
literal norm-power sublevel set in the unit disc.  For `0 < m` and
`0 < r < 1`, flattening its subtypes identifies it with the complex ball
of radius `r ^ (m : ℝ)⁻¹`.  This proves contractibility of the full disc and
path connectedness after removing the center.
-/

noncomputable section

open Set Topology Metric

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity

/-- The actual inverse image of a small disc under the power map. -/
def powerDisc (m : ℕ) (r : ℝ) : TopologicalSpace.Opens Disc :=
  ⟨{z | ‖(z : ℂ)‖ ^ m < r},
    isOpen_lt (continuous_subtype_val.norm.pow m) continuous_const⟩

@[simp] theorem mem_powerDisc (m : ℕ) (r : ℝ) (z : Disc) :
    z ∈ powerDisc m r ↔ ‖(z : ℂ)‖ ^ m < r := Iff.rfl

theorem powerDisc_norm_pow_lt (m : ℕ) (r : ℝ) (z : powerDisc m r) :
    ‖((z : Disc) : ℂ)‖ ^ m < r := z.property

theorem zero_mem_powerDisc (m : ℕ) (r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    Elliptic.discZero ∈ powerDisc m r := by
  simpa only [mem_powerDisc, Elliptic.discZero_coe, norm_zero,
    zero_pow hm.ne'] using hr

/-- The positive real radius of the power-sublevel disc. -/
def powerDiscRadius (m : ℕ) (r : ℝ) : ℝ := r ^ (m : ℝ)⁻¹

theorem powerDiscRadius_pos (m : ℕ) (r : ℝ) (hr : 0 < r) :
    0 < powerDiscRadius m r := Real.rpow_pos_of_pos hr _

theorem powerDiscRadius_pow (m : ℕ) (r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    powerDiscRadius m r ^ m = r :=
  Real.rpow_inv_natCast_pow hr.le hm.ne'

theorem powerDiscRadius_lt_one (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) : powerDiscRadius m r < 1 :=
  Real.rpow_lt_one hr.le hr1 (inv_pos.mpr (Nat.cast_pos.mpr hm))

theorem norm_pow_lt_iff_norm_lt_powerDiscRadius (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (z : ℂ) :
    ‖z‖ ^ m < r ↔ ‖z‖ < powerDiscRadius m r := by
  calc
    ‖z‖ ^ m < r ↔ ‖z‖ ^ m < powerDiscRadius m r ^ m := by
      rw [powerDiscRadius_pow m r hm hr]
    _ ↔ ‖z‖ < powerDiscRadius m r :=
      pow_lt_pow_iff_left₀ (norm_nonneg z) (powerDiscRadius_pos m r hr).le hm.ne'

/-- The power-sublevel disc is the ordinary ball, with the same underlying point. -/
def powerDiscBallHomeomorph (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) :
    powerDisc m r ≃ₜ Metric.ball (0 : ℂ) (powerDiscRadius m r) where
  toFun z := ⟨((z : Disc) : ℂ), by
    simpa only [Metric.mem_ball, dist_zero_right] using
      (norm_pow_lt_iff_norm_lt_powerDiscRadius m r hm hr _).mp z.property⟩
  invFun z := ⟨⟨z, by
    change (z : ℂ) ∈ Metric.ball (0 : ℂ) 1
    simpa only [Metric.mem_ball, dist_zero_right] using
      (show ‖(z : ℂ)‖ < powerDiscRadius m r by
      simpa only [Metric.mem_ball, dist_zero_right] using z.property).trans
        (powerDiscRadius_lt_one m r hm hr hr1)⟩, by
    apply (norm_pow_lt_iff_norm_lt_powerDiscRadius m r hm hr _).mpr
    simpa only [Metric.mem_ball, dist_zero_right] using z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem powerDiscBallHomeomorph_apply_coe (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1) (z : powerDisc m r) :
    (powerDiscBallHomeomorph m r hm hr hr1 z : ℂ) = ((z : Disc) : ℂ) := rfl

@[simp] theorem powerDiscBallHomeomorph_symm_apply_coe_coe (m : ℕ) (r : ℝ)
    (hm : 0 < m) (hr : 0 < r) (hr1 : r < 1)
    (z : Metric.ball (0 : ℂ) (powerDiscRadius m r)) :
    (((powerDiscBallHomeomorph m r hm hr hr1).symm z : Disc) : ℂ) = z := rfl

/-- The full source disc of a small elliptic filling is contractible. -/
theorem powerDisc_contractibleSpace (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) : ContractibleSpace (powerDisc m r) := by
  apply (powerDiscBallHomeomorph m r hm hr hr1).contractibleSpace_iff.mpr
  exact (convex_ball (0 : ℂ) (powerDiscRadius m r)).contractibleSpace
    ⟨0, Metric.mem_ball_self (powerDiscRadius_pos m r hr)⟩

/-- The full source disc is simply connected in its literal inherited topology. -/
theorem powerDisc_simplyConnectedSpace (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) : SimplyConnectedSpace (powerDisc m r) := by
  let := powerDisc_contractibleSpace m r hm hr hr1
  exact SimplyConnectedSpace.ofContractible _

/-- Flattening the punctured source disc gives the entire punctured complex ball. -/
theorem powerDisc_punctured_image (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) :
    (fun z : powerDisc m r => ((z : Disc) : ℂ)) ''
      {z : powerDisc m r | ((z : Disc) : ℂ) ≠ 0} =
        Metric.ball (0 : ℂ) (powerDiscRadius m r) \ {0} := by
  let e := powerDiscBallHomeomorph m r hm hr hr1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(e w).property, hw⟩
  · rintro ⟨hz, hne⟩
    refine ⟨e.symm ⟨z, hz⟩, ?_, rfl⟩
    exact hne

/-- Removing the center leaves a nonempty path-connected source disc. -/
theorem powerDisc_punctured_isPathConnected (m : ℕ) (r : ℝ) (hm : 0 < m)
    (hr : 0 < r) (hr1 : r < 1) :
    IsPathConnected {z : powerDisc m r | ((z : Disc) : ℂ) ≠ 0} := by
  have h : IsInducing (fun z : powerDisc m r => ((z : Disc) : ℂ)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  apply h.isPathConnected_iff.mpr
  rw [powerDisc_punctured_image m r hm hr hr1]
  exact Threefold.punctured_complex_ball_isPathConnected (powerDiscRadius_pos m r hr)

end Wikipedia.HopfProblem.SpecialPeriods.EllipticAttachingSurjectivity
