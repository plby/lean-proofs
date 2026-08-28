import Wikipedia.HopfProblem.CuspHoneycombTilingTopology
import Mathlib.Topology.Algebra.Module.Basic

/-!
# The explicit radial gauge of the literal central honeycomb cell

The maximum of the three defining absolute-value expressions measures radial
position in the actual dual hexagon. Its unit sublevel set, strict unit sublevel
set, and unit level set are respectively the cell, its interior, and its frontier.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

open CuspHoneycombTiling

/-- The explicit gauge of the literal central dual hexagon. -/
def cellGauge (x : Plane) : ℝ :=
  max |2 * x 0 + x 1| (max |x 0 - x 1| |x 0 + 2 * x 1|)

theorem cellGauge_continuous : Continuous cellGauge :=
  (((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)).abs).max
    (((continuous_apply 0).sub (continuous_apply 1)).abs.max
      ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).abs)

theorem cellGauge_nonneg (x : Plane) : 0 ≤ cellGauge x :=
  (abs_nonneg _).trans (le_max_left _ _)

@[simp] theorem cellGauge_zero : cellGauge (0 : Plane) = 0 := by
  simp [cellGauge]

theorem cellGauge_smul (c : ℝ) (x : Plane) :
    cellGauge (c • x) = |c| * cellGauge x := by
  have h0 : 2 * (c * x 0) + c * x 1 = c * (2 * x 0 + x 1) := by ring
  have h1 : c * x 0 - c * x 1 = c * (x 0 - x 1) := by ring
  have h2 : c * x 0 + 2 * (c * x 1) = c * (x 0 + 2 * x 1) := by ring
  simp only [cellGauge, Pi.smul_apply, smul_eq_mul, h0, h1, h2, abs_mul,
    mul_max_of_nonneg _ _ (abs_nonneg c)]

theorem cellGauge_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c) (x : Plane) :
    cellGauge (c • x) = c * cellGauge x := by
  rw [cellGauge_smul, abs_of_nonneg hc]

@[simp] theorem cellGauge_eq_zero_iff (x : Plane) : cellGauge x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h0 : |2 * x 0 + x 1| ≤ 0 :=
      (le_max_left _ _).trans (le_of_eq hx)
    have h1 : |x 0 - x 1| ≤ 0 :=
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_of_eq hx))
    have h0' : 2 * x 0 + x 1 = 0 :=
      abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    have h1' : x 0 - x 1 = 0 :=
      abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    funext i
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
  · rintro rfl
    exact cellGauge_zero

theorem cellGauge_pos_iff (x : Plane) : 0 < cellGauge x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    simp only [hzero, cellGauge_zero, lt_self_iff_false] at hx
  · intro hx
    apply lt_of_le_of_ne (cellGauge_nonneg x)
    intro h
    exact hx ((cellGauge_eq_zero_iff x).mp h.symm)

theorem mem_baseCell_iff (x : Plane) : x ∈ baseCell ↔ cellGauge x ≤ 1 := by
  simp only [CuspHoneycombTiling.mem_baseCell, cellGauge, max_le_iff]

theorem mem_interior_baseCell_iff (x : Plane) :
    x ∈ interior baseCell ↔ cellGauge x < 1 := by
  constructor
  · intro hx
    have hle := (mem_baseCell_iff x).mp (interior_subset hx)
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior baseCell) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior baseCell := by
      simpa only [mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior baseCell := hball (by
      change dist (1 + δ / 2) (1 : ℝ) < δ
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ)
    have hb := (mem_baseCell_iff _).mp (interior_subset ha)
    rw [cellGauge_smul_of_nonneg _ (by linarith), heq, mul_one] at hb
    linarith
  · intro hx
    have hopen : IsOpen {y : Plane | cellGauge y < 1} :=
      isOpen_lt cellGauge_continuous continuous_const
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hopen.mem_nhds hx)
    intro y hy
    exact (mem_baseCell_iff y).mpr hy.le

theorem mem_frontier_baseCell_iff (x : Plane) :
    x ∈ frontier baseCell ↔ cellGauge x = 1 := by
  rw [frontier, baseCell_isClosed.closure_eq, mem_sdiff,
    mem_baseCell_iff, mem_interior_baseCell_iff, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

end Wikipedia.HopfProblem.CuspCentralHomology.Radial
