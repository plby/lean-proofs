import Wikipedia.HopfProblem.CuspHoneycombHexagonPolygon
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Convex geometry and the actual frontier of the hexagonal cell

The explicit hexagon is a compact convex neighborhood of the origin.
Its topological frontier is exactly the union of its six named closed
sides, with strict supporting inequalities characterizing the interior.
These facts permit the radial boundary-extension construction to be
applied to the genuine polygon.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

theorem sideFunctional_continuous (k : Fin 6) : Continuous (sideFunctional k) := by
  fin_cases k <;> unfold sideFunctional <;> fun_prop

theorem sideFunctional_add (k : Fin 6) (x y : Plane) :
    sideFunctional k (x + y) = sideFunctional k x + sideFunctional k y := by
  fin_cases k <;> simp [sideFunctional] <;> ring

theorem sideFunctional_smul (k : Fin 6) (a : ℝ) (x : Plane) :
    sideFunctional k (a • x) = a * sideFunctional k x := by
  fin_cases k <;> simp [sideFunctional] <;> ring

theorem mem_hexagon_iff_sideFunctional_le (x : Plane) :
    x ∈ Hexagon ↔ ∀ k : Fin 6, sideFunctional k x ≤ 1 := by
  constructor
  · rintro ⟨hx, hy, hxy⟩ k
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    have hxy' := abs_le.mp hxy
    fin_cases k
    · exact hx'.2
    · exact hxy'.2
    · exact hy'.2
    · change -x 0 ≤ 1
      linarith [hx'.1]
    · change -x 0 - x 1 ≤ 1
      linarith [hxy'.1]
    · change -x 1 ≤ 1
      linarith [hy'.1]
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    simp only [sideFunctional_zero, sideFunctional_one, sideFunctional_two,
      sideFunctional_three, sideFunctional_four, sideFunctional_five] at h0 h1 h2 h3 h4 h5
    exact ⟨abs_le.mpr ⟨by linarith, h0⟩, abs_le.mpr ⟨by linarith, h2⟩,
      abs_le.mpr ⟨by linarith, h1⟩⟩

theorem hexagon_convex : Convex ℝ Hexagon := by
  intro x hx y hy a b ha hb hab
  apply (mem_hexagon_iff_sideFunctional_le _).mpr
  intro k
  rw [sideFunctional_add, sideFunctional_smul, sideFunctional_smul]
  calc
    a * sideFunctional k x + b * sideFunctional k y ≤ a * 1 + b * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le x).mp hx k) ha)
        (mul_le_mul_of_nonneg_left ((mem_hexagon_iff_sideFunctional_le y).mp hy k) hb)
    _ = 1 := by simpa only [mul_one] using hab

theorem hexagon_isClosed : IsClosed Hexagon := by
  have he : Hexagon = ⋂ k : Fin 6, {x | sideFunctional k x ≤ 1} := by
    ext x
    simp only [mem_iInter, mem_ofPred_eq, mem_hexagon_iff_sideFunctional_le]
  rw [he]
  exact isClosed_iInter fun k => isClosed_le (sideFunctional_continuous k) continuous_const

theorem hexagon_subset_closedBall : Hexagon ⊆ Metric.closedBall (0 : Plane) 1 := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)).mpr
  intro i
  fin_cases i
  · exact hx.1
  · exact hx.2.1

theorem hexagon_isCompact : IsCompact Hexagon :=
  (isCompact_closedBall (0 : Plane) 1).of_isClosed_subset hexagon_isClosed
    hexagon_subset_closedBall

theorem hexagon_isBounded : Bornology.IsBounded Hexagon := hexagon_isCompact.isBounded

theorem ball_half_subset_hexagon : Metric.ball (0 : Plane) (1 / 2) ⊆ Hexagon := by
  intro x hx
  have hn : ‖x‖ < 1 / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
  have h0 : |x 0| ≤ ‖x‖ := norm_le_pi_norm x 0
  have h1 : |x 1| ≤ ‖x‖ := norm_le_pi_norm x 1
  have hsum := abs_add_le (x 0) (x 1)
  exact ⟨by linarith, by linarith, by linarith⟩

theorem hexagon_mem_nhds_zero : Hexagon ∈ 𝓝 (0 : Plane) :=
  Filter.mem_of_superset (Metric.ball_mem_nhds _ (by norm_num)) ball_half_subset_hexagon

theorem zero_mem_interior_hexagon : (0 : Plane) ∈ interior Hexagon :=
  mem_interior_iff_mem_nhds.mpr hexagon_mem_nhds_zero

theorem hexagon_interior_nonempty : (interior Hexagon).Nonempty :=
  ⟨0, zero_mem_interior_hexagon⟩

theorem mem_interior_hexagon_iff (x : Plane) :
    x ∈ interior Hexagon ↔ ∀ k : Fin 6, sideFunctional k x < 1 := by
  constructor
  · intro hx k
    have hle := (mem_hexagon_iff_sideFunctional_le x).mp (interior_subset hx) k
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior Hexagon) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior Hexagon := by
      simpa only [mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior Hexagon := hball (by
      change dist (1 + δ / 2) (1 : ℝ) < δ
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ)
    have hb := (mem_hexagon_iff_sideFunctional_le _).mp (interior_subset ha) k
    rw [sideFunctional_smul, heq, mul_one] at hb
    linarith
  · intro hx
    let U : Set Plane := ⋂ k : Fin 6, {y | sideFunctional k y < 1}
    have hU : IsOpen U := isOpen_iInter_of_finite fun k =>
      isOpen_lt (sideFunctional_continuous k) continuous_const
    have hxU : x ∈ U := mem_iInter.mpr hx
    have hUK : U ⊆ Hexagon := by
      intro y hy
      apply (mem_hexagon_iff_sideFunctional_le y).mpr
      intro k
      exact (mem_iInter.mp hy k).le
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hU.mem_nhds hxU) hUK)

/-- The named polygon sides are precisely the actual topological frontier. -/
theorem frontier_hexagon : frontier Hexagon = ⋃ k : Fin 6, side k := by
  ext x
  rw [frontier, hexagon_isClosed.closure_eq, mem_sdiff, mem_interior_hexagon_iff, mem_iUnion]
  constructor
  · rintro ⟨hx, hn⟩
    push Not at hn
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, hx, le_antisymm ((mem_hexagon_iff_sideFunctional_le x).mp hx k) hk⟩
  · rintro ⟨k, hx, hk⟩
    exact ⟨hx, fun h => (h k).ne hk⟩

end Wikipedia.HopfProblem.CuspHoneycombHexagon
