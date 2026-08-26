import ErdosProblems.Erdos633b.GroupTwoBoundedWeights

/-! Exact finite primitive phase enumeration for rational group-2 tilings. -/

namespace Erdos633b

def smallPrimitivePhases : Finset (ℕ × ℕ) :=
  {(7, 1), (8, 1), (9, 1), (10, 1), (11, 1),
  (12, 1), (13, 1), (13, 2), (14, 1), (15, 1),
  (15, 2), (16, 1), (18, 1), (20, 1), (20, 3),
  (21, 1), (21, 2), (22, 1), (22, 3), (24, 1),
  (26, 1), (26, 3), (28, 1), (28, 3), (30, 1),
  (36, 1), (36, 5), (42, 1), (42, 5)}

theorem smallPrimitivePhases_card : smallPrimitivePhases.card = 29 := by decide

theorem primitive_phase_order_7 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 7)
    (hs : 6 * j < 7) : (7, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_8 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 8)
    (hs : 6 * j < 8) : (8, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_9 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 9)
    (hs : 6 * j < 9) : (9, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_10 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 10)
    (hs : 6 * j < 10) : (10, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_11 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 11)
    (hs : 6 * j < 11) : (11, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_12 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 12)
    (hs : 6 * j < 12) : (12, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 1 := by omega
  interval_cases j
  · decide

theorem primitive_phase_order_13 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 13)
    (hs : 6 * j < 13) : (13, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 2 := by omega
  interval_cases j
  · decide
  · decide

theorem primitive_phase_order_14 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 14)
    (hs : 6 * j < 14) : (14, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 2 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_15 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 15)
    (hs : 6 * j < 15) : (15, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 2 := by omega
  interval_cases j
  · decide
  · decide

theorem primitive_phase_order_16 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 16)
    (hs : 6 * j < 16) : (16, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 2 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_18 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 18)
    (hs : 6 * j < 18) : (18, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 2 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_20 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 20)
    (hs : 6 * j < 20) : (20, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 3 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · decide

theorem primitive_phase_order_21 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 21)
    (hs : 6 * j < 21) : (21, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 3 := by omega
  interval_cases j
  · decide
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_22 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 22)
    (hs : 6 * j < 22) : (22, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 3 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · decide

theorem primitive_phase_order_24 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 24)
    (hs : 6 * j < 24) : (24, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 3 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_26 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 26)
    (hs : 6 * j < 26) : (26, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 4 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_28 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 28)
    (hs : 6 * j < 28) : (28, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 4 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · decide
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_30 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 30)
    (hs : 6 * j < 30) : (30, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 4 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc

theorem primitive_phase_order_36 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 36)
    (hs : 6 * j < 36) : (36, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 5 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc
  · decide

theorem primitive_phase_order_42 (j : ℕ) (hj : 0 < j) (hc : j.Coprime 42)
    (hs : 6 * j < 42) : (42, j) ∈ smallPrimitivePhases := by
  have hb : j ≤ 6 := by omega
  interval_cases j
  · decide
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc
  · norm_num [Nat.Coprime] at hc
  · decide
  · norm_num [Nat.Coprime] at hc

theorem mem_smallPrimitivePhases (D j : ℕ) (hD : 6 < D) (hφ : D.totient ≤ 12)
    (hj : 0 < j) (hc : j.Coprime D) (hs : 6 * j < D) : (D, j) ∈ smallPrimitivePhases := by
  have hm := mem_smallTotientOrders D hD hφ
  simp only [smallTotientOrders, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact primitive_phase_order_7 j hj hc hs
  · exact primitive_phase_order_8 j hj hc hs
  · exact primitive_phase_order_9 j hj hc hs
  · exact primitive_phase_order_10 j hj hc hs
  · exact primitive_phase_order_11 j hj hc hs
  · exact primitive_phase_order_12 j hj hc hs
  · exact primitive_phase_order_13 j hj hc hs
  · exact primitive_phase_order_14 j hj hc hs
  · exact primitive_phase_order_15 j hj hc hs
  · exact primitive_phase_order_16 j hj hc hs
  · exact primitive_phase_order_18 j hj hc hs
  · exact primitive_phase_order_20 j hj hc hs
  · exact primitive_phase_order_21 j hj hc hs
  · exact primitive_phase_order_22 j hj hc hs
  · exact primitive_phase_order_24 j hj hc hs
  · exact primitive_phase_order_26 j hj hc hs
  · exact primitive_phase_order_28 j hj hc hs
  · exact primitive_phase_order_30 j hj hc hs
  · exact primitive_phase_order_36 j hj hc hs
  · exact primitive_phase_order_42 j hj hc hs

namespace Tiling

theorem groupTwo_primitive_phase_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi)) (hs : GroupTwoShape d.tile T) :
    ∃ D j : ℕ, (D, j) ∈ smallPrimitivePhases ∧
      d.tile.angle 0 = 2 * Real.pi * j / D := by
  have hsmall : d.tile.angle 0 < Real.pi / 3 := by
    linarith [d.tile.angle_sum, d.tile.angle_pos 1, hs.1]
  obtain ⟨D, j, hD, hj, hc, hb, ha, hz⟩ :=
    d.tile.rational_small_angle_primitive_order hrat hsmall
  have hφ := d.groupTwo_order_totient_bound hs D (by omega) hz
  exact ⟨D, j, mem_smallPrimitivePhases D j hD hφ hj hc hb, ha⟩

end Tiling
end Erdos633b
