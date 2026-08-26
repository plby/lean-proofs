import ErdosProblems.Erdos633b.GroupOneFirstOrders
import ErdosProblems.Erdos633b.ThirtiethOrderBoundary

/-! Complete exact elimination of the first group-1 rational-angle
orders, leaving only the three outer shapes already in the classification. -/

namespace Erdos633b

theorem quarterThird_possible_pairs (D j : ℕ) (hD : D ∈ quarterThirdExceptions)
    (hj : 0 < j) (hc : j.Coprime D) (hs : 6 * j < D) :
    (D = 8 ∧ j = 1) ∨ (D = 9 ∧ j = 1) ∨ (D = 12 ∧ j = 1) ∨
    (D = 14 ∧ j = 1) ∨ (D = 20 ∧ j = 1) ∨ (D = 20 ∧ j = 3) ∨
    (D = 21 ∧ j = 1) ∨ (D = 21 ∧ j = 2) ∨ (D = 30 ∧ j = 1) := by
  simp only [quarterThirdExceptions, Finset.mem_insert, Finset.mem_singleton] at hD
  rcases hD with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals have hb : j ≤ 4 := by omega
  all_goals interval_cases j <;> first | omega | norm_num at hc

namespace Tiling

theorem groupOne_first_commensurable_angle_cases {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hrat : ∀ i, IsRational (d.tile.angle i / Real.pi))
    (h0 : T.angle 0 = d.tile.angle 0) (h1 : T.angle 1 = 2 * d.tile.angle 0)
    (h2 : T.angle 2 = 2 * d.tile.angle 1) :
    d.tile.angle 0 = Real.pi / 4 ∨ d.tile.angle 0 = Real.pi / 6 ∨
      d.tile.angle 0 = Real.pi / 7 := by
  obtain ⟨D, hD, j, hj, hc, hs, ha⟩ := d.groupOne_first_primitive_order hrat h0 h1 h2
  have hpairs := quarterThird_possible_pairs D j hD hj hc hs
  rcases hpairs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    norm_num only [Nat.cast_ofNat, mul_one] at ha
    linarith
  · exfalso
    apply d.groupOne_first_parameter_not_large_degree h0 h1 h2 36 7
      (by decide) (by decide) (by decide)
    rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    norm_num
    ring
  · right; left
    norm_num only [Nat.cast_ofNat, mul_one] at ha
    linarith
  · right; right
    norm_num only [Nat.cast_ofNat, mul_one] at ha
    linarith
  · exfalso
    apply d.groupOne_first_parameter_not_large_degree h0 h1 h2 40 9
      (by decide) (by decide) (by decide)
    rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    norm_num
    ring
  · exfalso
    apply d.groupOne_first_parameter_not_large_degree h0 h1 h2 40 7
      (by decide) (by decide) (by decide)
    rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    norm_num
    ring
  · exfalso
    apply d.groupOne_first_parameter_not_large_degree h0 h1 h2 84 19
      (by decide) (by decide) (by decide)
    rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    norm_num
    ring
  · exfalso
    apply d.groupOne_first_parameter_not_large_degree h0 h1 h2 84 17
      (by decide) (by decide) (by decide)
    rw [ha, ← Real.cos_pi_div_two_sub]
    congr 2
    norm_num
    ring
  · exfalso
    apply d.groupOne_first_not_thirtieth h0 h1 h2
    simpa using ha

end Tiling
end Erdos633b
