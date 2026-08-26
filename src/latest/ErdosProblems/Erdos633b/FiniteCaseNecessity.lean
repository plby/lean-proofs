import ErdosProblems.Erdos633b.FiniteCaseTransports

/-! Every one of the 52 actual finite angle pairs has an eight-case outer triangle. -/

namespace Erdos633b.Tiling

theorem finite_angle_pair_necessary {T : Triangle} {n : ℕ} (d : Tiling T n)
    (p : (ℕ × ℕ × ℕ) × ℕ × ℕ) (hp : p ∈ finiteOuterCandidates)
    (hw : ∀ i, d.tile.angle i = (angleTableWeights p.1 i : ℝ) * (Real.pi / p.1.1))
    (ha : ∀ i, T.angle i =
      (angleTableWeights (p.1.1, p.2.1, p.2.2) i : ℝ) * (Real.pi / p.1.1)) : EightCases T := by
  simp only [finiteOuterCandidates, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact False.elim (d.finite_pair_01_impossible hw ha)
  · exact False.elim (d.finite_pair_02_impossible hw ha)
  · refine ⟨Equiv.swap 1 2, Or.inr (Or.inr (Or.inl ?_))⟩
    change T.angle 0 = Real.pi / 6 ∧ T.angle 2 = Real.pi / 2 ∧ T.angle 1 = Real.pi / 3
    have h0 := ha 0
    have h1 := ha 1
    norm_num [angleTableWeights] at h0 h1
    exact ⟨by linarith, by linarith [T.angle_sum], by linarith⟩
  · exact False.elim (d.finite_boundary_04_impossible hw ha)
  · exact False.elim (d.finite_boundary_05_impossible hw ha)
  · exact False.elim (d.finite_boundary_06_impossible hw ha)
  · exact False.elim (d.finite_pair_07_impossible hw ha)
  · exact False.elim (d.finite_pair_08_impossible hw ha)
  · exact False.elim (d.finite_pair_09_impossible hw ha)
  · exact False.elim (d.finite_pair_10_impossible hw ha)
  · exact False.elim (d.finite_pair_11_impossible hw ha)
  · exact False.elim (d.finite_pair_12_impossible hw ha)
  · exact False.elim (d.finite_boundary_13_impossible hw ha)
  · exact False.elim (d.finite_boundary_14_impossible hw ha)
  · exact False.elim (d.finite_boundary_15_impossible hw ha)
  · exact False.elim (d.finite_boundary_16_impossible hw ha)
  · exact False.elim (d.finite_boundary_17_impossible hw ha)
  · exact False.elim (d.finite_boundary_18_impossible hw ha)
  · exact False.elim (d.finite_boundary_19_impossible hw ha)
  · exact False.elim (d.finite_boundary_20_impossible hw ha)
  · exact False.elim (d.finite_boundary_21_impossible hw ha)
  · exact False.elim (d.finite_boundary_22_impossible hw ha)
  · exact False.elim (d.finite_boundary_23_impossible hw ha)
  · exact False.elim (d.finite_boundary_24_impossible hw ha)
  · exact False.elim (d.finite_boundary_25_impossible hw ha)
  · exact False.elim (d.finite_boundary_26_impossible hw ha)
  · exact False.elim (d.finite_boundary_27_impossible hw ha)
  · exact False.elim (d.finite_boundary_28_impossible hw ha)
  · exact False.elim (d.finite_boundary_29_impossible hw ha)
  · exact False.elim (d.finite_boundary_30_impossible hw ha)
  · exact False.elim (d.finite_boundary_31_impossible hw ha)
  · exact False.elim (d.finite_boundary_32_impossible hw ha)
  · exact False.elim (d.finite_boundary_33_impossible hw ha)
  · exact False.elim (d.finite_pair_34_impossible hw ha)
  · exact False.elim (d.finite_boundary_35_impossible hw ha)
  · exact False.elim (d.finite_boundary_36_impossible hw ha)
  · exact False.elim (d.finite_boundary_37_impossible hw ha)
  · exact False.elim (d.finite_boundary_38_impossible hw ha)
  · exact False.elim (d.finite_boundary_39_impossible hw ha)
  · exact False.elim (d.finite_pair_40_impossible hw ha)
  · exact False.elim (d.finite_pair_41_impossible hw ha)
  · exact False.elim (d.finite_boundary_42_impossible hw ha)
  · exact False.elim (d.finite_boundary_43_impossible hw ha)
  · exact False.elim (d.finite_boundary_44_impossible hw ha)
  · exact False.elim (d.finite_boundary_45_impossible hw ha)
  · exact False.elim (d.finite_boundary_46_impossible hw ha)
  · exact False.elim (d.finite_boundary_47_impossible hw ha)
  · exact False.elim (d.finite_boundary_48_impossible hw ha)
  · exact False.elim (d.finite_boundary_49_impossible hw ha)
  · exact False.elim (d.finite_boundary_50_impossible hw ha)
  · exact False.elim (d.finite_boundary_51_impossible hw ha)
  · exact False.elim (d.finite_boundary_52_impossible hw ha)

end Erdos633b.Tiling
