import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicUniformSubdivision

/-!
# Uniform logarithm control for bounded exponential generators

A sufficiently small uniform mesh puts every exponential prefix with a
bounded generator in the logarithm target. The statement holds for all
finer uniform partitions, not just the one chosen initially.
-/

open Set Metric

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.UniformTimePartition

private theorem norm_real_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (c : ℝ) (v : V) : ‖c • v‖ = |c| * ‖v‖ := by
  simpa only [Real.norm_eq_abs] using norm_smul c v

theorem exists_uniform_prefix_target_bound (n : ℕ) (B : ℝ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → ∀ K : SkewSpace n, ‖K‖ ≤ B →
      ∀ i : Fin (m + 1),
        ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ),
          ((u : ℝ) - time m i.castSucc) • K ∈ compatibleTarget n := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_compatibleTarget n).mem_nhds (zero_mem_compatibleTarget n))
  let D := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N, _, hN⟩ := exists_mesh_lt_above (r / D) (div_pos hr hD) 0
  refine ⟨N, ?_⟩
  intro m hm K hK i u hu
  have hden : (N : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hm 1
  have hmesh : 1 / ((m : ℝ) + 1) < r / D :=
    (one_div_le_one_div_of_le (by positivity) hden).trans_lt hN
  have hδ : 0 ≤ (u : ℝ) - time m i.castSucc := sub_nonneg.mpr hu.1
  have hstep : (u : ℝ) - time m i.castSucc ≤ 1 / ((m : ℝ) + 1) := by
    have h := dist_left_le_step m i hu
    change |(u : ℝ) - time m i.castSucc| ≤ _ at h
    rwa [abs_of_nonneg hδ] at h
  apply hball
  rw [Metric.mem_ball, dist_zero_right (((u : ℝ) - time m i.castSucc) • K),
    norm_real_smul (V := SkewSpace n), abs_of_nonneg hδ]
  calc
    ((u : ℝ) - time m i.castSucc) * ‖K‖ ≤ ((u : ℝ) - time m i.castSucc) * D :=
      mul_le_mul_of_nonneg_left (hK.trans (le_max_left _ _)) hδ
    _ ≤ (1 / ((m : ℝ) + 1)) * D := mul_le_mul_of_nonneg_right hstep hD.le
    _ < r := (lt_div_iff₀ hD).mp hmesh

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential
