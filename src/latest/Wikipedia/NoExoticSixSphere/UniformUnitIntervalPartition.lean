import Wikipedia.NoExoticSixSphere.UniformTimePartition
import Mathlib.Topology.UnitInterval

/-!
# Uniform partitions as actual unit-interval points
-/

open Set

namespace NoExoticSixSphere.UniformTimePartition

theorem time_mem_unitInterval (m : ℕ) (i : Fin (m + 2)) : time m i ∈ unitInterval := by
  constructor
  · simpa only [time_zero] using (strictMono_time m).monotone (Fin.zero_le i)
  · simpa only [time_last] using (strictMono_time m).monotone (Fin.le_last i)

noncomputable def unitTime (m : ℕ) (i : Fin (m + 2)) : unitInterval :=
  ⟨time m i, time_mem_unitInterval m i⟩

theorem unitTime_zero (m : ℕ) : unitTime m 0 = 0 := Subtype.ext (time_zero m)

theorem unitTime_last (m : ℕ) : unitTime m (Fin.last (m + 1)) = 1 :=
  Subtype.ext (time_last m)

theorem strictMono_unitTime (m : ℕ) : StrictMono (unitTime m) := strictMono_time m

theorem dist_left_le_step (m : ℕ) (i : Fin (m + 1)) {u : unitInterval}
    (hu : u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ)) :
    dist u (unitTime m i.castSucc) ≤ 1 / ((m : ℝ) + 1) := by
  change |(u : ℝ) - time m i.castSucc| ≤ _
  have hl : time m i.castSucc ≤ (u : ℝ) := hu.1
  have hr : (u : ℝ) ≤ time m i.succ := hu.2
  rw [abs_of_nonneg (sub_nonneg.mpr hl)]
  exact (sub_le_sub_right hr _).trans_eq (time_step m i)

theorem exists_mesh_lt_above (δ : ℝ) (hδ : 0 < δ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 1 / ((m : ℝ) + 1) < δ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / δ) (N : ℝ))
  have hNm : N ≤ m := by exact_mod_cast (le_max_right (1 / δ) (N : ℝ)).trans hm.le
  have hlarge : 1 < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp ((le_max_left _ _).trans_lt hm)
  refine ⟨m, hNm, (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr ?_⟩
  nlinarith

end NoExoticSixSphere.UniformTimePartition
