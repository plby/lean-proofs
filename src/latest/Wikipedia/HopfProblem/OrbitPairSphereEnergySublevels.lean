import Wikipedia.HopfProblem.OrbitPairSpherePolygonSublevels
import Wikipedia.NoExoticSixSphere.UniformTimePartition

/-!
# Admissible sphere energy sublevels and uniform partition control

The admissible sublevel is the actual nonantipodal domain intersected with
the literal energy bound. The checked mesh estimate identifies it with the
compact full-space sublevel. Arbitrarily fine uniform partitions supply
this control simultaneously for every endpoint pair and every smaller cap.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy

open NoExoticSixSphere SphereVertexSpace

variable {n m : ℕ}

def energySublevel (a b : Sphere n) (τ : Fin (m + 2) → ℝ) (E : ℝ) : Set (Space n m) :=
  {v | v ∈ admissible (costDomain n) a b m ∧ energy a b τ v ≤ E}

theorem energySublevel_eq_full_of_mesh (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (E : ℝ)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    energySublevel a b τ E = {v : Space n m | energy a b τ v ≤ E} :=
  admissible_inter_sublevel a b τ hτ E hmesh

theorem isCompact_energySublevel (a b : Sphere n) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (E : ℝ)
    (hmesh : ∀ i : Fin (m + 1), E * (τ i.succ - τ i.castSucc) < Real.pi ^ 2) :
    IsCompact (energySublevel a b τ E) := by
  rw [energySublevel_eq_full_of_mesh a b τ hτ E hmesh]
  exact isCompact_sublevel a b τ E

theorem exists_compact_sublevels_partition (n : ℕ) (E : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      (∀ i : Fin (m + 1), E * (UniformTimePartition.time m i.succ -
        UniformTimePartition.time m i.castSucc) < Real.pi ^ 2) ∧
      ∀ a b : Sphere n, ∀ C : ℝ, C ≤ E →
        IsCompact (energySublevel a b (UniformTimePartition.time m) C) ∧
        {v : Space n m | energy a b (UniformTimePartition.time m) v ≤ C} ⊆
          admissible (costDomain n) a b m := by
  obtain ⟨m, hNm, hm⟩ := UniformTimePartition.exists_small_energy_steps_above E Real.pi_pos N
  refine ⟨m, hNm, hm, fun a b C hC => ?_⟩
  have hτ := UniformTimePartition.strictMono_time m
  have hmesh (i : Fin (m + 1)) : C * (UniformTimePartition.time m i.succ -
      UniformTimePartition.time m i.castSucc) < Real.pi ^ 2 :=
    (mul_le_mul_of_nonneg_right hC
      (sub_nonneg.mpr (hτ (show i.castSucc < i.succ by simp)).le)).trans_lt (hm i)
  exact ⟨isCompact_energySublevel a b _ hτ C hmesh,
    sublevel_subset_admissible a b _ hτ C hmesh⟩

end Wikipedia.HopfProblem.OrbitPair.SpherePolygonEnergy
