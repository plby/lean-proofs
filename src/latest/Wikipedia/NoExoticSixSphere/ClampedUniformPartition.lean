import Wikipedia.NoExoticSixSphere.UniformUnitIntervalPartition

/-!
# An eventually constant extension of a uniform finite partition

This connects the strictly increasing finite partition to the natural-indexed
interface of the existing broken-path replacement. The constant tail has only
identity increments.
-/

open Set

namespace NoExoticSixSphere.UniformTimePartition

noncomputable def clampedTime (m k : ℕ) : unitInterval :=
  unitTime m ⟨min k (m + 1), by have := Nat.min_le_right k (m + 1); omega⟩

theorem clampedTime_of_fin (m : ℕ) (i : Fin (m + 2)) :
    clampedTime m i.val = unitTime m i := by
  unfold clampedTime
  congr 1
  apply Fin.ext
  exact min_eq_left (by have := i.isLt; omega)

theorem clampedTime_zero (m : ℕ) : clampedTime m 0 = 0 :=
  (clampedTime_of_fin m 0).trans (unitTime_zero m)

theorem clampedTime_after (m k : ℕ) (hk : m + 1 ≤ k) : clampedTime m k = 1 := by
  have hi : (⟨min k (m + 1), by have := Nat.min_le_right k (m + 1); omega⟩ : Fin (m + 2)) =
      Fin.last (m + 1) := Fin.ext (min_eq_right hk)
  exact (congrArg (unitTime m) hi).trans (unitTime_last m)

theorem monotone_clampedTime (m : ℕ) : Monotone (clampedTime m) := by
  intro j k hjk
  apply (strictMono_unitTime m).monotone
  change min j (m + 1) ≤ min k (m + 1)
  exact min_le_min_right _ hjk

theorem clampedTime_left (m : ℕ) (i : Fin (m + 1)) :
    clampedTime m i.val = unitTime m i.castSucc := clampedTime_of_fin m i.castSucc

theorem clampedTime_right (m : ℕ) (i : Fin (m + 1)) :
    clampedTime m (i.val + 1) = unitTime m i.succ := clampedTime_of_fin m i.succ

theorem clamped_increment_control {X G : Type*} [Group G]
    (F : unitInterval × X → G) (m : ℕ) (U : Set G) (hU : 1 ∈ U)
    (hfinite : ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (F (unitTime m i.castSucc, x))⁻¹ * F (u, x) ∈ U) :
    ∀ k : ℕ, ∀ u ∈ Icc (clampedTime m k) (clampedTime m (k + 1)), ∀ x,
      (F (clampedTime m k, x))⁻¹ * F (u, x) ∈ U := by
  intro k u hu x
  by_cases hk : k < m + 1
  · let i : Fin (m + 1) := ⟨k, hk⟩
    have hl : clampedTime m k = unitTime m i.castSucc := clampedTime_left m i
    have hr : clampedTime m (k + 1) = unitTime m i.succ := clampedTime_right m i
    rw [hl, hr] at hu
    rw [hl]
    exact hfinite i u hu x
  · have hk' : m + 1 ≤ k := Nat.le_of_not_gt hk
    have he : u = 1 := le_antisymm le_top (by simpa only [clampedTime_after m k hk'] using hu.1)
    rw [clampedTime_after m k hk', he, inv_mul_cancel]
    exact hU

end NoExoticSixSphere.UniformTimePartition
