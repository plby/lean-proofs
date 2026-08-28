import Wikipedia.HomotopyGroupsOfSpheres.BalancedMinimumPolygonPartition

/-! # Every sufficiently fine partition supports the balanced minimum deformation -/

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon

open VertexSpace BalancedRealInvolutions ComplexSkewMatrices
open NoExoticSixSphere.UniformTimePartition

theorem exists_eventual_minimum_partition (n : ℕ) (E : ℝ) :
    ∃ lower : ℕ, ∀ m : ℕ, lower ≤ m →
      (∀ J : BalancedRealInvolutions.Space n, ∀ i : Fin (m + 1),
        ‖(time m i.succ - time m i.castSucc) • imaginaryDirection (minimumGenerator J)‖ <
          CompatibleLog.radius (Index n)) ∧
      ∀ C : ℝ, C ≤ max E ((4 * n : ℝ) * Real.pi ^ 2) →
        IsCompact (energySublevel specialIdentity (antipode n) (time m) C) := by
  let cap := max E ((4 * n : ℝ) * Real.pi ^ 2)
  let r := CompatibleLog.radius (Index n) / 2
  have hr : 0 < r := half_pos (CompatibleLog.radius_pos (N := Index n))
  have hrsmall : r < CompatibleLog.radius (Index n) :=
    half_lt_self (CompatibleLog.radius_pos (N := Index n))
  obtain ⟨lower, hlower⟩ := exists_nat_gt (cap / r ^ 2)
  refine ⟨lower, ?_⟩
  intro m hm
  have hmesh := small_energy_step_of_large cap hr m
    (hlower.trans_le (by exact_mod_cast hm))
  have hτ := strictMono_time m
  have hδpos (i : Fin (m + 1)) : 0 < time m i.succ - time m i.castSucc :=
    sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))
  have hQ : 0 ≤ (2 * n : ℝ) * Real.pi ^ 2 := by positivity
  have hQcap : (2 * n : ℝ) * Real.pi ^ 2 ≤ cap := by
    apply le_trans _ (le_max_right E ((4 * n : ℝ) * Real.pi ^ 2))
    nlinarith only [hQ]
  refine ⟨?_, ?_⟩
  · intro J i
    have hδone : time m i.succ - time m i.castSucc ≤ 1 := by
      have hl := hτ.monotone (Fin.zero_le i.castSucc)
      have hu := hτ.monotone (Fin.le_last i.succ)
      rw [time_zero] at hl
      rw [time_last] at hu
      linarith
    have hδsq : (time m i.succ - time m i.castSucc) ^ 2 ≤
        time m i.succ - time m i.castSucc := by nlinarith [hδpos i]
    have hs : ‖(time m i.succ - time m i.castSucc) •
        imaginaryDirection (minimumGenerator J)‖ ^ 2 =
        (time m i.succ - time m i.castSucc) ^ 2 * ((2 * n : ℝ) * Real.pi ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sq_minimumGenerator]
    have hbound : ‖(time m i.succ - time m i.castSucc) •
        imaginaryDirection (minimumGenerator J)‖ ^ 2 < r ^ 2 := by
      rw [hs]
      exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_right hδsq hQ).trans
        (by simpa only [mul_comm] using mul_le_mul_of_nonneg_right hQcap (hδpos i).le))
        (hmesh i)
    exact ((sq_lt_sq₀ (norm_nonneg _) hr.le).mp hbound).trans hrsmall
  · intro C hC
    apply isCompact_energySublevel specialIdentity (antipode n) (time m) hτ hr.le hrsmall
    intro i
    exact (mul_le_mul_of_nonneg_right hC (hδpos i).le).trans (hmesh i).le

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices.Polygon
