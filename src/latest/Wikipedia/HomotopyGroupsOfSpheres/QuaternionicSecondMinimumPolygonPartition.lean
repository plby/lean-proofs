import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondMinimumPolygonRetraction

/-!
# Uniform partitions supporting the second minimum-locus retraction

One sufficiently fine uniform partition gives compact energy sublevels below
a prescribed bound and short generators for every minimum rotation. It may
be chosen beyond any prescribed number of vertices.
-/

noncomputable section

open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon

open ComplexStructures NoExoticSixSphere.UniformTimePartition

private theorem real_norm_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : ℝ) (v : V) : ‖r • v‖ = |r| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]

private theorem real_lt_of_mul_lt {x y z : ℝ} (hz : 0 < z) (h : x * z < y * z) : x < y := by
  nlinarith only [hz, h]

theorem minimumSpeed_step_norm_lt {n : ℕ} {a : ComplexStructures.Space n}
    (P : AnticommutingStructures.Space a) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : δ * Real.pi < ShortLog.radius n) :
    ‖δ • (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ <
      ShortLog.radius n := by
  rw [real_norm_smul (V := SkewSpace n), abs_of_nonneg hδ,
    real_norm_smul (V := SkewSpace n), abs_of_pos Real.pi_pos]
  calc
    δ * (Real.pi * ‖(AnticommutingStructures.generatorParameter P).val.val‖) ≤
        δ * (Real.pi * 1) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (ComplexStructures.norm_le_one (AnticommutingStructures.generatorParameter P).val)
          Real.pi_pos.le) hδ
    _ = δ * Real.pi := by rw [mul_one]
    _ < _ := hsmall

theorem exists_eventual_minimum_partition (n : ℕ) (B : ℝ) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      (∀ a b : ComplexStructures.Space n, ∀ C : ℝ, C ≤ B →
        IsCompact (energySublevel a b (time m) C)) ∧
      (∀ a : ComplexStructures.Space n, ∀ P : AnticommutingStructures.Space a,
        ∀ i : Fin (m + 1), ‖(time m i.succ - time m i.castSucc) •
          (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ <
            ShortLog.radius n) := by
  let r := ShortLog.radius n
  let E := max B (2 * Real.pi * r)
  have hr : 0 < r := ShortLog.radius_pos n
  have hrhalf : 0 < r / 2 := half_pos hr
  obtain ⟨N, hN⟩ := exists_nat_gt (E / (r / 2) ^ 2)
  refine ⟨N, ?_⟩
  intro m hNm
  have hm := small_energy_step_of_large E hrhalf m
    (hN.trans_le (by exact_mod_cast hNm))
  have hτ := strictMono_time m
  have hδ (i : Fin (m + 1)) : 0 < time m i.succ - time m i.castSucc :=
    sub_pos.mpr (hτ (show i.castSucc < i.succ by simp))
  have hstep (i : Fin (m + 1)) : (time m i.succ - time m i.castSucc) * Real.pi < r := by
    have hprod : 2 * Real.pi * r * (time m i.succ - time m i.castSucc) ≤
        E * (time m i.succ - time m i.castSucc) :=
      mul_le_mul_of_nonneg_right (le_max_right B _) (hδ i).le
    have hbound : ((time m i.succ - time m i.castSucc) * Real.pi) * (2 * r) < (r / 2) ^ 2 := by
      nlinarith only [hprod, hm i]
    exact real_lt_of_mul_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
      (hbound.trans (by nlinarith only [sq_pos_of_pos hr]))
  refine ⟨?_, ?_⟩
  · intro a b C hC
    have hmesh (i : Fin (m + 1)) : C * (time m i.succ - time m i.castSucc) ≤ (r / 2) ^ 2 :=
      (mul_le_mul_of_nonneg_right (hC.trans (le_max_left B _)) (hδ i).le).trans (hm i).le
    exact isCompact_energySublevel a b (time m) hτ hrhalf.le (half_lt_self hr) hmesh
  · intro a P i
    exact minimumSpeed_step_norm_lt P (hδ i).le (hstep i)

theorem exists_minimum_partition (n : ℕ) (B : ℝ) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      (∀ a b : ComplexStructures.Space n, ∀ C : ℝ, C ≤ B →
        IsCompact (energySublevel a b (time m) C)) ∧
      (∀ a : ComplexStructures.Space n, ∀ P : AnticommutingStructures.Space a,
        ∀ i : Fin (m + 1), ‖(time m i.succ - time m i.castSucc) •
          (Real.pi • (AnticommutingStructures.generatorParameter P).val.val)‖ <
            ShortLog.radius n) := by
  obtain ⟨N₀, hN₀⟩ := exists_eventual_minimum_partition n B
  exact ⟨max N N₀, le_max_left _ _, hN₀ _ (le_max_right _ _)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructurePolygon
