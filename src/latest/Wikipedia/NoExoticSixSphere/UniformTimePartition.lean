import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Basic

/-!
# Uniform finite partitions with a prescribed energy mesh bound

For any real energy bound and any positive logarithmic radius, a uniform
partition of the unit interval makes energy times each time step smaller
than the squared radius.
-/

namespace NoExoticSixSphere.UniformTimePartition

noncomputable def time (m : ℕ) (j : Fin (m + 2)) : ℝ := (j : ℕ) / ((m : ℝ) + 1)

theorem time_zero (m : ℕ) : time m 0 = 0 := by simp [time]

theorem time_last (m : ℕ) : time m (Fin.last (m + 1)) = 1 := by
  simp only [time, Fin.val_last, Nat.cast_add, Nat.cast_one]
  exact div_self (by positivity)

theorem strictMono_time (m : ℕ) : StrictMono (time m) := by
  intro i j hij
  apply div_lt_div_of_pos_right _ (by positivity : 0 < (m : ℝ) + 1)
  exact_mod_cast hij

theorem time_step (m : ℕ) (i : Fin (m + 1)) :
    time m i.succ - time m i.castSucc = 1 / ((m : ℝ) + 1) := by
  simp only [time, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem small_energy_step_of_large (E : ℝ) {r : ℝ} (hr : 0 < r)
    (m : ℕ) (hm : E / r ^ 2 < m) (i : Fin (m + 1)) :
    E * (time m i.succ - time m i.castSucc) < r ^ 2 := by
  have hsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hlarge : E < ((m : ℝ) + 1) * r ^ 2 := by
    have h := (div_lt_iff₀ hsq).mp hm
    nlinarith
  rw [time_step, mul_one_div]
  apply (div_lt_iff₀ (by positivity : 0 < (m : ℝ) + 1)).mpr
  simpa only [mul_comm] using hlarge

theorem exists_small_energy_steps (E : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ m : ℕ, ∀ i : Fin (m + 1), E * (time m i.succ - time m i.castSucc) < r ^ 2 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (E / r ^ 2)
  exact ⟨m, small_energy_step_of_large E hr m hm⟩

theorem exists_small_energy_steps_above (E : ℝ) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧
      ∀ i : Fin (m + 1), E * (time m i.succ - time m i.castSucc) < r ^ 2 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (E / r ^ 2) (N : ℝ))
  have hNm : N ≤ m := by exact_mod_cast (le_max_right (E / r ^ 2) (N : ℝ)).trans hm.le
  exact ⟨m, hNm, small_energy_step_of_large E hr m ((le_max_left _ _).trans_lt hm)⟩

end NoExoticSixSphere.UniformTimePartition
