import Wikipedia.NoExoticSixSphere.UniformUnitIntervalPartition

/-!
# Equal subdivision of every uniform partition interval

There are `l + 1` fine intervals inside each coarse interval. The parent
index is integer division, so each closed fine cell, including its endpoints,
lies in the claimed coarse cell.
-/

namespace NoExoticSixSphere.UniformTimePartition

def refinedCount (m l : ℕ) : ℕ := m + (m + 1) * l

theorem refinedCount_add_one (m l : ℕ) : refinedCount m l + 1 = (m + 1) * (l + 1) := by
  unfold refinedCount
  ring

theorem le_refinedCount (m l : ℕ) : l ≤ refinedCount m l := by
  have h := Nat.mul_le_mul_right l (Nat.succ_pos m)
  simp only [Nat.one_mul] at h
  exact h.trans (Nat.le_add_left _ _)

def parentIndex (m l : ℕ) (j : Fin (refinedCount m l + 1)) : Fin (m + 1) :=
  ⟨j.val / (l + 1), (Nat.div_lt_iff_lt_mul (Nat.succ_pos l)).mpr (by
    simpa only [refinedCount_add_one] using j.isLt)⟩

theorem parentIndex_left (m l : ℕ) (j : Fin (refinedCount m l + 1)) :
    time m (parentIndex m l j).castSucc ≤ time (refinedCount m l) j.castSucc := by
  have hnat : (parentIndex m l j).val * (l + 1) ≤ j.val := Nat.div_mul_le_self _ _
  have hden : (refinedCount m l : ℝ) + 1 = ((m : ℝ) + 1) * ((l : ℝ) + 1) := by
    exact_mod_cast refinedCount_add_one m l
  simp only [time, Fin.val_castSucc]
  rw [hden, div_le_div_iff₀ (by positivity) (by positivity)]
  have hreal : ((parentIndex m l j).val : ℝ) * ((l : ℝ) + 1) ≤ (j.val : ℝ) := by
    exact_mod_cast hnat
  nlinarith

theorem parentIndex_right (m l : ℕ) (j : Fin (refinedCount m l + 1)) :
    time (refinedCount m l) j.succ ≤ time m (parentIndex m l j).succ := by
  have hnat : j.val + 1 ≤ ((parentIndex m l j).val + 1) * (l + 1) := by
    have h := Nat.mod_lt j.val (Nat.succ_pos l)
    have he := Nat.mod_add_div j.val (l + 1)
    change j.val + 1 ≤ (j.val / (l + 1) + 1) * (l + 1)
    nlinarith
  have hden : (refinedCount m l : ℝ) + 1 = ((m : ℝ) + 1) * ((l : ℝ) + 1) := by
    exact_mod_cast refinedCount_add_one m l
  simp only [time, Fin.val_succ, Nat.cast_add, Nat.cast_one]
  rw [hden, div_le_div_iff₀ (by positivity) (by positivity)]
  have hreal : (j.val : ℝ) + 1 ≤ (((parentIndex m l j).val : ℝ) + 1) * ((l : ℝ) + 1) := by
    exact_mod_cast hnat
  nlinarith

theorem refined_step_ratio (m l : ℕ) (j : Fin (refinedCount m l + 1))
    (i : Fin (m + 1)) :
    (time (refinedCount m l) j.succ - time (refinedCount m l) j.castSucc) /
      (time m i.succ - time m i.castSucc) = 1 / ((l : ℝ) + 1) := by
  rw [time_step, time_step]
  have hden : (refinedCount m l : ℝ) + 1 = ((m : ℝ) + 1) * ((l : ℝ) + 1) := by
    exact_mod_cast refinedCount_add_one m l
  rw [hden]
  field_simp

end NoExoticSixSphere.UniformTimePartition
