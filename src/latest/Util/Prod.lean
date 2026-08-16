import Mathlib

/-! # Finite product estimates -/

namespace Finset

/-- A finite product of factors in `[0, 1]` loses at most the sum of their defects. -/
theorem one_sub_sum_le_prod_one_sub
    {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hf0 : ∀ i ∈ s, 0 ≤ f i) (hf1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hfa0 := hf0 a (by simp)
      have hfa1 := hf1 a (by simp)
      have ih' :=
        ih (fun i hi ↦ hf0 i (by simp [hi]))
          (fun i hi ↦ hf1 i (by simp [hi]))
      calc
        1 - (f a + ∑ i ∈ s, f i) ≤
            (1 - f a) * (1 - ∑ i ∈ s, f i) := by
              have hsum0 : 0 ≤ ∑ i ∈ s, f i :=
                Finset.sum_nonneg fun i hi ↦ hf0 i (by simp [hi])
              nlinarith
        _ ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) :=
          mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hfa1)

end Finset
