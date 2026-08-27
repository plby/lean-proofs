import ErdosProblems.Erdos587.HooleyBoxMass

/-! # A proper linear hyperplane saves an entire coordinate width -/

open scoped BigOperators

namespace Erdos587.CFP

theorem delta_hyperplane_card_bound {ι : Type*} [Fintype ι]
    (A : Finset (ι → ℤ)) (R : ι → ℕ) (a : ι → ℝ) (j : ι) (haj : a j ≠ 0)
    (hbox : ∀ v ∈ A, ∀ i, (v i).natAbs ≤ R i)
    (hplane : ∀ v ∈ A, (∑ i, a i * (v i : ℝ)) = 0) :
    (2 * R j + 1) * A.card ≤ ∏ i, (2 * R i + 1) := by
  classical
  let J := {i : ι // i ≠ j}
  let q : (ι → ℤ) → J → ℤ := fun v i => v i
  have hinj : Set.InjOn q (A : Set (ι → ℤ)) := by
    intro v hv w hw heq
    have hsum : (∑ i, a i * ((v i : ℝ) - (w i : ℝ))) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hplane v hv, hplane w hw, sub_self]
    have hsingle : (∑ i, a i * ((v i : ℝ) - (w i : ℝ))) =
        a j * ((v j : ℝ) - (w j : ℝ)) := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        have hi : v i = w i := congrFun heq ⟨i, hij⟩
        rw [hi, sub_self, mul_zero]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [hsingle] at hsum
    have hjR : (v j : ℝ) = (w j : ℝ) := sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left haj)
    have hjZ : v j = w j := by exact_mod_cast hjR
    funext i
    by_cases hij : i = j
    · simpa only [hij] using hjZ
    · exact congrFun heq ⟨i, hij⟩
  have hsmall := delta_card_le_integer_box (A.image q) (fun i : J => R i) (by
    intro v hv i
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact hbox w hw i)
  rw [Finset.card_image_of_injOn hinj] at hsmall
  calc
    _ ≤ (2 * R j + 1) * ∏ i : J, (2 * R i + 1) := Nat.mul_le_mul_left _ hsmall
    _ = ∏ i, (2 * R i + 1) :=
      (Fintype.prod_eq_mul_prod_subtype_ne (fun i => 2 * R i + 1) j).symm

end Erdos587.CFP
