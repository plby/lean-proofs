import ErdosProblems.Erdos547.FiniteRounding

/-!
# Finite bin assignments with several simultaneous load bounds
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F I J : Type*} [Fintype I] [Nonempty I] [Fintype J] [DecidableEq I]

open scoped Classical in
theorem exists_bin_assignment (S : Finset F) (p : F → I → ℝ) (u : F → J → ℝ)
    (hp : ∀ x i, 0 ≤ p x i) (hmass : ∀ x, ∑ i, p x i = 1)
    (L C : ℝ) (hC : 0 ≤ C)
    (hu : ∀ x ∈ S, ∀ j, 0 ≤ u x j ∧ u x j ≤ L)
    (hsmall : L * (∑ x ∈ S, ∑ j, u x j) < C ^ 2) :
    ∃ f : F → I, (∀ x ∈ S, 0 < p x (f x)) ∧
      ∀ i j, (∑ x ∈ S.filter (fun x ↦ f x = i), u x j) <
        (∑ x ∈ S, p x i * u x j) + C := by
  classical
  let a : F → I → (I × J) → ℝ := fun x i z ↦ if i = z.1 then u x z.2 else 0
  have hfirst (x : F) (z : I × J) : (∑ i, p x i * a x i z) = p x z.1 * u x z.2 := by
    simp [a, mul_ite]
  have hsecond (x : F) : (∑ z : I × J, ∑ i, p x i * (a x i z) ^ 2) =
      ∑ j, (u x j) ^ 2 := by
    calc
      _ = ∑ z : I × J, p x z.1 * (u x z.2) ^ 2 := by
        apply Finset.sum_congr rfl
        intro z _
        simp [a, apply_ite, mul_ite]
      _ = ∑ j, ∑ i, p x i * (u x j) ^ 2 := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = _ := by simp only [← Finset.sum_mul, hmass, one_mul]
  have hmoment : (∑ x ∈ S, ∑ z : I × J, ∑ i, p x i * (a x i z) ^ 2) < C ^ 2 := by
    apply lt_of_le_of_lt _ hsmall
    simp only [hsecond, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro j _
    obtain ⟨hzero, hupper⟩ := hu x hx j
    nlinarith only [hzero, hupper]
  obtain ⟨f, hf, hloads⟩ := exists_choices_load_lt S p a hp hmass C hC hmoment
  refine ⟨f, hf, ?_⟩
  intro i j
  calc
    (∑ x ∈ S.filter (fun x ↦ f x = i), u x j) = ∑ x ∈ S, a x (f x) (i, j) := by
      simp only [a, Finset.sum_filter]
    _ < (∑ x ∈ S, ∑ l, p x l * a x l (i, j)) + C := hloads (i, j)
    _ = _ := by simp only [hfirst]

end Erdos547

#print axioms Erdos547.exists_bin_assignment
