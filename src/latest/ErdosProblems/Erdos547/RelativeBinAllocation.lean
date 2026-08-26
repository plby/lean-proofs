import ErdosProblems.Erdos547.WeightedBinAllocation

/-!
# Absorbing the finite rounding error into relative bin capacity
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F I J : Type*} [Fintype F] [Fintype I] [Nonempty I] [Fintype J] [DecidableEq I]

open scoped Classical in
theorem exists_relative_bin_assignment (allowed : F → Finset I)
    (w : I → ℝ) (u : F → J → ℝ) (A L C θ : ℝ) (capacity margin : J → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hA : 0 < A) (hC : 0 ≤ C)
    (hallowed : ∀ x, A ≤ ∑ i ∈ allowed x, w i)
    (hweight : ∀ x i, i ∈ allowed x → θ ≤ w i)
    (hu : ∀ x j, 0 ≤ u x j ∧ u x j ≤ L)
    (hsmall : L * (∑ x, ∑ j, u x j) < C ^ 2)
    (hcapacity : ∀ j, 0 ≤ capacity j) (hmargin : ∀ j, 0 ≤ margin j)
    (hmean : ∀ j, (∑ x, u x j) / A + margin j ≤ capacity j)
    (herror : ∀ j, C ≤ θ * margin j) :
    ∃ f : F → I, (∀ x, f x ∈ allowed x) ∧
      ∀ i j, (∑ x ∈ (Finset.univ : Finset F).filter (fun x ↦ f x = i), u x j) ≤
        capacity j * w i := by
  classical
  obtain ⟨f, hf, hload⟩ := exists_weighted_bin_assignment allowed w u A L C
    hw hA hC hallowed hu hsmall
  refine ⟨f, hf, ?_⟩
  intro i j
  by_cases hused : ∃ x, f x = i
  · obtain ⟨x, hx⟩ := hused
    have hθ : θ ≤ w i := hx ▸ hweight x (f x) (hf x)
    have herr : C ≤ w i * margin j :=
      (herror j).trans (mul_le_mul_of_nonneg_right hθ (hmargin j))
    have hmain := mul_le_mul_of_nonneg_left (hmean j) (hw i)
    have he : w i * ((∑ x, u x j) / A + margin j) =
        w i / A * (∑ x, u x j) + w i * margin j := by ring
    rw [he] at hmain
    have hh := hload i j
    nlinarith only [hh, herr, hmain]
  · have he : (Finset.univ : Finset F).filter (fun x ↦ f x = i) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hused ⟨x, (Finset.mem_filter.mp hx).2⟩
    rw [he, Finset.sum_empty]
    exact mul_nonneg (hcapacity j) (hw i)

end Erdos547

#print axioms Erdos547.exists_relative_bin_assignment
