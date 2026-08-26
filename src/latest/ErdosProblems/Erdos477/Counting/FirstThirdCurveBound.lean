/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The plane-curve estimate applied to the first and third sextic coordinates.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.BoundedDegreeCurves
import ErdosProblems.Erdos477.IntegerDiagonal

namespace Erdos477.Counting

variable {K : Type*} [Field K] [CharZero K]

theorem exists_first_third_curve_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℤ, ∀ B : ℝ, 1 ≤ B →
      ∀ P : MvPolynomial (Fin 2) K, Irreducible P → 3 ≤ P.totalDegree →
      P.totalDegree ≤ N → ∀ S : Finset (Fin 3 → ℤ),
      (∀ z ∈ S, IntegerDiagonalPoint c z) →
      (∀ z ∈ S, MvPolynomial.eval ![(z 0 : K), (z 2 : K)] P = 0) →
      (∀ z ∈ S, ∀ i, |(z i : ℝ)| ≤ B) →
      (S.card : ℝ) ≤ C * B ^ ((1 : ℝ) / 3 + ε) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_high_degree_cylinder_bound (K := K) N ε hε
  refine ⟨C, hC, ?_⟩
  intro c B hB P hP hdegree hN S hS hroot hheight
  have h := hbound c B hB P hP hdegree hN (S.image swapPositiveCoordinates) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    change 0 ≤ z 1 ∧ z 1 ^ 6 + z 0 ^ 6 - z 2 ^ 6 = c
    exact ⟨(hS z hz).2.1, by rw [add_comm]; exact (hS z hz).2.2.2⟩) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact hroot z hz) (by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    exact height_swapPositiveCoordinates z B (hheight z hz))
  rwa [Finset.card_image_of_injective _ swapPositiveCoordinates_injective] at h

#print axioms exists_first_third_curve_bound
-- 'Erdos477.Counting.exists_first_third_curve_bound' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
