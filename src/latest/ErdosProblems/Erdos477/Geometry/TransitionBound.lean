/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Bounding points lost when factors of one auxiliary equation do not persist in the next.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneFactors

namespace Erdos477.Geometry

open scoped BigOperators

variable {K : Type*} [Field K] [Infinite K]

/-- Pairwise relatively prime components of a parent equation that do not
divide the child equation contribute at most the product of the two degrees. -/
theorem card_component_drop_le (P Q : MvPolynomial (Fin 2) K) (hP : P ≠ 0)
    (C : Finset (MvPolynomial (Fin 2) K)) (hirr : ∀ F ∈ C, Irreducible F)
    (hpair : (↑C : Set (MvPolynomial (Fin 2) K)).Pairwise IsRelPrime)
    (hdiv : ∀ F ∈ C, F ∣ P) (hnot : ∀ F ∈ C, ¬ F ∣ Q)
    (S : Finset (K × K))
    (hS : ∀ z ∈ S, MvPolynomial.eval ![z.1, z.2] Q = 0 ∧
      ∃ F ∈ C, MvPolynomial.eval ![z.1, z.2] F = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  let U : MvPolynomial (Fin 2) K → Finset (K × K) := fun F =>
    S.filter (fun z => MvPolynomial.eval ![z.1, z.2] F = 0)
  have hcover : S ⊆ C.biUnion U := by
    intro z hz
    obtain ⟨F, hF, hzero⟩ := (hS z hz).2
    exact Finset.mem_biUnion.mpr ⟨F, hF, Finset.mem_filter.mpr ⟨hz, hzero⟩⟩
  have hbound (F) (hF : F ∈ C) : (U F).card ≤ F.totalDegree * Q.totalDegree := by
    apply card_common_zeroes_le F Q (hirr F hF) (hnot F hF)
    intro z hz
    have hmem := Finset.mem_filter.mp hz
    exact ⟨hmem.2, (hS z hmem.1).1⟩
  have hdegrees := sum_degrees_le_of_pairwise_dvd C
    (fun F hF => (hirr F hF).ne_zero) hpair P hP hdiv
  calc
    S.card ≤ (C.biUnion U).card := Finset.card_le_card hcover
    _ ≤ ∑ F ∈ C, (U F).card := Finset.card_biUnion_le
    _ ≤ ∑ F ∈ C, F.totalDegree * Q.totalDegree := Finset.sum_le_sum hbound
    _ = (∑ F ∈ C, F.totalDegree) * Q.totalDegree := (Finset.sum_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hdegrees

#print axioms card_component_drop_le
-- 'Erdos477.Geometry.card_component_drop_le' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
