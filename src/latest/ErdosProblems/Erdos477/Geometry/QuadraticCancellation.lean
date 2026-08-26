/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Quadratic parametrizations of a diagonal sextic have a cancelling coordinate pair.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticWronskian
import ErdosProblems.Erdos477.Geometry.WronskianDependence
import ErdosProblems.Erdos477.Geometry.SixthRelations

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- A base-point-free identity between four sixth powers of degree-two
polynomials has a cancelling pair among its first three coordinates. -/
theorem quadratic_sixth_pair_cancellation (f : Fin 4 → K[X])
    (hf : ∀ i, (f i).natDegree = 2)
    (hroot : ∀ x : K, ∃ i, (f i).eval x ≠ 0)
    (hsum : f 0 ^ 6 + f 1 ^ 6 + f 2 ^ 6 + f 3 ^ 6 = 0) :
    f 0 ^ 6 + f 1 ^ 6 = 0 ∨ f 0 ^ 6 + f 2 ^ 6 = 0 ∨ f 1 ^ 6 + f 2 ^ 6 = 0 := by
  have hf0 (i) : f i ≠ 0 := by intro h; have hi := hf i; simp [h] at hi
  have hfpos (i) : 0 < (f i).natDegree := by rw [hf]; decide
  have hnone (x) (h0 : (f 0).eval x = 0) (h1 : (f 1).eval x = 0)
      (h2 : (f 2).eval x = 0) (h3 : (f 3).eval x = 0) : False := by
    obtain ⟨i, hi⟩ := hroot x
    fin_cases i
    · exact hi h0
    · exact hi h1
    · exact hi h2
    · exact hi h3
  obtain ⟨a, b, c, hnonzero, hrel⟩ := exists_relation_of_wronskianThree_eq_zero
    (f 0 ^ 6) (f 1 ^ 6) (f 2 ^ 6) (quadratic_sixth_wronskian_eq_zero f hf hroot hsum)
  have hsingle (i : Fin 4) (a : K) (ha : a ≠ 0) : C a * f i ^ 6 ≠ 0 :=
    mul_ne_zero (C_ne_zero.mpr ha) (pow_ne_zero 6 (hf0 i))
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      have hc : c ≠ 0 := by simpa [ha, hb] using hnonzero
      exact hsingle 2 c hc (by simpa [ha, hb] using hrel)
    have hc : c ≠ 0 := by
      intro hc
      exact hsingle 1 b hb (by simpa [ha, hc] using hrel)
    have hrel' : C b * f 1 ^ 6 + C c * f 2 ^ 6 = 0 := by simpa [ha] using hrel
    have hsum' : f 1 ^ 6 + f 2 ^ 6 + f 0 ^ 6 + f 3 ^ 6 = 0 := by linear_combination hsum
    exact Or.inr (Or.inr (pair_sixth_relation_cancels (f 1) (f 2) (f 0) (f 3)
      (hfpos 1) (hf0 0) (hf0 3)
      (fun x h1 h2 h0 h3 => hnone x h0 h1 h2 h3) hsum' b c hb hc hrel'))
  by_cases hb : b = 0
  · have hc : c ≠ 0 := by
      intro hc
      exact hsingle 0 a ha (by simpa [hb, hc] using hrel)
    have hrel' : C a * f 0 ^ 6 + C c * f 2 ^ 6 = 0 := by simpa [hb] using hrel
    have hsum' : f 0 ^ 6 + f 2 ^ 6 + f 1 ^ 6 + f 3 ^ 6 = 0 := by linear_combination hsum
    exact Or.inr (Or.inl (pair_sixth_relation_cancels (f 0) (f 2) (f 1) (f 3)
      (hfpos 0) (hf0 1) (hf0 3)
      (fun x h0 h2 h1 h3 => hnone x h0 h1 h2 h3) hsum' a c ha hc hrel'))
  by_cases hc : c = 0
  · have hrel' : C a * f 0 ^ 6 + C b * f 1 ^ 6 = 0 := by simpa [hc] using hrel
    exact Or.inl (pair_sixth_relation_cancels (f 0) (f 1) (f 2) (f 3)
      (hfpos 0) (hf0 2) (hf0 3) hnone hsum a b ha hb hrel')
  have hconstant := weighted_triple_sixth_degree_zero (f 0) (f 1) (f 2) (f 3)
    (hf0 0) (hf0 1) (hf0 2) hnone hsum a b c ha hb hc hrel
  rw [hf 0] at hconstant
  exact (by omega : False).elim

#print axioms quadratic_sixth_pair_cancellation
-- 'Erdos477.Geometry.quadratic_sixth_pair_cancellation' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
