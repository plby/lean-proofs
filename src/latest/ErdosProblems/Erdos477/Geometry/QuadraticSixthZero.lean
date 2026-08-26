/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The zero linear remainder of an irreducible quadratic forces zero trace.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticSixthDegree

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K] [IsAlgClosed K]

lemma not_irreducible_scaled_quadratic (b : K[X]) (k : K) :
    ¬ Irreducible (X ^ 2 + C b * X + C (C k * b ^ 2) : K[X][X]) := by
  let p : K[X] := X ^ 2 + X + C k
  have hcoeff : p.coeff 2 ≠ 0 := by norm_num [p, coeff_add, coeff_X]
  have hdegree : p.degree ≠ 0 := by
    have h := le_natDegree_of_ne_zero hcoeff
    exact (natDegree_pos_iff_degree_pos.mp (by omega : 0 < p.natDegree)).ne'
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hdegree
  have hr' : r ^ 2 + r + k = 0 := by simpa [p, Polynomial.IsRoot] using hr
  have hk : k = -r - r ^ 2 := by linear_combination hr'
  let L : K[X][X] := X - C (C r * b)
  let M : K[X][X] := X - C (C (-1 - r) * b)
  have hfactor : (X ^ 2 + C b * X + C (C k * b ^ 2) : K[X][X]) = L * M := by
    rw [hk]
    simp only [L, M, map_sub, map_neg, map_mul, map_pow, map_one]
    ring
  intro h
  rcases h.isUnit_or_isUnit hfactor with hL | hM
  · exact not_isUnit_of_natDegree_pos L (by simp only [L, natDegree_X_sub_C]; decide) hL
  · exact not_isUnit_of_natDegree_pos M (by simp only [M, natDegree_X_sub_C]; decide) hM

theorem quadraticSixthLinear_ne_zero_of_irreducible [CharZero K] (b c : K[X])
    (hP : Irreducible (X ^ 2 + C b * X + C c : K[X][X]))
    (hb : b ≠ 0) : quadraticSixthLinear b c ≠ 0 := by
  intro hzero
  rcases (quadraticSixthLinear_eq_zero_iff b c).mp hzero with h | h | h
  · exact hb h
  · apply not_irreducible_scaled_quadratic b 1
    simpa only [map_one, one_mul, ← h] using hP
  · have hinv : C ((1 : K) / 3) * (3 : K[X]) = 1 := by
      rw [← C_ofNat 3, ← map_mul]
      norm_num
    have hc : c = C ((1 : K) / 3) * b ^ 2 := by
      calc
        c = (C ((1 : K) / 3) * 3) * c := by rw [hinv, one_mul]
        _ = C ((1 : K) / 3) * b ^ 2 := by rw [h]; ring
    apply not_irreducible_scaled_quadratic b ((1 : K) / 3)
    rwa [hc] at hP

theorem quadraticSixthLinear_zero_forces_zero_trace [CharZero K] (b c : K[X])
    (hP : Irreducible (X ^ 2 + C b * X + C c : K[X][X]))
    (hzero : quadraticSixthLinear b c = 0) : b = 0 := by
  by_contra hb
  exact quadraticSixthLinear_ne_zero_of_irreducible b c hP hb hzero

#print axioms quadraticSixthLinear_zero_forces_zero_trace
-- 'Erdos477.Geometry.quadraticSixthLinear_zero_forces_zero_trace' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
