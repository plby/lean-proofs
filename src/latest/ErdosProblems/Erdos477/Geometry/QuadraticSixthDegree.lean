/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Degree bounds for the quadratic sixth-power remainder.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.QuadraticSixthReduction

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

lemma degree_quadraticSixthLinear (b c : K[X]) (hb : b.natDegree ≤ 1) (hc : c.natDegree ≤ 2) :
    (quadraticSixthLinear b c).natDegree ≤ 5 := by
  have hb2 : (b ^ 2).natDegree ≤ 2 := by simpa using natDegree_pow_le_of_le 2 hb
  have hc3 : ((3 : K[X]) * c).natDegree ≤ 2 := by
    simpa only [C_ofNat] using (natDegree_C_mul_le (3 : K) c).trans hc
  have hbc : (b ^ 2 - c).natDegree ≤ 2 := (natDegree_sub_le _ _).trans (max_le hb2 hc)
  have hbc3 : (b ^ 2 - 3 * c).natDegree ≤ 2 :=
    (natDegree_sub_le _ _).trans (max_le hb2 hc3)
  have hneg : (-b).natDegree ≤ 1 := by simpa only [natDegree_neg] using hb
  have hprod : (-b * (b ^ 2 - c)).natDegree ≤ 3 :=
    natDegree_mul_le.trans (Nat.add_le_add hneg hbc)
  exact natDegree_mul_le.trans (Nat.add_le_add hprod hbc3)

lemma degree_quadraticSixthConstant (b c : K[X]) (hb : b.natDegree ≤ 1)
    (hc : c.natDegree ≤ 2) : (quadraticSixthConstant b c).natDegree ≤ 6 := by
  have hb2 : (b ^ 2).natDegree ≤ 2 := by simpa using natDegree_pow_le_of_le 2 hb
  have hb4 : (b ^ 4).natDegree ≤ 4 := by simpa using natDegree_pow_le_of_le 4 hb
  have hc2 : (c ^ 2).natDegree ≤ 4 := by simpa using natDegree_pow_le_of_le 2 hc
  have hc3 : (c ^ 3).natDegree ≤ 6 := by simpa using natDegree_pow_le_of_le 3 hc
  have hleft : (-b ^ 4 * c).natDegree ≤ 6 :=
    natDegree_mul_le.trans (Nat.add_le_add (by simpa only [natDegree_neg] using hb4) hc)
  have hmid0 : ((3 : K[X]) * b ^ 2).natDegree ≤ 2 := by
    simpa only [C_ofNat] using (natDegree_C_mul_le (3 : K) (b ^ 2)).trans hb2
  have hmid : (3 * b ^ 2 * c ^ 2).natDegree ≤ 6 :=
    natDegree_mul_le.trans (Nat.add_le_add hmid0 hc2)
  exact (natDegree_sub_le _ _).trans
    (max_le ((natDegree_add_le _ _).trans (max_le hleft hmid)) hc3)

#print axioms degree_quadraticSixthConstant
-- 'Erdos477.Geometry.degree_quadraticSixthConstant' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
