/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Affine linear substitutions do not increase total polynomial degree.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

variable {σ τ R : Type*} [CommSemiring R]

lemma totalDegree_linear_substitution (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial σ R) :
    (MvPolynomial.eval₂Hom MvPolynomial.C g P).totalDegree ≤ P.totalDegree := by
  classical
  let φ := MvPolynomial.eval₂Hom MvPolynomial.C g
  have hmap : φ P = ∑ m ∈ P.support, φ (MvPolynomial.monomial m (P.coeff m)) := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
  change (φ P).totalDegree ≤ P.totalDegree
  rw [hmap]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  simp only [φ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial]
  have hprod : (m.prod (fun i e => g i ^ e)).totalDegree ≤ m.sum (fun _ e => e) := by
    dsimp only [Finsupp.prod, Finsupp.sum]
    apply (MvPolynomial.totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (MvPolynomial.totalDegree_pow _ _).trans
    simpa only [mul_one] using Nat.mul_le_mul_left (m i) (hg i)
  have hmul := MvPolynomial.totalDegree_mul (MvPolynomial.C (P.coeff m))
    (m.prod (fun i e => g i ^ e))
  simp only [MvPolynomial.totalDegree_C, zero_add] at hmul
  exact hmul.trans (hprod.trans (MvPolynomial.le_totalDegree hm))

#print axioms totalDegree_linear_substitution
-- 'Erdos477.Geometry.totalDegree_linear_substitution' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
