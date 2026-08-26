/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Absolute irreducibility of the affine diagonal sextic, by Eisenstein at a smooth point.
Formal author: Codex.
-/

import Mathlib

namespace Erdos477.Geometry

variable {σ K : Type*} [Field K]

lemma eval_pderiv_eq_zero_of_mem_ker_sq (x : σ → K) (i : σ)
    (P : MvPolynomial σ K) (hP : P ∈ RingHom.ker (MvPolynomial.eval x) ^ 2) :
    MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0 := by
  rw [pow_two] at hP
  refine Submodule.mul_induction_on hP ?_ ?_
  · intro a ha b hb
    have ha0 := RingHom.mem_ker.mp ha
    have hb0 := RingHom.mem_ker.mp hb
    simp only [MvPolynomial.pderiv_mul, map_add, map_mul, ha0, hb0, mul_zero, zero_mul,
      add_zero]
  · intro a b ha hb
    simp only [map_add, ha, hb, add_zero]

/-- A simple zero of the coefficient polynomial supplies an Eisenstein ideal. -/
theorem irreducible_X_pow_sub_of_simple_zero (g : MvPolynomial σ K)
    (x : σ → K) (hg : MvPolynomial.eval x g = 0) (i : σ)
    (hderiv : MvPolynomial.eval x (MvPolynomial.pderiv i g) ≠ 0)
    (n : ℕ) (hn : 0 < n) : Irreducible (Polynomial.X ^ n - Polynomial.C g) := by
  let I := RingHom.ker (MvPolynomial.eval x)
  have hprime : I.IsPrime := RingHom.ker_isPrime _
  have hmonic := Polynomial.monic_X_pow_sub_C g hn.ne'
  have hdegree : (Polynomial.X ^ n - Polynomial.C g).natDegree = n :=
    Polynomial.natDegree_X_pow_sub_C
  have hmem : ∀ j < (Polynomial.X ^ n - Polynomial.C g).natDegree,
      (Polynomial.X ^ n - Polynomial.C g).coeff j ∈ I := by
    intro j hj
    rw [hdegree] at hj
    by_cases hj0 : j = 0
    · subst j
      simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, hn.ne, if_false,
        Polynomial.coeff_C_zero, zero_sub]
      exact I.neg_mem (RingHom.mem_ker.mpr hg)
    · simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, ne_of_lt hj, if_false,
        Polynomial.coeff_C, hj0, sub_zero]
      exact I.zero_mem
  have hnot : (Polynomial.X ^ n - Polynomial.C g).coeff 0 ∉ I ^ 2 := by
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, hn.ne, if_false,
      Polynomial.coeff_C_zero, zero_sub]
    intro h
    have hgI : g ∈ I ^ 2 := (Ideal.neg_mem_iff _).mp h
    exact hderiv (eval_pderiv_eq_zero_of_mem_ker_sq x i g hgI)
  exact (hmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top
    (fun hj => hmem _ hj) hnot).irreducible hprime hmonic.isPrimitive (by rw [hdegree]; exact hn)

noncomputable def sexticSurface (c : K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 - MvPolynomial.X 2 ^ 6 - MvPolynomial.C c

lemma finSuccEquiv_sexticSurface (c : K) :
    MvPolynomial.finSuccEquiv K 2 (sexticSurface c) =
      Polynomial.X ^ 6 - Polynomial.C
        (MvPolynomial.C c - MvPolynomial.X (0 : Fin 2) ^ 6 + MvPolynomial.X 1 ^ 6) := by
  simp only [Nat.reduceAdd, sexticSurface, Fin.isValue, MvPolynomial.finSuccEquiv_apply,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, Fin.cases_zero, MvPolynomial.eval₂_C,
    RingHom.coe_comp, Function.comp_apply, map_add, map_sub, map_pow]
  change Polynomial.X ^ 6 + Polynomial.C (MvPolynomial.X (0 : Fin 2)) ^ 6 -
    Polynomial.C (MvPolynomial.X (1 : Fin 2)) ^ 6 - Polynomial.C (MvPolynomial.C c) = _
  ring

lemma totalDegree_sexticSurface_le (c : K) : (sexticSurface c).totalDegree ≤ 6 := by
  apply (MvPolynomial.totalDegree_sub_C_le _ c).trans
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  · simp

/-- Irreducibility is proved over every algebraically closed field of
characteristic zero, so it includes the required geometric irreducibility. -/
theorem irreducible_sexticSurface [CharZero K] [IsAlgClosed K]
    (c : K) (hc : c ≠ 0) : Irreducible (sexticSurface c) := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq c (by decide : 0 < 6)
  have ha0 : a ≠ 0 := by
    intro h
    simp only [h, zero_pow (by decide : 6 ≠ 0)] at ha
    exact hc ha.symm
  let g : MvPolynomial (Fin 2) K :=
    MvPolynomial.C c - MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6
  have hg : MvPolynomial.eval ![a, 0] g = 0 := by simp [g, ha]
  have hderiv : MvPolynomial.eval ![a, 0] (MvPolynomial.pderiv 0 g) ≠ 0 := by
    have h6 : (6 : K) ≠ 0 := by norm_num
    simpa [g, MvPolynomial.pderiv_pow] using neg_ne_zero.mpr (mul_ne_zero h6 (pow_ne_zero 5 ha0))
  have hirr := irreducible_X_pow_sub_of_simple_zero g ![a, 0] hg 0 hderiv 6 (by decide)
  have heq : MvPolynomial.finSuccEquiv K 2 (sexticSurface c) =
      Polynomial.X ^ 6 - Polynomial.C g := finSuccEquiv_sexticSurface c
  rw [← heq] at hirr
  exact (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv K 2)).mp hirr

#print axioms irreducible_sexticSurface
-- 'Erdos477.Geometry.irreducible_sexticSurface' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
