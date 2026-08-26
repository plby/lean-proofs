/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The defining sextic polynomial and independence of the auxiliary monomial family.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.SexticPolynomials

namespace Erdos477.Counting

noncomputable def sexticSurface (c : ℤ) : MvPolynomial (Fin 3) ℤ :=
  MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 - MvPolynomial.X 2 ^ 6 - MvPolynomial.C c

lemma eval_sexticSurface (c : ℤ) (z : Fin 3 → ℤ) :
    MvPolynomial.eval z (sexticSurface c) = z 0 ^ 6 + z 1 ^ 6 - z 2 ^ 6 - c := by
  simp [sexticSurface]

lemma degreeOf_sexticSurface (c : ℤ) : (sexticSurface c).degreeOf 2 = 6 := by
  let Q : MvPolynomial (Fin 3) ℤ :=
    MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 - MvPolynomial.C c
  have h0 : (MvPolynomial.X 0 ^ 6 : MvPolynomial (Fin 3) ℤ).degreeOf 2 = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne 6 (by decide)
  have h1 : (MvPolynomial.X 1 ^ 6 : MvPolynomial (Fin 3) ℤ).degreeOf 2 = 0 :=
    MvPolynomial.degreeOf_X_pow_of_ne 6 (by decide)
  have hQ : Q.degreeOf 2 = 0 := by
    have ha := MvPolynomial.degreeOf_add_le 2
      (MvPolynomial.X 0 ^ 6 : MvPolynomial (Fin 3) ℤ) (MvPolynomial.X 1 ^ 6)
    have hb := MvPolynomial.degreeOf_sub_le 2
      (MvPolynomial.X 0 ^ 6 + MvPolynomial.X 1 ^ 6 : MvPolynomial (Fin 3) ℤ)
      (MvPolynomial.C c)
    simp only [h0, h1, MvPolynomial.degreeOf_C, max_self] at ha hb
    dsimp only [Q]
    omega
  have htop : (-MvPolynomial.X 2 ^ 6 : MvPolynomial (Fin 3) ℤ).degreeOf 2 = 6 := by
    rw [MvPolynomial.degreeOf_neg, MvPolynomial.degreeOf_X_self_pow]
  have heq : sexticSurface c = -MvPolynomial.X 2 ^ 6 + Q := by
    dsimp only [sexticSurface, Q]
    ring
  rw [heq, MvPolynomial.degreeOf_add_eq_of_degreeOf_lt (by rw [hQ, htop]; decide), htop]

lemma sexticSurface_ne_zero (c : ℤ) : sexticSurface c ≠ 0 :=
  MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [degreeOf_sexticSurface]; decide)

/-- A nonzero linear combination of the chosen monomials cannot contain the
surface equation as a factor: its degree in the last variable is at most five. -/
theorem sexticSurface_not_dvd_combination {n : ℕ} (c : ℤ)
    (v : SexticMonomial n → ℤ) (hv : ∃ a, v a ≠ 0) :
    ¬ sexticSurface c ∣ sexticCombination v := by
  intro hdiv
  obtain ⟨Q, hQ⟩ := hdiv
  have hQ0 : Q ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ
    exact sexticCombination_ne_zero v hv hQ
  have hdegree := degreeOf_sexticCombination v
  rw [hQ, MvPolynomial.degreeOf_mul_eq (sexticSurface_ne_zero c) hQ0,
    degreeOf_sexticSurface] at hdegree
  omega

#print axioms sexticSurface_not_dvd_combination
-- 'Erdos477.Counting.sexticSurface_not_dvd_combination' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Counting
