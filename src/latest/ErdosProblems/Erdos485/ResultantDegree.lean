import Mathlib

/-!
# Degree bounds for bivariate resultants

A bivariate polynomial is written as `Polynomial (Polynomial K)`, with the outer variable
playing the role of `y` and the coefficient variable playing the role of `z`.  This file records
the elementary determinant estimate

`deg_z Res_y(F,G) ≤ deg_y(F) * maxdeg_z(G) + deg_y(G) * maxdeg_z(F)`.

It also packages the two resultant facts used in the squarefree-gap argument: nonvanishing after
passing to the fraction field of `K[z]`, and the Sylvester-adjugate Bezout identity.
-/

namespace Erdos485

open Matrix Polynomial Equiv.Perm

noncomputable section

/-- The largest `z`-degree among the (nonzero) `y`-coefficients of a bivariate polynomial. -/
def maxCoeffDegree {K : Type*} [Semiring K] (F : Polynomial (Polynomial K)) : ℕ :=
  F.support.sup fun i ↦ (F.coeff i).natDegree

/-- Every `y`-coefficient has `z`-degree at most `maxCoeffDegree`. -/
theorem coeff_natDegree_le_maxCoeffDegree {K : Type*} [Semiring K]
    (F : Polynomial (Polynomial K)) (i : ℕ) :
    (F.coeff i).natDegree ≤ maxCoeffDegree F := by
  by_cases hi : i ∈ F.support
  · exact Finset.le_sup (f := fun j ↦ (F.coeff j).natDegree) hi
  · rw [not_ne_iff.mp (mt Polynomial.mem_support_iff.mpr hi)]
    exact Nat.zero_le _

/-- A determinant over `K[z]` has degree bounded by the sum of uniform column bounds. -/
theorem natDegree_det_le_sum_column_bounds {K ι : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (Polynomial K)) (d : ι → ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le
    (s := Finset.univ)
    (fun σ : Equiv.Perm ι ↦ Equiv.Perm.sign σ • ∏ i, A (σ i) i) ?_
  intro σ _
  calc
    (Equiv.Perm.sign σ • ∏ i, A (σ i) i).natDegree ≤
        (∏ i, A (σ i) i).natDegree := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · rw [hσ, one_smul]
      · rw [hσ, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (A (σ i) i).natDegree :=
      Polynomial.natDegree_prod_le (Finset.univ : Finset ι) fun i ↦ A (σ i) i
    _ ≤ ∑ i, d i := Finset.sum_le_sum fun i _ ↦ hA (σ i) i

/-- The `z`-degree of a bivariate resultant, with freely supplied upper bounds on the two
`y`-degrees.  Supplying bounds instead of requiring equality makes the lemma useful for zero or
degree-dropped special cases too. -/
theorem natDegree_resultant_le {K : Type*} [CommRing K]
    (F G : Polynomial (Polynomial K)) (m n dF dG : ℕ)
    (_hF : F.natDegree ≤ m) (_hG : G.natDegree ≤ n)
    (hFd : maxCoeffDegree F ≤ dF) (hGd : maxCoeffDegree G ≤ dG) :
    (F.resultant G m n).natDegree ≤ m * dG + n * dF := by
  rw [Polynomial.resultant]
  refine (natDegree_det_le_sum_column_bounds (F.sylvester G m n)
    (fun j ↦ j.addCases (fun _ ↦ dG) (fun _ ↦ dF)) ?_).trans ?_
  · intro i j
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact (coeff_natDegree_le_maxCoeffDegree G _).trans hGd
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · exact (coeff_natDegree_le_maxCoeffDegree F _).trans hFd
        · simp
  · simp [Fin.sum_univ_add]

/-- The sharp coefficient-degree form of `natDegree_resultant_le`. -/
theorem natDegree_resultant_le_maxCoeffDegree {K : Type*} [CommRing K]
    (F G : Polynomial (Polynomial K)) :
    (F.resultant G).natDegree ≤
      F.natDegree * maxCoeffDegree G + G.natDegree * maxCoeffDegree F := by
  exact natDegree_resultant_le F G F.natDegree G.natDegree
    (maxCoeffDegree F) (maxCoeffDegree G) le_rfl le_rfl le_rfl le_rfl

/-- The numerical specialization used for `G = (D F)^2`: if `F` is bounded by `(dY,dZ)`
and `G` by `(2*dY,2*dZ)`, then the resultant has `z`-degree at most `4*dY*dZ`. -/
theorem natDegree_resultant_le_four_mul {K : Type*} [CommRing K]
    (F G : Polynomial (Polynomial K)) (dY dZ : ℕ)
    (hFy : F.natDegree ≤ dY) (hGy : G.natDegree ≤ 2 * dY)
    (hFz : maxCoeffDegree F ≤ dZ) (hGz : maxCoeffDegree G ≤ 2 * dZ) :
    (F.resultant G dY (2 * dY)).natDegree ≤ 4 * dY * dZ := by
  calc
    (F.resultant G dY (2 * dY)).natDegree ≤
        dY * (2 * dZ) + (2 * dY) * dZ :=
      natDegree_resultant_le F G dY (2 * dY) dZ (2 * dZ)
        hFy hGy hFz hGz
    _ = 4 * dY * dZ := by ring

/-- The Sylvester adjugate supplies a Bezout identity for the resultant. -/
theorem exists_bivariate_bezout_resultant {K : Type*} [CommRing K]
    (F G : Polynomial (Polynomial K)) (m n : ℕ)
    (hF : F.natDegree ≤ m) (hG : G.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) :
    ∃ A B : Polynomial (Polynomial K),
      A.degree < n ∧ B.degree < m ∧
        F * A + G * B = Polynomial.C (F.resultant G m n) := by
  exact Polynomial.exists_mul_add_mul_eq_C_resultant F G hF hG hmn

/-- If the images of two polynomials are coprime over a fraction field, their original
resultant is nonzero.  This is the convenient Gauss-lemma-facing form: the caller proves
coprimality after mapping, while injectivity brings nonvanishing back to `K[z]`. -/
theorem resultant_ne_zero_of_fractionRing_isCoprime
    {R L : Type*} [CommRing R] [IsDomain R] [Field L]
    (algebraMapRL : R →+* L) (hinj : Function.Injective algebraMapRL)
    (F G : Polynomial R)
    (hcop : IsCoprime (F.map algebraMapRL) (G.map algebraMapRL)) :
    F.resultant G ≠ 0 := by
  intro hres
  have hmapped : (F.map algebraMapRL).resultant (G.map algebraMapRL) = 0 := by
    rw [Polynomial.resultant_map_map,
      Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.natDegree_map_eq_of_injective hinj, hres, map_zero]
  exact Polynomial.resultant_ne_zero _ _ hcop hmapped

/-- `resultant_ne_zero_of_fractionRing_isCoprime` for the canonical fraction field. -/
theorem resultant_ne_zero_of_isCoprime_fractionRing
    {R : Type*} [CommRing R] [IsDomain R] (F G : Polynomial R)
    (hcop : IsCoprime
      (F.map (algebraMap R (FractionRing R)))
      (G.map (algebraMap R (FractionRing R)))) :
    F.resultant G ≠ 0 := by
  exact resultant_ne_zero_of_fractionRing_isCoprime
    (algebraMap R (FractionRing R)) (IsFractionRing.injective R (FractionRing R)) F G hcop

end

end Erdos485
