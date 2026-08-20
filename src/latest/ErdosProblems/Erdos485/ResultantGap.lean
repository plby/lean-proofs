import ErdosProblems.Erdos485.ResultantDegree

/-!
# The resultant core of Schinzel's squarefree-gap lemma

We write a bivariate polynomial as `Polynomial (Polynomial K)`, with outer variable `y`
and coefficient variable `z`.  The substitution `y = x^n`, `z = x` is therefore simply
`H.eval (Polynomial.X ^ n)`.

This file isolates the two algebraic branches of the squarefree-gap argument.

* If `H` has positive `y`-degree, coprimality of `H` with a polynomial `D`, the divisibility
  `H(x^n,x) ∣ D(x^n,x)^2`, and the gap `4 * deg_z H < n` contradict the resultant degree
  estimate.
* If `H` has `y`-degree zero, the required conclusion is the elementary univariate fact that a
  squarefree `H` not divisible by `X` cannot divide `(X * H')^2` unless it is a unit.

The hypotheses involving `D` are exactly the interface supplied later by the weighted Euler
derivation and the distinct-weight argument.  No factorization or coprimality claim is hidden in
this module.
-/

namespace Erdos485

open Polynomial

noncomputable section

/-! ## Kronecker substitution without collisions -/

/-- If every coefficient of `H(y)` has `z`-degree below `n`, the coefficient at the encoded
top exponent is the leading coefficient of the leading `y`-coefficient.  This is the precise
no-collision statement needed for the lower bound on `deg H(x^n,x)`. -/
theorem coeff_eval_X_pow_at_top_of_coeff_natDegree_lt
    {K : Type*} [Field K]
    (H : Polynomial (Polynomial K)) (n : ℕ)
    (hcoeff : ∀ i, (H.coeff i).natDegree < n) :
    (H.eval (X ^ n)).coeff (n * H.natDegree + H.leadingCoeff.natDegree) =
      H.leadingCoeff.leadingCoeff := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.finsetSum_coeff,
    Finset.sum_range_succ]
  have hsum :
      ∑ x ∈ Finset.range H.natDegree,
          (H.coeff x * (X ^ n) ^ x).coeff
            (n * H.natDegree + H.leadingCoeff.natDegree) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_range] at hx
    rw [← pow_mul, Polynomial.coeff_mul_X_pow']
    have hshift : n * x + n ≤ n * H.natDegree + H.leadingCoeff.natDegree := by
      calc
        n * x + n = n * (x + 1) := by ring
        _ ≤ n * H.natDegree :=
          Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr hx)
        _ ≤ n * H.natDegree + H.leadingCoeff.natDegree := Nat.le_add_right _ _
    have hbase : n * x ≤ n * H.natDegree + H.leadingCoeff.natDegree :=
      (Nat.le_add_right (n * x) n).trans hshift
    rw [if_pos hbase]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    exact (hcoeff x).trans_le
      (Nat.le_sub_of_add_le (by simpa [Nat.add_comm] using hshift))
  rw [hsum, zero_add, ← pow_mul]
  have htarget :
      n * H.natDegree + H.leadingCoeff.natDegree =
        H.leadingCoeff.natDegree + n * H.natDegree := by omega
  rw [Polynomial.coeff_natDegree, htarget, Polynomial.coeff_mul_X_pow,
    Polynomial.coeff_natDegree]

/-- The collision-free substitution `y = x^n`, `z = x` has degree at least
`n * deg_y H`. -/
theorem mul_natDegree_le_natDegree_eval_X_pow
    {K : Type*} [Field K]
    (H : Polynomial (Polynomial K)) (n : ℕ)
    (hH : H ≠ 0)
    (hcoeff : ∀ i, (H.coeff i).natDegree < n) :
    n * H.natDegree ≤ (H.eval (X ^ n)).natDegree := by
  have hinner : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH
  have htop : H.leadingCoeff.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hinner
  have hcoeffTop :
      (H.eval (X ^ n)).coeff
          (n * H.natDegree + H.leadingCoeff.natDegree) ≠ 0 := by
    rw [coeff_eval_X_pow_at_top_of_coeff_natDegree_lt H n hcoeff]
    exact htop
  exact (Nat.le_add_right _ _).trans (Polynomial.le_natDegree_of_ne_zero hcoeffTop)

/-! ## Coefficient-degree bookkeeping for a square -/

/-- Multiplication adds uniform bounds on the `z`-degrees of all `y`-coefficients. -/
theorem natDegree_coeff_mul_le
    {K : Type*} [Field K]
    (P Q : Polynomial (Polynomial K)) (a b i : ℕ)
    (hP : ∀ j, (P.coeff j).natDegree ≤ a)
    (hQ : ∀ j, (Q.coeff j).natDegree ≤ b) :
    ((P * Q).coeff i).natDegree ≤ a + b := by
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro jk _hjk
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP jk.1) (hQ jk.2))

/-- The maximum coefficient degree is subadditive under multiplication. -/
theorem maxCoeffDegree_mul_le
    {K : Type*} [Field K] (P Q : Polynomial (Polynomial K)) :
    maxCoeffDegree (P * Q) ≤ maxCoeffDegree P + maxCoeffDegree Q := by
  unfold maxCoeffDegree
  apply Finset.sup_le
  intro i _hi
  exact natDegree_coeff_mul_le P Q (maxCoeffDegree P) (maxCoeffDegree Q) i
    (coeff_natDegree_le_maxCoeffDegree P) (coeff_natDegree_le_maxCoeffDegree Q)

/-- Squaring at most doubles the maximum coefficient degree. -/
theorem maxCoeffDegree_sq_le
    {K : Type*} [Field K] (P : Polynomial (Polynomial K)) :
    maxCoeffDegree (P ^ 2) ≤ 2 * maxCoeffDegree P := by
  rw [pow_two]
  simpa [two_mul] using maxCoeffDegree_mul_le P P

/-! ## The positive-`y`-degree resultant contradiction -/

/-- Resultant form of the positive-degree squarefree-gap contradiction.

The polynomial `E` is normally `(D H)^2`.  It is kept abstract here because this is the useful
resultant interface: its bidegree is at most twice that of `H`, it is coprime to `H`, and its
specialization is divisible by the specialization of `H`. -/
theorem resultant_gap_contradiction
    {K : Type*} [Field K]
    (H E : Polynomial (Polynomial K)) (n dY dZ : ℕ)
    (hH : H ≠ 0)
    (hHy : H.natDegree = dY)
    (hdY : 0 < dY)
    (hEy : E.natDegree ≤ 2 * dY)
    (hHz : maxCoeffDegree H ≤ dZ)
    (hEz : maxCoeffDegree E ≤ 2 * dZ)
    (hcop : IsCoprime H E)
    (hdiv : H.eval (X ^ n) ∣ E.eval (X ^ n))
    (hgap : 4 * dZ < n) : False := by
  let R : Polynomial K := H.resultant E
  have hR0 : R ≠ 0 := by
    exact Polynomial.resultant_ne_zero H E hcop
  have hRdeg0 : R.natDegree ≤
      H.natDegree * maxCoeffDegree E + E.natDegree * maxCoeffDegree H :=
    natDegree_resultant_le_maxCoeffDegree H E
  have hRdeg : R.natDegree ≤ 4 * dY * dZ := by
    calc
      R.natDegree ≤
          H.natDegree * maxCoeffDegree E + E.natDegree * maxCoeffDegree H := hRdeg0
      _ ≤ dY * (2 * dZ) + (2 * dY) * dZ := by
        apply Nat.add_le_add
        · rw [hHy]
          exact Nat.mul_le_mul_left dY hEz
        · exact Nat.mul_le_mul hEy hHz
      _ = 4 * dY * dZ := by ring
  obtain ⟨A, B, _hAdeg, _hBdeg, hbez⟩ :=
    exists_bivariate_bezout_resultant H E H.natDegree E.natDegree le_rfl le_rfl
      (Or.inl (by simpa [hHy] using hdY.ne'))
  have hbezEval := congrArg (Polynomial.eval (X ^ n)) hbez
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C] at hbezEval
  have hHR : H.eval (X ^ n) ∣ R := by
    change H.eval (X ^ n) ∣ H.resultant E
    rw [← hbezEval]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_left hdiv _)
  have hsubdeg : (H.eval (X ^ n)).natDegree ≤ R.natDegree :=
    Polynomial.natDegree_le_of_dvd hHR hR0
  have hdZn : dZ < n := by omega
  have hcoeff : ∀ i, (H.coeff i).natDegree < n := fun i ↦
    (coeff_natDegree_le_maxCoeffDegree H i).trans hHz |>.trans_lt hdZn
  have hlower : n * dY ≤ (H.eval (X ^ n)).natDegree := by
    rw [← hHy]
    exact mul_natDegree_le_natDegree_eval_X_pow H n hH hcoeff
  have hmul : n * dY ≤ (4 * dZ) * dY := by
    calc
      n * dY ≤ (H.eval (X ^ n)).natDegree := hlower
      _ ≤ R.natDegree := hsubdeg
      _ ≤ 4 * dY * dZ := hRdeg
      _ = (4 * dZ) * dY := by ring
  have : n ≤ 4 * dZ := Nat.le_of_mul_le_mul_right hmul hdY
  omega

/-- The form used directly with the weighted Euler polynomial `D`.  The preceding theorem is
applied to `E = D^2`; all doubled bidegree and coprimality hypotheses are derived here. -/
theorem resultant_square_gap_contradiction
    {K : Type*} [Field K]
    (H D : Polynomial (Polynomial K)) (n dY dZ : ℕ)
    (hH : H ≠ 0)
    (hHy : H.natDegree = dY)
    (hdY : 0 < dY)
    (hDy : D.natDegree ≤ dY)
    (hHz : maxCoeffDegree H ≤ dZ)
    (hDz : maxCoeffDegree D ≤ dZ)
    (hcop : IsCoprime H D)
    (hdiv : H.eval (X ^ n) ∣ (D.eval (X ^ n)) ^ 2)
    (hgap : 4 * dZ < n) : False := by
  have hDsqY : (D ^ 2).natDegree ≤ 2 * dY := by
    exact Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hDy)
  have hDsqZ : maxCoeffDegree (D ^ 2) ≤ 2 * dZ :=
    (maxCoeffDegree_sq_le D).trans (Nat.mul_le_mul_left 2 hDz)
  have hdiv' : H.eval (X ^ n) ∣ (D ^ 2).eval (X ^ n) := by
    simpa only [Polynomial.eval_pow] using hdiv
  exact resultant_gap_contradiction H (D ^ 2) n dY dZ hH hHy hdY hDsqY hHz hDsqZ
    hcop.pow_right hdiv' hgap

/-! ## The zero-`y`-degree branch -/

/-- A squarefree univariate polynomial not divisible by `X` cannot divide the square of its
Euler derivative unless it is a unit.  This is the `deg_y H = 0` branch of the squarefree-gap
lemma. -/
theorem squarefree_dvd_eulerSquare_isUnit
    {K : Type*} [Field K] [PerfectField K]
    (H : Polynomial K)
    (hsq : Squarefree H)
    (hX : ¬ X ∣ H)
    (hdiv : H ∣ (X * H.derivative) ^ 2) : IsUnit H := by
  have hsep : H.Separable := PerfectField.separable_iff_squarefree.mpr hsq
  have hcopDeriv : IsCoprime H H.derivative := hsep
  have hcopX : IsCoprime H X := by
    rcases EuclideanDomain.dvd_or_coprime X H Polynomial.irreducible_X with h | h
    · exact False.elim (hX h)
    · exact h.symm
  have hcopEuler : IsCoprime H (X * H.derivative) :=
    hcopX.mul_right hcopDeriv
  exact hcopEuler.pow_right.isUnit_of_dvd hdiv

end

end Erdos485
