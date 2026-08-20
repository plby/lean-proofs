/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib

/-!
# Generalized Wronskians over the rationals

This file contains the rational form of the generalized-Wronskian lemma used
in the proof of the binary Roth lemma.  We use ordinary formal partial
derivatives.  This differs from the divided derivatives in GLR only by a
nonzero rational scalar on every row.
-/

namespace Erdos407.GeneralizedWronskian

open scoped BigOperators
open Polynomial

noncomputable section

/-- A (not necessarily finitely supported, since the variable set is finite)
multi-index. -/
abbrev MultiIndex (m : ℕ) := Fin m → ℕ

/-- Total order of a multi-index. -/
def totalOrder {m : ℕ} (μ : MultiIndex m) : ℕ :=
  ∑ i, μ i

/-- Apply the indicated partial derivative repeatedly.  The fixed order in
which variables are traversed is immaterial because formal partial
derivatives commute; fixing it makes the definition computationally simple. -/
def multiDerivative {m : ℕ} (μ : MultiIndex m)
    (P : MvPolynomial (Fin m) ℚ) : MvPolynomial (Fin m) ℚ :=
  Finset.univ.toList.foldl
    (fun Q i ↦ (MvPolynomial.pderiv i)^[μ i] Q) P

/-- The generalized Wronskian belonging to a tuple of multi-indices. -/
def generalizedWronskian {m r : ℕ} (μ : Fin r → MultiIndex m)
    (P : Fin r → MvPolynomial (Fin m) ℚ) : MvPolynomial (Fin m) ℚ :=
  Matrix.det fun i j ↦ multiDerivative (μ i) (P j)

@[simp] theorem totalOrder_zero {m : ℕ} :
    totalOrder (fun _ : Fin m ↦ 0) = 0 := by
  simp [totalOrder]

private theorem iterate_pderiv_add {m : ℕ} (i : Fin m) (n : ℕ)
    (P Q : MvPolynomial (Fin m) ℚ) :
    (MvPolynomial.pderiv i)^[n] (P + Q) =
      (MvPolynomial.pderiv i)^[n] P + (MvPolynomial.pderiv i)^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply', ih, map_add]

private theorem iterate_pderiv_smul {m : ℕ} (i : Fin m) (n : ℕ)
    (a : ℚ) (P : MvPolynomial (Fin m) ℚ) :
    (MvPolynomial.pderiv i)^[n] (a • P) =
      a • (MvPolynomial.pderiv i)^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih]
      exact (MvPolynomial.pderiv i).map_smul a _

@[simp] theorem multiDerivative_zero {m : ℕ} (μ : MultiIndex m) :
    multiDerivative μ (0 : MvPolynomial (Fin m) ℚ) = 0 := by
  unfold multiDerivative
  generalize (Finset.univ.toList : List (Fin m)) = l
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      have hz : (MvPolynomial.pderiv i)^[μ i]
          (0 : MvPolynomial (Fin m) ℚ) = 0 := by
        induction μ i with
        | zero => rfl
        | succ n hn => simp [Function.iterate_succ_apply', hn]
      simpa [hz] using ih

@[simp] theorem multiDerivative_zero_index {m : ℕ}
    (P : MvPolynomial (Fin m) ℚ) :
    multiDerivative (fun _ : Fin m ↦ 0) P = P := by
  simp [multiDerivative]

@[simp] theorem multiDerivative_add {m : ℕ} (μ : MultiIndex m)
    (P Q : MvPolynomial (Fin m) ℚ) :
    multiDerivative μ (P + Q) = multiDerivative μ P + multiDerivative μ Q := by
  unfold multiDerivative
  generalize (Finset.univ.toList : List (Fin m)) = l
  induction l generalizing P Q with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons, iterate_pderiv_add]
      exact ih _ _

@[simp] theorem multiDerivative_finsetSum {m : ℕ} {ι : Type*}
    (μ : MultiIndex m) (s : Finset ι)
    (F : ι → MvPolynomial (Fin m) ℚ) :
    multiDerivative μ (∑ i ∈ s, F i) = ∑ i ∈ s, multiDerivative μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

@[simp] theorem multiDerivative_smul {m : ℕ} (μ : MultiIndex m)
    (a : ℚ) (P : MvPolynomial (Fin m) ℚ) :
    multiDerivative μ (a • P) = a • multiDerivative μ P := by
  unfold multiDerivative
  generalize (Finset.univ.toList : List (Fin m)) = l
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      simp only [List.foldl_cons, iterate_pderiv_smul]
      exact ih _

/-- A single partial derivative cannot increase the degree in any variable. -/
theorem degreeOf_pderiv_le {m : ℕ} (i k : Fin m)
    (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.degreeOf k (MvPolynomial.pderiv i P) ≤
      MvPolynomial.degreeOf k P := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hdcoeff : MvPolynomial.coeff d (MvPolynomial.pderiv i P) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  have hc : MvPolynomial.coeff (d + Finsupp.single i 1) P ≠ 0 := by
    intro hzero
    apply hdcoeff
    rw [MvPolynomial.coeff_pderiv, hzero, zero_mul]
  have hs : d + Finsupp.single i 1 ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hc
  calc
    d k ≤ (d + Finsupp.single i 1 : Fin m →₀ ℕ) k := by simp
    _ ≤ MvPolynomial.degreeOf k P := MvPolynomial.monomial_le_degreeOf k hs

private theorem degreeOf_iterate_pderiv_le {m : ℕ} (i k : Fin m) (n : ℕ)
    (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.degreeOf k ((MvPolynomial.pderiv i)^[n] P) ≤
      MvPolynomial.degreeOf k P := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (degreeOf_pderiv_le i k _).trans ih

/-- A mixed partial derivative cannot increase the degree in any variable. -/
theorem degreeOf_multiDerivative_le {m : ℕ} (k : Fin m)
    (μ : MultiIndex m) (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.degreeOf k (multiDerivative μ P) ≤
      MvPolynomial.degreeOf k P := by
  unfold multiDerivative
  generalize (Finset.univ.toList : List (Fin m)) = l
  induction l generalizing P with
  | nil => exact le_rfl
  | cons i l ih =>
      simp only [List.foldl_cons]
      exact (ih _).trans (degreeOf_iterate_pderiv_le i k (μ i) P)

/-! ### The univariate determinant -/

private def polynomialWronskianMatrix {r : ℕ} (P : Fin r → Polynomial ℚ) :
    Matrix (Fin r) (Fin r) (Polynomial ℚ) :=
  fun i j ↦ (Polynomial.derivative)^[i.1] (P j)

/-- The ordinary square Wronskian matrix, with derivative orders `0,…,r-1`. -/
private def polynomialWronskian {r : ℕ} (P : Fin r → Polynomial ℚ) : Polynomial ℚ :=
  Matrix.det (polynomialWronskianMatrix P)

private theorem coeff_finset_prod_at_sum {r : ℕ} (s : Finset (Fin r))
    (P : Fin r → Polynomial ℚ) (d : Fin r → ℕ)
    (hdeg : ∀ i ∈ s, (P i).natDegree ≤ d i) :
    (s.prod P).coeff (s.sum d) = s.prod fun i ↦ (P i).coeff (d i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Polynomial.coeff_mul_add_eq_of_natDegree_le (hdeg a (Finset.mem_insert_self _ _))]
      · rw [ih (fun i hi ↦ hdeg i (Finset.mem_insert_of_mem hi)), Finset.prod_insert ha]
      · exact (Polynomial.natDegree_prod_le _ _).trans <|
          Finset.sum_le_sum fun i hi ↦ hdeg i (Finset.mem_insert_of_mem hi)

private theorem fallingFactorial_det_ne_zero {r : ℕ} {d : Fin r → ℕ}
    (hd : Function.Injective d) :
    Matrix.det (Matrix.of fun i j : Fin r ↦ ((d j).descFactorial i.1 : ℚ)) ≠ 0 := by
  let v : Fin r → ℚ := fun j ↦ d j
  let A : Matrix (Fin r) (Fin r) ℚ :=
    Matrix.of fun j i ↦ (descPochhammer ℚ i.1).eval (v j)
  have hv : Function.Injective v := by
    intro i j hij
    exact hd (Nat.cast_injective hij)
  have hdetA : A.det ≠ 0 := by
    rw [← Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun i : Fin r ↦ descPochhammer ℚ i.1)
      (fun i ↦ descPochhammer_natDegree ℚ i.1)
      (fun i ↦ monic_descPochhammer ℚ i.1)]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have heq : (Matrix.of fun i j : Fin r ↦ ((d j).descFactorial i.1 : ℚ)) = A.transpose := by
    ext i j
    simp [A, v, descPochhammer_eval_eq_descFactorial]
  rw [heq, Matrix.det_transpose]
  exact hdetA

private theorem derivative_leading_coeff {r : ℕ} (P : Polynomial ℚ) (i : Fin r)
    (hi : i.1 ≤ P.natDegree) :
    ((Polynomial.derivative)^[i.1] P).coeff (P.natDegree - i.1) =
      (P.natDegree.descFactorial i.1 : ℚ) * P.leadingCoeff := by
  rw [Polynomial.coeff_iterate_derivative]
  have hadd : P.natDegree - i.1 + i.1 = P.natDegree := Nat.sub_add_cancel hi
  rw [hadd, Polynomial.coeff_natDegree, nsmul_eq_mul]

private def leadingDerivativeMatrix {r : ℕ} (P : Fin r → Polynomial ℚ) :
    Matrix (Fin r) (Fin r) ℚ :=
  fun i j ↦ ((P j).natDegree.descFactorial i.1 : ℚ) * (P j).leadingCoeff

private theorem polynomialWronskian_ne_zero_of_natDegree_injective {r : ℕ}
    (P : Fin r → Polynomial ℚ) (hP : Function.Injective (fun j ↦ (P j).natDegree))
    (hP0 : ∀ j, P j ≠ 0) :
    polynomialWronskian P ≠ 0 := by
  let d : Fin r → ℕ := fun j ↦ (P j).natDegree
  let N : ℕ := (∑ j, d j) - ∑ i : Fin r, i.1
  let B : Matrix (Fin r) (Fin r) ℚ := leadingDerivativeMatrix P
  have hsum : (∑ i : Fin r, i.1) ≤ ∑ j, d j := by
    let s : Finset ℕ := Finset.univ.image d
    have hs : s.card = r := by
      simpa [s] using Finset.card_image_of_injective Finset.univ hP
    let e : Fin r ↪o ℕ := s.orderEmbOfFin hs
    have hie : ∀ i : Fin r, i.1 ≤ e i := by
      intro i
      have haux : ∀ (n : ℕ) (j : Fin r), j.1 = n → n ≤ e j := by
        intro n
        induction n with
        | zero => intro j hj; exact Nat.zero_le _
        | succ n ih =>
            intro j hj
            let k : Fin r := ⟨n, by omega⟩
            have hkj : k < j := by
              change n < j.1
              omega
            exact Nat.succ_le_of_lt ((ih k rfl).trans_lt (e.strictMono hkj))
      exact haux i.1 i rfl
    calc
      (∑ i : Fin r, i.1) ≤ ∑ i : Fin r, e i := Finset.sum_le_sum fun i _ ↦ hie i
      _ = ∑ x : s, x.1 := by
        exact (s.orderIsoOfFin hs).toEquiv.sum_comp (fun x : s ↦ x.1)
      _ = ∑ n ∈ s, n := by
        exact Finset.sum_attach s (fun n ↦ n)
      _ = ∑ j, d j := by
        rw [show s = Finset.univ.image d from rfl, Finset.sum_image]
        exact fun _ _ _ _ h ↦ hP h
  have hdetB : B.det ≠ 0 := by
    let F : Matrix (Fin r) (Fin r) ℚ :=
      fun i j ↦ ((d j).descFactorial i.1 : ℚ)
    let D : Matrix (Fin r) (Fin r) ℚ := Matrix.diagonal fun j ↦ (P j).leadingCoeff
    have hFD : F * D = B := by
      ext i j
      rw [Matrix.mul_diagonal]
      rfl
    rw [← hFD, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (fallingFactorial_det_ne_zero hP)
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ Polynomial.leadingCoeff_ne_zero.mpr (hP0 j))
  have hcoeff : (polynomialWronskian P).coeff N = B.det := by
    rw [polynomialWronskian, Matrix.det_apply (polynomialWronskianMatrix P),
      Matrix.det_apply B]
    change (Polynomial.lcoeff ℚ N) (∑ σ, Equiv.Perm.sign σ •
      ∏ i, (Polynomial.derivative)^[(σ i).1] (P i)) = _
    rw [map_sum (Polynomial.lcoeff ℚ N)]
    apply Finset.sum_congr rfl
    intro σ hσ
    have hsign (Q : Polynomial ℚ) :
        Polynomial.lcoeff ℚ N (Equiv.Perm.sign σ • Q) =
          Equiv.Perm.sign σ • Polynomial.lcoeff ℚ N Q := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h] <;> simp
    rw [hsign]
    congr 1
    by_cases hvalid : ∀ j : Fin r, (σ j).1 ≤ d j
    · have hsumperm : ∑ j : Fin r, (d j - (σ j).1) = N := by
        change (∑ j : Fin r, (d j - (σ j).1)) =
          (∑ j, d j) - ∑ i : Fin r, i.1
        have hadd : (∑ j : Fin r, (d j - (σ j).1)) + ∑ i : Fin r, i.1 =
            ∑ j : Fin r, d j := by
          calc
          (∑ j : Fin r, (d j - (σ j).1)) + ∑ i : Fin r, i.1 =
              (∑ j : Fin r, (d j - (σ j).1)) + ∑ j : Fin r, (σ j).1 := by
                rw [Equiv.sum_comp]
          _ = ∑ j : Fin r, ((d j - (σ j).1) + (σ j).1) :=
            Finset.sum_add_distrib.symm
          _ = ∑ j : Fin r, d j := by
            apply Finset.sum_congr rfl
            intro j hj
            exact Nat.sub_add_cancel (hvalid j)
        exact ((Nat.sub_eq_iff_eq_add hsum).mpr hadd.symm).symm
      change (∏ i, (Polynomial.derivative)^[(σ i).1] (P i)).coeff N = _
      rw [← hsumperm, coeff_finset_prod_at_sum]
      · apply Finset.prod_congr rfl
        intro j hj
        change ((Polynomial.derivative)^[(σ j).1] (P j)).coeff
          ((P j).natDegree - (σ j).1) =
          ((P j).natDegree.descFactorial (σ j).1 : ℚ) * (P j).leadingCoeff
        exact derivative_leading_coeff (r := r) (P j) (σ j) (hvalid j)
      · intro j hj
        exact Polynomial.natDegree_iterate_derivative _ _
    · push_neg at hvalid
      obtain ⟨j, hj⟩ := hvalid
      have hz : (Polynomial.derivative)^[(σ j).1] (P j) = 0 :=
        Polynomial.iterate_derivative_eq_zero hj
      have hprod : ∏ k : Fin r, (Polynomial.derivative)^[(σ k).1] (P k) = 0 := by
        exact Finset.prod_eq_zero (Finset.mem_univ j) hz
      have hfall : (d j).descFactorial (σ j).1 = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr hj
      rw [hprod]
      simp only [map_zero]
      symm
      apply (Finset.prod_eq_zero (Finset.mem_univ j))
      simp [B, leadingDerivativeMatrix, d, hfall]
  intro hzero
  apply hdetB
  rw [← hcoeff, hzero, Polynomial.coeff_zero]

private theorem polynomialWronskian_ne_zero_of_linearIndependent {r : ℕ}
    (P : Fin r → Polynomial ℚ) (hP : LinearIndependent ℚ P) :
    polynomialWronskian P ≠ 0 := by
  have hP0 : ∀ j, P j ≠ 0 := fun j ↦ hP.ne_zero j
  generalize hN : (∑ j, (P j).natDegree) = N
  induction N using Nat.strong_induction_on generalizing P with
  | h N ih =>
      by_cases hdegInj : Function.Injective (fun j ↦ (P j).natDegree)
      · exact polynomialWronskian_ne_zero_of_natDegree_injective P hdegInj hP0
      · simp only [Function.Injective] at hdegInj
        push Not at hdegInj
        obtain ⟨a, b, hdeg, hab⟩ := hdegInj
        let c : ℚ := (P a).leadingCoeff / (P b).leadingCoeff
        let Q : Polynomial ℚ := P a - c • P b
        let Ψ : Fin r → Polynomial ℚ := Function.update P a Q
        have ha0 : P a ≠ 0 := hP0 a
        have hb0 : P b ≠ 0 := hP0 b
        have hca0 : (P a).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
        have hcb0 : (P b).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hb0
        have hc0 : c ≠ 0 := div_ne_zero hca0 hcb0
        have hcReg : IsSMulRegular ℚ c :=
          IsSMulRegular.of_mul_eq_one (inv_mul_cancel₀ hc0)
        have hsmul0 : c • P b ≠ 0 := smul_ne_zero hc0 hb0
        have hlc : (c • P b).leadingCoeff = (P a).leadingCoeff := by
          rw [Polynomial.leadingCoeff_smul_of_smul_regular _ hcReg]
          simp [c, hcb0]
        have hdegree : (P a).degree = (c • P b).degree := by
          rw [Polynomial.degree_eq_natDegree ha0, Polynomial.degree_eq_natDegree hsmul0,
            Polynomial.natDegree_smul_of_smul_regular _ hcReg, hdeg]
        have hΨ : LinearIndependent ℚ Ψ := by
          apply hP.update a Q
          refine ⟨1, by simp, Finsupp.single a 1 - Finsupp.single b c, ?_, ?_⟩
          · simp [hab]
          · simp only [one_smul]
            rw [map_sub]
            simp [Q, hab]
        have hQ0 : Q ≠ 0 := by
          simpa [Ψ] using hΨ.ne_zero a
        have hQdeg : Q.natDegree < (P a).natDegree := by
          apply (Polynomial.natDegree_lt_iff_degree_lt hQ0).mpr
          rw [← Polynomial.degree_eq_natDegree ha0]
          simpa [Q] using Polynomial.degree_sub_lt_left hdegree ha0 hlc.symm
        have hsumlt : (∑ j, (Ψ j).natDegree) < ∑ j, (P j).natDegree := by
          apply Finset.sum_lt_sum
          · intro j hj
            by_cases hja : j = a
            · subst j; simpa [Ψ] using hQdeg.le
            · simp [Ψ, hja]
          · exact ⟨a, Finset.mem_univ a, by simpa [Ψ] using hQdeg⟩
        have hmat : polynomialWronskianMatrix Ψ =
            (polynomialWronskianMatrix P).updateCol a
              (fun i ↦ polynomialWronskianMatrix P i a +
                (-Polynomial.C c) • polynomialWronskianMatrix P i b) := by
          ext i j
          by_cases hja : j = a
          · subst j
            simp [polynomialWronskianMatrix, Ψ, Q, Polynomial.iterate_derivative_sub,
              Polynomial.iterate_derivative_smul, sub_eq_add_neg, Polynomial.smul_eq_C_mul]
          · simp [polynomialWronskianMatrix, Ψ, hja]
        have hWr : polynomialWronskian Ψ = polynomialWronskian P := by
          rw [polynomialWronskian, polynomialWronskian, hmat]
          exact Matrix.det_updateCol_add_smul_self (polynomialWronskianMatrix P) hab
            (-Polynomial.C c)
        rw [← hWr]
        exact ih _ (hN ▸ hsumlt) Ψ hΨ (fun j ↦ hΨ.ne_zero j) rfl

/-! ### Kronecker specialization -/

private def kroneckerCode {m : ℕ} (b : ℕ) (s : Fin m →₀ ℕ) : ℕ :=
  ∑ i : Fin m, b ^ i.1 * s i

private def kroneckerMap (m b : ℕ) :
    MvPolynomial (Fin m) ℚ →ₐ[ℚ] Polynomial ℚ :=
  MvPolynomial.eval₂AlgHom ℚ (fun i : Fin m ↦ Polynomial.X ^ (b ^ i.1))

private theorem kroneckerCode_injective_of_lt {m b : ℕ} (hb : 1 < b)
    {s t : Fin m →₀ ℕ} (hs : ∀ i, s i < b) (ht : ∀ i, t i < b)
    (hcode : kroneckerCode b s = kroneckerCode b t) : s = t := by
  apply Finsupp.ext
  apply congrFun
  apply List.ofFn_inj.mp
  apply Nat.ofDigits_inj_of_len_eq hb (by simp)
  · grind
  · grind
  · simpa only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.get_ofFn,
      List.length_ofFn, Fin.val_cast, mul_comm, List.sum_ofFn, kroneckerCode] using! hcode

private theorem kroneckerMap_monomial {m b : ℕ} (s : Fin m →₀ ℕ) (a : ℚ) :
    kroneckerMap m b (MvPolynomial.monomial s a) =
      Polynomial.monomial (kroneckerCode b s) a := by
  rw [kroneckerMap, MvPolynomial.eval₂AlgHom_apply, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod_fintype s _ (fun _ ↦ pow_zero _)]
  simp_rw [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  simp [kroneckerCode, Polynomial.C_mul_X_pow_eq_monomial]

private theorem kroneckerMap_eq_zero_imp_eq_zero_of_totalDegree_le {m D : ℕ}
    (Q : MvPolynomial (Fin m) ℚ) (hdeg : Q.totalDegree ≤ D)
    (hzero : kroneckerMap m (D + 2) Q = 0) : Q = 0 := by
  by_contra hQ
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hQ
  have hdigit : ∀ {t : Fin m →₀ ℕ}, t ∈ Q.support → ∀ i, t i < D + 2 := by
    intro t ht i
    exact lt_of_le_of_lt
      ((MvPolynomial.monomial_le_degreeOf i ht).trans
        ((MvPolynomial.degreeOf_le_totalDegree Q i).trans hdeg)) (by omega)
  have hsum : kroneckerMap m (D + 2) Q =
      ∑ t ∈ Q.support,
        Polynomial.monomial (kroneckerCode (D + 2) t) (MvPolynomial.coeff t Q) := by
    nth_rw 1 [← Q.support_sum_monomial_coeff]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [kroneckerMap_monomial]
  have hc := congrArg (fun q : Polynomial ℚ ↦ q.coeff (kroneckerCode (D + 2) s)) hsum
  rw [hzero, Polynomial.coeff_zero] at hc
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial] at hc
  rw [Finset.sum_eq_single s] at hc
  · simp only [if_pos] at hc
    exact (MvPolynomial.mem_support_iff.mp hs) hc.symm
  · intro t ht hts
    have hne : kroneckerCode (D + 2) t ≠ kroneckerCode (D + 2) s := by
      intro heq
      exact hts (kroneckerCode_injective_of_lt (by omega)
        (hdigit ht) (hdigit hs) heq)
    simp [hne]
  · exact fun hnot ↦ (hnot hs).elim

private theorem kroneckerMap_linearIndependent {m r : ℕ}
    (P : Fin r → MvPolynomial (Fin m) ℚ) (hP : LinearIndependent ℚ P) :
    let D := Finset.univ.sup fun j ↦ (P j).totalDegree
    LinearIndependent ℚ (fun j ↦ kroneckerMap m (D + 2) (P j)) := by
  let D := Finset.univ.sup fun j ↦ (P j).totalDegree
  have hPD : ∀ j, (P j).totalDegree ≤ D := by
    intro j
    change (P j).totalDegree ≤ Finset.univ.sup fun j ↦ (P j).totalDegree
    exact Finset.le_sup (f := fun j : Fin r ↦ (P j).totalDegree) (Finset.mem_univ j)
  have hspan : Submodule.span ℚ (Set.range P) ≤
      MvPolynomial.restrictTotalDegree (Fin m) ℚ D := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (MvPolynomial.mem_restrictTotalDegree (Fin m) D (P j)).mpr (hPD j)
  apply hP.map_injOn (kroneckerMap m (D + 2)).toLinearMap
  intro Q hQ R hR hQR
  have hQD : Q.totalDegree ≤ D :=
    (MvPolynomial.mem_restrictTotalDegree (Fin m) D Q).mp (hspan hQ)
  have hRD : R.totalDegree ≤ D :=
    (MvPolynomial.mem_restrictTotalDegree (Fin m) D R).mp (hspan hR)
  have hsub : (Q - R).totalDegree ≤ D :=
    (MvPolynomial.totalDegree_sub Q R).trans (max_le hQD hRD)
  apply sub_eq_zero.mp
  apply kroneckerMap_eq_zero_imp_eq_zero_of_totalDegree_le (Q - R) hsub
  simpa using sub_eq_zero.mpr hQR

/-! ### Mixed derivatives and the chain rule -/

private theorem pderiv_comm {m : ℕ} (i j : Fin m) (Q : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j Q) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i Q) := by
  ext d
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := Ne.symm hij
    simp [Finsupp.single_apply, hij, hji, add_comm, add_left_comm, mul_comm]
    ring

private theorem multiDerivative_update_succ {m : ℕ} (i : Fin m) (μ : MultiIndex m)
    (Q : MvPolynomial (Fin m) ℚ) :
    multiDerivative (Function.update μ i (μ i + 1)) Q =
      MvPolynomial.pderiv i (multiDerivative μ Q) := by
  have hcomm (j : Fin m) : Function.Commute (MvPolynomial.pderiv i)
      (MvPolynomial.pderiv j) := fun Q ↦ pderiv_comm i j Q
  have hfold_eq : ∀ (l : List (Fin m)), i ∉ l →
      ∀ Q : MvPolynomial (Fin m) ℚ,
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update μ i (μ i + 1)) j] R) Q =
          l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R) Q := by
    intro l hil
    induction l with
    | nil => intro Q; rfl
    | cons j l ih =>
        intro Q
        have hji : j ≠ i := by simpa using fun h ↦ hil (by simp [h])
        have hil' : i ∉ l := fun h ↦ hil (by simp [h])
        simp only [List.foldl_cons]
        rw [show Function.update μ i (μ i + 1) j = μ j by simp [hji]]
        exact ih hil' _
  have hthrough : ∀ (l : List (Fin m)) (Q : MvPolynomial (Fin m) ℚ),
      MvPolynomial.pderiv i
          (l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R) Q) =
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R)
          (MvPolynomial.pderiv i Q) := by
    intro l
    induction l with
    | nil => intro Q; rfl
    | cons j l ih =>
        intro Q
        simp only [List.foldl_cons]
        rw [ih]
        congr 1
        exact (hcomm j).iterate_right (μ j) Q
  have hlist : ∀ (l : List (Fin m)), l.Nodup → i ∈ l →
      ∀ Q : MvPolynomial (Fin m) ℚ,
        l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update μ i (μ i + 1)) j] R) Q =
          l.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R)
            (MvPolynomial.pderiv i Q) := by
    intro l hnodup hi
    induction l with
    | nil => simp at hi
    | cons j l ih =>
        intro Q
        simp only [List.foldl_cons]
        by_cases hji : j = i
        · subst j
          simp only [Function.update_self]
          rw [Function.iterate_succ_apply]
          exact hfold_eq l hnodup.notMem _
        · have hil : i ∈ l := by simpa [Ne.symm hji] using hi
          have hnodupl : l.Nodup := hnodup.tail
          rw [show Function.update μ i (μ i + 1) j = μ j by simp [hji]]
          rw [ih hnodupl hil]
          congr 1
          exact (hcomm j).iterate_right (μ j) Q
  unfold multiDerivative
  calc
    Finset.univ.toList.foldl
        (fun R j ↦ (MvPolynomial.pderiv j)^[(Function.update μ i (μ i + 1)) j] R) Q =
      Finset.univ.toList.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R)
        (MvPolynomial.pderiv i Q) := hlist _ (Finset.nodup_toList _) (by simp) Q
    _ = MvPolynomial.pderiv i
        (Finset.univ.toList.foldl (fun R j ↦ (MvPolynomial.pderiv j)^[μ j] R) Q) :=
      (hthrough _ Q).symm

private theorem totalOrder_update_succ {m : ℕ} (i : Fin m) (μ : MultiIndex m) :
    totalOrder (Function.update μ i (μ i + 1)) = totalOrder μ + 1 := by
  rw [totalOrder, totalOrder, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)]
  omega

private def chainCoefficient {m : ℕ} (b : ℕ) (i : Fin m) : Polynomial ℚ :=
  (b ^ i.1 : ℚ) • Polynomial.X ^ (b ^ i.1 - 1)

private theorem derivative_kroneckerMap {m b : ℕ} (Q : MvPolynomial (Fin m) ℚ) :
    Polynomial.derivative (kroneckerMap m b Q) =
      ∑ i : Fin m, chainCoefficient b i *
        kroneckerMap m b (MvPolynomial.pderiv i Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [kroneckerMap, chainCoefficient]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.derivative_add, hP, hQ]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  | mul_X P j hP =>
      simp only [map_mul, MvPolynomial.eval₂AlgHom_X, Polynomial.derivative_mul,
        Polynomial.derivative_X_pow, hP, MvPolynomial.pderiv_mul,
        MvPolynomial.pderiv_X, smul_eq_mul, map_add, map_mul]
      simp [kroneckerMap, chainCoefficient, Pi.single_apply, Finset.sum_add_distrib,
        Finset.sum_mul, Finset.mul_sum, mul_add, add_mul, mul_comm, mul_left_comm]
      simp [Polynomial.derivative_X_pow, nsmul_eq_mul, smul_eq_mul]
      rw [Polynomial.smul_eq_C_mul]
      have hC : Polynomial.C (((b ^ j.1 : ℕ) : ℚ)) =
          (b : Polynomial ℚ) ^ j.1 := by
        simpa only [Nat.cast_pow] using (Polynomial.C_eq_natCast (R := ℚ) (b ^ j.1))
      have hcast : (b : ℚ) ^ j.1 = ((b ^ j.1 : ℕ) : ℚ) := by norm_num
      rw [hcast, hC]
      ring

/-! ### Iterated chain-rule expansions -/

/-- A finite expansion of an iterated derivative after Kronecker substitution.
The field `order_le` records exactly the estimate needed in the generalized
Wronskian. -/
private structure DiffExpansion (m b k : ℕ) where
  ι : Type
  fintype_ι : Fintype ι
  μ : ι → MultiIndex m
  a : ι → Polynomial ℚ
  order_le : ∀ u, totalOrder (μ u) ≤ k
  expand : ∀ Q : MvPolynomial (Fin m) ℚ,
    Polynomial.derivative^[k] (kroneckerMap m b Q) =
      ∑ u : ι, a u * kroneckerMap m b (multiDerivative (μ u) Q)

private noncomputable def DiffExpansion.zero (m b : ℕ) : DiffExpansion m b 0 :=
  { ι := PUnit
    fintype_ι := inferInstance
    μ := fun _ _ ↦ 0
    a := fun _ ↦ 1
    order_le := by intro u; simp
    expand := by intro Q; simp [kroneckerMap] }

private noncomputable def DiffExpansion.succ {m b k : ℕ}
    (E : DiffExpansion m b k) : DiffExpansion m b (k + 1) := by
  letI : Fintype E.ι := E.fintype_ι
  let nextμ : E.ι ⊕ (E.ι × Fin m) → MultiIndex m
    | Sum.inl u => E.μ u
    | Sum.inr ui => Function.update (E.μ ui.1) ui.2 (E.μ ui.1 ui.2 + 1)
  let nexta : E.ι ⊕ (E.ι × Fin m) → Polynomial ℚ
    | Sum.inl u => Polynomial.derivative (E.a u)
    | Sum.inr ui => E.a ui.1 * chainCoefficient b ui.2
  exact
    { ι := E.ι ⊕ (E.ι × Fin m)
      fintype_ι := inferInstance
      μ := nextμ
      a := nexta
      order_le := by
        intro u
        cases u with
        | inl u => exact (E.order_le u).trans (Nat.le_succ k)
        | inr ui =>
            rw [show nextμ (Sum.inr ui) =
                Function.update (E.μ ui.1) ui.2 (E.μ ui.1 ui.2 + 1) by rfl,
              totalOrder_update_succ]
            exact Nat.succ_le_succ (E.order_le ui.1)
      expand := by
        intro Q
        rw [Function.iterate_succ_apply', E.expand]
        simp only [Polynomial.derivative_sum, Polynomial.derivative_mul]
        rw [Fintype.sum_sum_type]
        simp only [nexta, nextμ]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro u hu
        rw [derivative_kroneckerMap]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [multiDerivative_update_succ]
        ring }

private noncomputable def diffExpansion (m b : ℕ) (k : ℕ) :
    DiffExpansion m b k :=
  Nat.rec (DiffExpansion.zero m b) (fun _ E ↦ E.succ) k

/-! ### The generalized-Wronskian criterion -/

/-- Rational form of the generalized-Wronskian lemma (GLR, Lemma 2.25;
Lemma 2.24 in the earlier numbering).  Row `i : Fin r` uses a mixed
derivative of total order at most `i`. -/
theorem exists_generalizedWronskian_ne_zero {m r : ℕ}
    {P : Fin r → MvPolynomial (Fin m) ℚ}
    (hP : LinearIndependent ℚ P) :
    ∃ μ : Fin r → MultiIndex m,
      (∀ i, totalOrder (μ i) ≤ i.1) ∧ generalizedWronskian μ P ≠ 0 := by
  let D := Finset.univ.sup fun j ↦ (P j).totalDegree
  let b := D + 2
  let Φ : Fin r → Polynomial ℚ := fun j ↦ kroneckerMap m b (P j)
  have hΦ : LinearIndependent ℚ Φ := by
    simpa [Φ, b, D] using kroneckerMap_linearIndependent P hP
  have hordinary : polynomialWronskian Φ ≠ 0 :=
    polynomialWronskian_ne_zero_of_linearIndependent Φ hΦ
  by_contra hnot
  push Not at hnot
  let E (i : Fin r) := diffExpansion m b i.1
  letI : ∀ i : Fin r, Fintype (E i).ι := fun i ↦ (E i).fintype_ι
  let row (i : Fin r) (u : (E i).ι) : Fin r → Polynomial ℚ :=
    fun j ↦ kroneckerMap m b (multiDerivative ((E i).μ u) (P j))
  have hrows : polynomialWronskianMatrix Φ =
      fun i ↦ ∑ u : (E i).ι, (E i).a u • row i u := by
    funext i j
    change Polynomial.derivative^[i.1] (kroneckerMap m b (P j)) = _
    rw [(E i).expand]
    simp only [Finset.sum_apply, row, Pi.smul_apply, smul_eq_mul]
  have hexpand : polynomialWronskian Φ =
      ∑ choice : ∀ i, (E i).ι,
        Matrix.det fun i j ↦ (E i).a (choice i) • row i (choice i) j := by
    rw [polynomialWronskian, hrows]
    exact (Matrix.detRowAlternating.toMultilinearMap.map_sum
      (fun i u ↦ (E i).a u • row i u))
  have hterm : ∀ choice : ∀ i, (E i).ι,
      Matrix.det (fun i j ↦ (E i).a (choice i) • row i (choice i) j) = 0 := by
    intro choice
    let μ : Fin r → MultiIndex m := fun i ↦ (E i).μ (choice i)
    have hμorder : ∀ i, totalOrder (μ i) ≤ i.1 := fun i ↦ (E i).order_le (choice i)
    have hgeneral : generalizedWronskian μ P = 0 := hnot μ hμorder
    have hspecialized : Matrix.det (fun i j ↦ row i (choice i) j) = 0 := by
      calc
        Matrix.det (fun i j ↦ row i (choice i) j) =
            kroneckerMap m b (generalizedWronskian μ P) := by
          symm
          exact (kroneckerMap m b).map_det
            (fun i j ↦ multiDerivative (μ i) (P j))
        _ = 0 := by rw [hgeneral, map_zero]
    change Matrix.detRowAlternating
      (fun i ↦ (E i).a (choice i) • row i (choice i)) = 0
    rw [AlternatingMap.map_smul_univ]
    change (∏ i, (E i).a (choice i)) •
      Matrix.det (fun i j ↦ row i (choice i) j) = 0
    rw [hspecialized, smul_zero]
  apply hordinary
  rw [hexpand]
  exact Finset.sum_eq_zero fun choice _ ↦ hterm choice

/-! ### Finite-rank separation at one variable -/

/-- A minimal-rank separation of a polynomial into a linearly independent
family in the variables `1, …, m` and a linearly independent family in
variable `0`.  The reconstruction is stated after `finSuccEquiv`, which sends
variable `0` to the outer polynomial variable. -/
structure SeparationData (m : ℕ) (P : MvPolynomial (Fin (m + 1)) ℚ) where
  k : ℕ
  left : Fin k → MvPolynomial (Fin m) ℚ
  right : Fin k → Polynomial ℚ
  left_linearIndependent : LinearIndependent ℚ left
  right_linearIndependent : LinearIndependent ℚ right
  reconstruct : MvPolynomial.finSuccEquiv ℚ m P =
    ∑ i, (right i).map MvPolynomial.C * Polynomial.C (left i)
  rank_le : k ≤ (MvPolynomial.finSuccEquiv ℚ m P).natDegree + 1

/-- Every polynomial admits a separation whose two factor families are both
linearly independent and whose length is at most one more than its degree in
the distinguished variable. -/
theorem exists_separationData {m : ℕ}
    (P : MvPolynomial (Fin (m + 1)) ℚ) : Nonempty (SeparationData m P) := by
  let q : Polynomial (MvPolynomial (Fin m) ℚ) :=
    MvPolynomial.finSuccEquiv ℚ m P
  let s : Finset (MvPolynomial (Fin m) ℚ) := q.support.image q.coeff
  let V : Submodule ℚ (MvPolynomial (Fin m) ℚ) :=
    Submodule.span ℚ (s : Set (MvPolynomial (Fin m) ℚ))
  letI : FiniteDimensional ℚ V := FiniteDimensional.span_finset ℚ s
  let B : Module.Basis (Fin (Module.finrank ℚ V)) ℚ V := Module.finBasis ℚ V
  have hcoeffV (n : ℕ) : q.coeff n ∈ V := by
    by_cases hn : n ∈ q.support
    · apply Submodule.subset_span
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact V.zero_mem
  let c (n : ℕ) : V := ⟨q.coeff n, hcoeffV n⟩
  let left : Fin (Module.finrank ℚ V) → MvPolynomial (Fin m) ℚ :=
    fun i ↦ B i
  let right : Fin (Module.finrank ℚ V) → Polynomial ℚ := fun i ↦
    ∑ n ∈ q.support, Polynomial.monomial n ((B.repr (c n)) i)
  have hleft : LinearIndependent ℚ left := by
    exact B.linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  have hrightCoeff (i : Fin (Module.finrank ℚ V)) (n : ℕ) :
      (right i).coeff n = if n ∈ q.support then (B.repr (c n)) i else 0 := by
    classical
    by_cases hn : n ∈ q.support
    · rw [if_pos hn]
      simp only [right, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single n]
      · simp
      · intro a ha han
        simp [han]
      · exact fun h ↦ (h hn).elim
    · rw [if_neg hn]
      simp only [right, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      apply Finset.sum_eq_zero
      intro a ha
      have han : a ≠ n := fun h ↦ hn (h ▸ ha)
      simp [han]
  have hrepr (n : ℕ) :
      ∑ i, (B.repr (c n)) i • left i = q.coeff n := by
    simp only [left]
    change (∑ i, (B.repr (c n)) i • (B i : MvPolynomial (Fin m) ℚ)) =
      (c n : MvPolynomial (Fin m) ℚ)
    simpa only [map_sum, map_smul, Submodule.coe_subtype] using
      congrArg V.subtype (B.sum_repr (c n))
  have hright : LinearIndependent ℚ right := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let L : V →ₗ[ℚ] ℚ :=
      { toFun := fun v ↦ ∑ j, g j * (B.repr v) j
        map_add' := by
          intro x y
          simp only [map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro a x
          simp only [map_smul, Finsupp.smul_apply, RingHom.id_apply, smul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring }
    have hLcoeff (n : ℕ) (hn : n ∈ q.support) : L (c n) = 0 := by
      have h := congrArg (fun f : Polynomial ℚ ↦ f.coeff n) hg
      simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_zero,
        Polynomial.coeff_smul] at h
      change (∑ j, g j * (B.repr (c n)) j) = 0
      simpa [hrightCoeff, hn, smul_eq_mul] using h
    have hLzero (v : V) : L v = 0 := by
      refine Submodule.span_induction (p := fun x hx ↦ L ⟨x, hx⟩ = 0) ?_ ?_ ?_ ?_
        v.property
      · intro x hx
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact hLcoeff n hn
      · exact L.map_zero
      · intro x y hx hy hzx hzy
        change L (⟨x, hx⟩ + ⟨y, hy⟩) = 0
        rw [map_add, hzx, hzy, add_zero]
      · intro a x hx hzx
        change L (a • ⟨x, hx⟩) = 0
        rw [map_smul, hzx, smul_zero]
    have hi := hLzero (B i)
    change (∑ j, g j * (B.repr (B i)) j) = 0 at hi
    rw [B.repr_self] at hi
    simpa [Finsupp.single_apply, eq_comm] using hi
  have hreconstruct : q =
      ∑ i, (right i).map MvPolynomial.C * Polynomial.C (left i) := by
    apply Polynomial.ext
    intro n
    by_cases hn : n ∈ q.support
    · simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map,
        RingHom.coe_coe, Function.comp_apply, hrightCoeff, if_pos hn]
      simpa only [MvPolynomial.smul_eq_C_mul] using (hrepr n).symm
    · have hqn : q.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
      rw [hqn]
      simp [Polynomial.finsetSum_coeff, hrightCoeff, hn]
  refine ⟨{
    k := Module.finrank ℚ V
    left := left
    right := right
    left_linearIndependent := hleft
    right_linearIndependent := hright
    reconstruct := ?_
    rank_le := ?_ }⟩
  · exact hreconstruct
  · calc
      Module.finrank ℚ V ≤ s.card := finrank_span_finset_le_card s
      _ ≤ q.support.card := Finset.card_image_le
      _ ≤ q.natDegree + 1 := Polynomial.card_supp_le_succ_natDegree q

/-! ### Wronskians of a separation -/

/-- The ordinary univariate Wronskian, with derivative orders `0, …, k-1`. -/
def univariateWronskian {k : ℕ} (f : Fin k → Polynomial ℚ) : Polynomial ℚ :=
  Matrix.det fun i j ↦ Polynomial.derivative^[i.1] (f j)

/-- A linearly independent rational polynomial family has nonzero ordinary
Wronskian. -/
theorem univariateWronskian_ne_zero_of_linearIndependent {k : ℕ}
    {f : Fin k → Polynomial ℚ} (hf : LinearIndependent ℚ f) :
    univariateWronskian f ≠ 0 := by
  exact polynomialWronskian_ne_zero_of_linearIndependent f hf

/-- The separated mixed-derivative matrix.  Row `a` differentiates the left
factor by `μ a`; column `b` differentiates the right factor `b` times. -/
def separatedDerivativeMatrix {m : ℕ} {P : MvPolynomial (Fin (m + 1)) ℚ}
    (S : SeparationData m P) (μ : Fin S.k → MultiIndex m) :
    Matrix (Fin S.k) (Fin S.k) (Polynomial (MvPolynomial (Fin m) ℚ)) :=
  fun a b ↦ ∑ j,
    ((Polynomial.derivative^[b.1] (S.right j)).map MvPolynomial.C) *
      Polynomial.C (multiDerivative (μ a) (S.left j))

/-- The separated mixed-derivative determinant factors as the generalized
Wronskian of the left factors times the ordinary Wronskian of the right
factors. -/
theorem separatedDerivativeMatrix_det {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} (S : SeparationData m P)
    (μ : Fin S.k → MultiIndex m) :
    (separatedDerivativeMatrix S μ).det =
      Polynomial.C (generalizedWronskian μ S.left) *
        (univariateWronskian S.right).map MvPolynomial.C := by
  let L : Matrix (Fin S.k) (Fin S.k) (Polynomial (MvPolynomial (Fin m) ℚ)) :=
    fun a j ↦ Polynomial.C (multiDerivative (μ a) (S.left j))
  let R : Matrix (Fin S.k) (Fin S.k) (Polynomial (MvPolynomial (Fin m) ℚ)) :=
    fun j b ↦ (Polynomial.derivative^[b.1] (S.right j)).map MvPolynomial.C
  have hmatrix : separatedDerivativeMatrix S μ = L * R := by
    funext a b
    simp only [separatedDerivativeMatrix, Matrix.mul_apply, L, R]
    apply Finset.sum_congr rfl
    intro j hj
    rw [mul_comm]
  have hleft : L.det = Polynomial.C (generalizedWronskian μ S.left) := by
    symm
    exact (Polynomial.C : MvPolynomial (Fin m) ℚ →+*
      Polynomial (MvPolynomial (Fin m) ℚ)).map_det
        (fun a j ↦ multiDerivative (μ a) (S.left j))
  have hright : R.det = (univariateWronskian S.right).map MvPolynomial.C := by
    let W : Matrix (Fin S.k) (Fin S.k) (Polynomial ℚ) :=
      fun b j ↦ Polynomial.derivative^[b.1] (S.right j)
    let f : Polynomial ℚ →+* Polynomial (MvPolynomial (Fin m) ℚ) :=
      Polynomial.mapRingHom MvPolynomial.C
    calc
      R.det = (R.transpose).det := (Matrix.det_transpose R).symm
      _ = (f.mapMatrix W).det := by
        congr 1
      _ = f W.det := by
        exact (f.map_det W).symm
      _ = (univariateWronskian S.right).map MvPolynomial.C := rfl
  rw [hmatrix, Matrix.det_mul, hleft, hright]

/-- A separation admits controlled left derivative rows for which both
Wronskian factors, and hence the separated mixed determinant, are nonzero. -/
theorem SeparationData.exists_wronskian_factorization {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} (S : SeparationData m P) :
    ∃ μ : Fin S.k → MultiIndex m,
      (∀ i, totalOrder (μ i) ≤ i.1) ∧
      generalizedWronskian μ S.left ≠ 0 ∧
      univariateWronskian S.right ≠ 0 ∧
      (separatedDerivativeMatrix S μ).det =
        Polynomial.C (generalizedWronskian μ S.left) *
          (univariateWronskian S.right).map MvPolynomial.C ∧
      (separatedDerivativeMatrix S μ).det ≠ 0 := by
  obtain ⟨μ, hμ, hleft⟩ :=
    exists_generalizedWronskian_ne_zero S.left_linearIndependent
  have hright :=
    univariateWronskian_ne_zero_of_linearIndependent S.right_linearIndependent
  refine ⟨μ, hμ, hleft, hright, separatedDerivativeMatrix_det S μ, ?_⟩
  rw [separatedDerivativeMatrix_det]
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr hleft
  · intro hz
    apply hright
    apply Polynomial.map_injective MvPolynomial.C
      (MvPolynomial.C_injective (Fin m) ℚ)
    simpa using hz

/-! ### Transport back through `finSuccEquiv` -/

/-- Extend a multi-index on the last `m` variables by zero in coordinate
`0`. -/
def liftMultiIndex {m : ℕ} (μ : MultiIndex m) : MultiIndex (m + 1) :=
  Fin.cases 0 μ

private theorem finSuccEquiv_pderiv_zero {m : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℚ) :
    MvPolynomial.finSuccEquiv ℚ m (MvPolynomial.pderiv 0 Q) =
      Polynomial.derivative (MvPolynomial.finSuccEquiv ℚ m Q) := by
  apply Polynomial.ext
  intro n
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_pderiv,
    Polynomial.coeff_derivative]
  rw [mul_comm ((MvPolynomial.finSuccEquiv ℚ m Q).coeff (n + 1))]
  have hscalar : ((n : MvPolynomial (Fin m) ℚ) + 1) =
      MvPolynomial.C ((n + 1 : ℕ) : ℚ) := by norm_num
  rw [hscalar]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.finSuccEquiv_coeff_coeff]
  have hindex : d.cons n + Finsupp.single (0 : Fin (m + 1)) 1 =
      d.cons (n + 1) := by
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · simp
    · simp
  rw [hindex]
  simp [mul_comm]

private theorem finSuccEquiv_pderiv_succ_coeff {m : ℕ} (i : Fin m)
    (Q : MvPolynomial (Fin (m + 1)) ℚ) (n : ℕ) :
    (MvPolynomial.finSuccEquiv ℚ m (MvPolynomial.pderiv i.succ Q)).coeff n =
      MvPolynomial.pderiv i ((MvPolynomial.finSuccEquiv ℚ m Q).coeff n) := by
  apply MvPolynomial.ext
  intro d
  rw [MvPolynomial.finSuccEquiv_coeff_coeff, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv, MvPolynomial.finSuccEquiv_coeff_coeff]
  have hindex : d.cons n + Finsupp.single i.succ 1 =
      (d + Finsupp.single i 1).cons n := by
    ext j
    refine Fin.cases ?_ (fun h ↦ ?_) j
    · simp
    · simp [Finsupp.single_apply]
  rw [hindex]
  simp

private theorem finSuccEquiv_iterate_pderiv_zero {m n : ℕ}
    (Q : MvPolynomial (Fin (m + 1)) ℚ) :
    MvPolynomial.finSuccEquiv ℚ m ((MvPolynomial.pderiv 0)^[n] Q) =
      Polynomial.derivative^[n] (MvPolynomial.finSuccEquiv ℚ m Q) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        finSuccEquiv_pderiv_zero, ih]

private theorem finSuccEquiv_multiDerivative_coeff {m : ℕ}
    (μ : MultiIndex m) (Q : MvPolynomial (Fin (m + 1)) ℚ) (n : ℕ) :
    (MvPolynomial.finSuccEquiv ℚ m
      (multiDerivative (liftMultiIndex μ) Q)).coeff n =
      multiDerivative μ ((MvPolynomial.finSuccEquiv ℚ m Q).coeff n) := by
  generalize hN : totalOrder μ = N
  induction N using Nat.strong_induction_on generalizing μ Q with
  | h N ih =>
      by_cases hμzero : μ = fun _ ↦ 0
      · subst μ
        have hliftzero : liftMultiIndex (fun _ : Fin m ↦ 0) =
            (fun _ : Fin (m + 1) ↦ 0) := by
          funext j
          exact Fin.cases rfl (fun _ ↦ rfl) j
        rw [hliftzero, multiDerivative_zero_index, multiDerivative_zero_index]
      · have hex : ∃ i : Fin m, 0 < μ i := by
          by_contra h
          push Not at h
          apply hμzero
          funext i
          exact Nat.eq_zero_of_le_zero (h i)
        obtain ⟨i, hi⟩ := hex
        let ν : MultiIndex m := Function.update μ i (μ i - 1)
        have hνi : ν i + 1 = μ i := by
          simp [ν, Nat.sub_add_cancel hi]
        have hupdate : Function.update ν i (ν i + 1) = μ := by
          funext j
          by_cases hji : j = i
          · subst j
            simp [hνi]
          · simp [ν, hji]
        have hliftupdate : liftMultiIndex μ =
            Function.update (liftMultiIndex ν) i.succ
              (liftMultiIndex ν i.succ + 1) := by
          rw [← hupdate]
          funext j
          refine Fin.cases ?_ (fun t ↦ ?_) j
          · symm
            simpa [liftMultiIndex] using
              (Function.update_of_ne (Fin.succ_ne_zero i).symm
                (liftMultiIndex ν i.succ + 1) (liftMultiIndex ν))
          · by_cases hti : t = i
            · subst t
              simp [liftMultiIndex]
            · simp [liftMultiIndex, hti]
        have horderν : totalOrder ν + 1 = N := by
          rw [← totalOrder_update_succ i ν, hupdate, hN]
        have hlt : totalOrder ν < N := by omega
        calc
          (MvPolynomial.finSuccEquiv ℚ m
              (multiDerivative (liftMultiIndex μ) Q)).coeff n =
              (MvPolynomial.finSuccEquiv ℚ m
                (MvPolynomial.pderiv i.succ
                  (multiDerivative (liftMultiIndex ν) Q))).coeff n := by
                    rw [hliftupdate, multiDerivative_update_succ]
          _ = MvPolynomial.pderiv i
              ((MvPolynomial.finSuccEquiv ℚ m
                (multiDerivative (liftMultiIndex ν) Q)).coeff n) :=
                finSuccEquiv_pderiv_succ_coeff i _ n
          _ = MvPolynomial.pderiv i
              (multiDerivative ν
                ((MvPolynomial.finSuccEquiv ℚ m Q).coeff n)) := by
                rw [ih (totalOrder ν) hlt ν Q rfl]
          _ = multiDerivative μ
              ((MvPolynomial.finSuccEquiv ℚ m Q).coeff n) := by
                rw [← multiDerivative_update_succ, hupdate]

/-- The actual mixed-derivative matrix in the original `m+1` variables:
columns differentiate coordinate `0`, and rows differentiate only the
remaining coordinates. -/
def mixedDerivativeMatrix {m : ℕ} {P : MvPolynomial (Fin (m + 1)) ℚ}
    (S : SeparationData m P) (μ : Fin S.k → MultiIndex m) :
    Matrix (Fin S.k) (Fin S.k) (MvPolynomial (Fin (m + 1)) ℚ) :=
  fun a b ↦ multiDerivative (liftMultiIndex (μ a))
    ((MvPolynomial.pderiv 0)^[b.1] P)

/-- Entrywise transport of the actual mixed-derivative matrix through
`finSuccEquiv`. -/
theorem SeparationData.finSuccEquiv_mixedDerivativeMatrix_entry {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} (S : SeparationData m P)
    (μ : Fin S.k → MultiIndex m) (a b : Fin S.k) :
    MvPolynomial.finSuccEquiv ℚ m (mixedDerivativeMatrix S μ a b) =
      separatedDerivativeMatrix S μ a b := by
  have hderivative :
      Polynomial.derivative^[b.1] (MvPolynomial.finSuccEquiv ℚ m P) =
        ∑ j,
          ((Polynomial.derivative^[b.1] (S.right j)).map MvPolynomial.C) *
            Polynomial.C (S.left j) := by
    rw [S.reconstruct, Polynomial.iterate_derivative_sum]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      Polynomial.derivative^[b.1]
          ((S.right j).map MvPolynomial.C * Polynomial.C (S.left j)) =
          Polynomial.derivative^[b.1]
            (Polynomial.C (S.left j) * (S.right j).map MvPolynomial.C) := by
              rw [mul_comm]
      _ = Polynomial.C (S.left j) *
          Polynomial.derivative^[b.1] ((S.right j).map MvPolynomial.C) :=
            Polynomial.iterate_derivative_C_mul _ _ _
      _ = Polynomial.C (S.left j) *
          (Polynomial.derivative^[b.1] (S.right j)).map MvPolynomial.C := by
            rw [Polynomial.iterate_derivative_map]
      _ = (Polynomial.derivative^[b.1] (S.right j)).map MvPolynomial.C *
          Polynomial.C (S.left j) := by rw [mul_comm]
  apply Polynomial.ext
  intro n
  change (MvPolynomial.finSuccEquiv ℚ m
    (multiDerivative (liftMultiIndex (μ a))
      ((MvPolynomial.pderiv 0)^[b.1] P))).coeff n = _
  rw [finSuccEquiv_multiDerivative_coeff,
    finSuccEquiv_iterate_pderiv_zero, hderivative]
  simp only [mixedDerivativeMatrix, separatedDerivativeMatrix,
    Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    MvPolynomial.C_mul', multiDerivative_finsetSum, multiDerivative_smul]

/-- Mapping the determinant of the actual mixed-derivative matrix through
`finSuccEquiv` gives the separated determinant. -/
theorem SeparationData.finSuccEquiv_mixedDerivativeMatrix_det {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} (S : SeparationData m P)
    (μ : Fin S.k → MultiIndex m) :
    MvPolynomial.finSuccEquiv ℚ m (mixedDerivativeMatrix S μ).det =
      (separatedDerivativeMatrix S μ).det := by
  calc
    MvPolynomial.finSuccEquiv ℚ m (mixedDerivativeMatrix S μ).det =
        Matrix.det ((MvPolynomial.finSuccEquiv ℚ m).mapMatrix
          (mixedDerivativeMatrix S μ)) :=
      (MvPolynomial.finSuccEquiv ℚ m).map_det (mixedDerivativeMatrix S μ)
    _ = (separatedDerivativeMatrix S μ).det := by
      congr 1
      funext a b
      exact S.finSuccEquiv_mixedDerivativeMatrix_entry μ a b

/-- Controlled derivative rows giving a nonzero actual mixed-derivative
determinant, together with its explicit factorization after `finSuccEquiv`. -/
theorem SeparationData.exists_mixedDerivativeMatrix_ne_zero {m : ℕ}
    {P : MvPolynomial (Fin (m + 1)) ℚ} (S : SeparationData m P) :
    ∃ μ : Fin S.k → MultiIndex m,
      (∀ i, totalOrder (μ i) ≤ i.1) ∧
      (mixedDerivativeMatrix S μ).det ≠ 0 ∧
      MvPolynomial.finSuccEquiv ℚ m (mixedDerivativeMatrix S μ).det =
        Polynomial.C (generalizedWronskian μ S.left) *
          (univariateWronskian S.right).map MvPolynomial.C := by
  obtain ⟨μ, hμ, hleft, hright, hfactor, hsep⟩ :=
    S.exists_wronskian_factorization
  refine ⟨μ, hμ, ?_, ?_⟩
  · intro hzero
    apply hsep
    rw [← S.finSuccEquiv_mixedDerivativeMatrix_det μ, hzero, map_zero]
  · rw [S.finSuccEquiv_mixedDerivativeMatrix_det μ, hfactor]

end

end Erdos407.GeneralizedWronskian
