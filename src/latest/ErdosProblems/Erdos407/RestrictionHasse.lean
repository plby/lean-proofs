/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos407.RestrictionIndex
import ErdosProblems.Erdos407.SymmetricPower

/-!
# Hasse derivatives of an adapted hyperplane slice

The explicit restricted divided derivative retains exactly the monomials
whose pivot exponents equal a prescribed normal order and then deletes
those pivot powers.  At a point where every pivot coordinate is zero,
taking a tangential Hasse derivative of this slice is therefore exactly the
same as taking the combined tangential-plus-normal derivative of the
original adapted polynomial.
-/

namespace Erdos407.RestrictionHasse

open scoped BigOperators

noncomputable section

open Erdos407.GeneralizedRoth

private theorem hasseDerivative_sum {ι κ : Type*} [Fintype ι]
    (A : ι →₀ ℕ) (s : Finset κ) (P : κ → MvPolynomial ι ℚ) :
    SymmetricPower.hasseDerivative A (∑ k ∈ s, P k) =
      ∑ k ∈ s, SymmetricPower.hasseDerivative A (P k) := by
  simp [SymmetricPower.hasseDerivative, map_sum, MvPolynomial.coeff_sum]

private theorem eval_hasseDerivative_monomial {m n : ℕ}
    (A e : RothIndex.MultiIndex m n) (c : ℚ)
    (a : RothIndex.BlockVar m n → ℚ) :
    MvPolynomial.eval a
        (SymmetricPower.hasseDerivative A (MvPolynomial.monomial e c)) =
      c * (∏ x, (Nat.choose (e x) (A x) : ℚ)) *
        (e - A).prod fun x k ↦ a x ^ k := by
  rw [SymmetricPower.hasseDerivative_monomial]
  rw [MvPolynomial.eval_monomial]

private theorem tangential_sub_eq_sub_add_normal
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A e : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (heN : RestrictionIndex.normalOrderOfExponent M hM e = N) :
    RestrictionIndex.tangentialExponent M hM e - A =
      e - (A + RestrictionIndex.normalMultiIndex M hM N) := by
  ext v
  rcases v with ⟨j, k⟩
  by_cases hk : k = pivotIndex (M j) (hM j)
  · subst k
    have hep : e (j, pivotIndex (M j) (hM j)) = N j := by
      exact congrFun heN j
    simp [RestrictionIndex.tangentialExponent, hA j, hep]
  · simp [RestrictionIndex.tangentialExponent,
      RestrictionIndex.normalMultiIndex, hk]

private theorem choose_prod_tangential_eq_add_normal
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A e : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (heN : RestrictionIndex.normalOrderOfExponent M hM e = N) :
    (∏ x, (Nat.choose
        (RestrictionIndex.tangentialExponent M hM e x) (A x) : ℚ)) =
      ∏ x, (Nat.choose (e x)
        ((A + RestrictionIndex.normalMultiIndex M hM N) x) : ℚ) := by
  classical
  apply Finset.prod_congr rfl
  intro v hv
  rcases v with ⟨j, k⟩
  by_cases hk : k = pivotIndex (M j) (hM j)
  · subst k
    have hep : e (j, pivotIndex (M j) (hM j)) = N j :=
      congrFun heN j
    simp [RestrictionIndex.tangentialExponent, hA j, hep]
  · simp [RestrictionIndex.tangentialExponent,
      RestrictionIndex.normalMultiIndex, hk]

private theorem eval_hasseDerivative_monomial_eq_of_normalOrder
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A e : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (heN : RestrictionIndex.normalOrderOfExponent M hM e = N)
    (c : ℚ) (a : RothIndex.BlockVar m n → ℚ) :
    MvPolynomial.eval a
        (SymmetricPower.hasseDerivative A
          (MvPolynomial.monomial
            (RestrictionIndex.tangentialExponent M hM e) c)) =
      MvPolynomial.eval a
        (SymmetricPower.hasseDerivative
          (A + RestrictionIndex.normalMultiIndex M hM N)
          (MvPolynomial.monomial e c)) := by
  rw [eval_hasseDerivative_monomial, eval_hasseDerivative_monomial]
  rw [choose_prod_tangential_eq_add_normal M hM N A e hA heN,
    tangential_sub_eq_sub_add_normal M hM N A e hA heN]

private theorem eval_hasseDerivative_monomial_eq_zero_of_normalOrder_ne
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A e : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (a : RothIndex.BlockVar m n → ℚ)
    (ha : ∀ j, a (j, pivotIndex (M j) (hM j)) = 0)
    (hne : RestrictionIndex.normalOrderOfExponent M hM e ≠ N)
    (c : ℚ) :
    MvPolynomial.eval a
        (SymmetricPower.hasseDerivative
          (A + RestrictionIndex.normalMultiIndex M hM N)
          (MvPolynomial.monomial e c)) = 0 := by
  have hex : ∃ j, e (j, pivotIndex (M j) (hM j)) ≠ N j := by
    contrapose! hne
    exact funext hne
  obtain ⟨j, hj⟩ := hex
  let p : RothIndex.BlockVar m n :=
    (j, pivotIndex (M j) (hM j))
  have hAp : A p = 0 := hA j
  have hnormalp : RestrictionIndex.normalMultiIndex M hM N p = N j := by
    simp [p]
  rw [eval_hasseDerivative_monomial]
  rcases Nat.lt_or_gt_of_ne hj with hjlt | hjgt
  · have hchoose :
        (∏ x, (Nat.choose (e x)
          ((A + RestrictionIndex.normalMultiIndex M hM N) x) : ℚ)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      rw [show (A + RestrictionIndex.normalMultiIndex M hM N) p = N j by
        simp [hAp, hnormalp]]
      rw [Nat.choose_eq_zero_of_lt hjlt]
      norm_num
    rw [hchoose, mul_zero, zero_mul]
  · have hsubp :
        (e - (A + RestrictionIndex.normalMultiIndex M hM N)) p =
          e p - N j := by
      simp [hAp, hnormalp]
    have hprod :
        (e - (A + RestrictionIndex.normalMultiIndex M hM N)).prod
            (fun x k ↦ a x ^ k) = 0 := by
      rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
      apply Finset.prod_eq_zero (Finset.mem_univ p)
      rw [hsubp, ha j, zero_pow]
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt hjgt)
    rw [hprod, mul_zero]

private theorem sum_eval_hasseDerivative_slice_eq
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (a : RothIndex.BlockVar m n → ℚ)
    (ha : ∀ j, a (j, pivotIndex (M j) (hM j)) = 0)
    (s : Finset (RothIndex.MultiIndex m n))
    (c : RothIndex.MultiIndex m n → ℚ) :
    (∑ e ∈ s.filter
        (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N),
      MvPolynomial.eval a
        (SymmetricPower.hasseDerivative A
          (MvPolynomial.monomial
            (RestrictionIndex.tangentialExponent M hM e) (c e)))) =
      ∑ e ∈ s, MvPolynomial.eval a
        (SymmetricPower.hasseDerivative
          (A + RestrictionIndex.normalMultiIndex M hM N)
          (MvPolynomial.monomial e (c e))) := by
  classical
  let f := fun e : RothIndex.MultiIndex m n ↦
    MvPolynomial.eval a
      (SymmetricPower.hasseDerivative A
        (MvPolynomial.monomial
          (RestrictionIndex.tangentialExponent M hM e) (c e)))
  let g := fun e : RothIndex.MultiIndex m n ↦
    MvPolynomial.eval a
      (SymmetricPower.hasseDerivative
        (A + RestrictionIndex.normalMultiIndex M hM N)
        (MvPolynomial.monomial e (c e)))
  change (∑ e ∈ s.filter
      (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N), f e) =
    ∑ e ∈ s, g e
  calc
    (∑ e ∈ s.filter
        (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N), f e) =
      ∑ e ∈ s.filter
        (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N), g e := by
      apply Finset.sum_congr rfl
      intro e he
      change MvPolynomial.eval a
          (SymmetricPower.hasseDerivative A
            (MvPolynomial.monomial
              (RestrictionIndex.tangentialExponent M hM e) (c e))) =
        MvPolynomial.eval a
          (SymmetricPower.hasseDerivative
            (A + RestrictionIndex.normalMultiIndex M hM N)
            (MvPolynomial.monomial e (c e)))
      exact eval_hasseDerivative_monomial_eq_of_normalOrder
        M hM N A e hA (Finset.mem_filter.mp he).2 _ a
    _ = ∑ e ∈ s, g e := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro e he hnot
      have hne : RestrictionIndex.normalOrderOfExponent M hM e ≠ N := by
        simpa [he] using hnot
      change MvPolynomial.eval a
          (SymmetricPower.hasseDerivative
            (A + RestrictionIndex.normalMultiIndex M hM N)
            (MvPolynomial.monomial e (c e))) = 0
      exact eval_hasseDerivative_monomial_eq_zero_of_normalOrder_ne
        M hM N A e hA a ha hne _

/-- A tangential Hasse derivative of the explicit normal slice equals the
combined tangential-plus-normal Hasse derivative of the original adapted
polynomial when evaluated at a zero-normal point. -/
theorem eval_hasseDerivative_restrictedDividedDerivativeInAdaptedCoordinates
    {m n : ℕ} (M : FormFamily m n) (hM : ∀ j, M j ≠ 0)
    (Q : MvPolynomial (RothIndex.BlockVar m n) ℚ)
    (N : RestrictionIndex.NormalOrder m)
    (A : RothIndex.MultiIndex m n)
    (hA : ∀ j, A (j, pivotIndex (M j) (hM j)) = 0)
    (a : RothIndex.BlockVar m n → ℚ)
    (ha : ∀ j, a (j, pivotIndex (M j) (hM j)) = 0) :
    MvPolynomial.eval a
        (SymmetricPower.hasseDerivative A
          (RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
            M hM Q N)) =
      MvPolynomial.eval a
        (SymmetricPower.hasseDerivative
          (A + RestrictionIndex.normalMultiIndex M hM N) Q) := by
  classical
  have hleft :
      MvPolynomial.eval a
          (SymmetricPower.hasseDerivative A
            (RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
              M hM Q N)) =
        ∑ e ∈ Q.support.filter
            (fun e ↦ RestrictionIndex.normalOrderOfExponent M hM e = N),
          MvPolynomial.eval a
            (SymmetricPower.hasseDerivative A
              (MvPolynomial.monomial
                (RestrictionIndex.tangentialExponent M hM e)
                (MvPolynomial.coeff e Q))) := by
    unfold RestrictionIndex.restrictedDividedDerivativeInAdaptedCoordinates
    rw [hasseDerivative_sum]
    simp only [map_sum]
  have hright :
      MvPolynomial.eval a
          (SymmetricPower.hasseDerivative
            (A + RestrictionIndex.normalMultiIndex M hM N) Q) =
        ∑ e ∈ Q.support,
          MvPolynomial.eval a
            (SymmetricPower.hasseDerivative
              (A + RestrictionIndex.normalMultiIndex M hM N)
              (MvPolynomial.monomial e (MvPolynomial.coeff e Q))) := by
    conv_lhs =>
      rhs
      rw [MvPolynomial.as_sum Q]
    rw [hasseDerivative_sum]
    simp only [map_sum]
  exact hleft.trans
    ((sum_eval_hasseDerivative_slice_eq M hM N A hA a ha
      Q.support (fun e ↦ MvPolynomial.coeff e Q)).trans hright.symm)

end

end Erdos407.RestrictionHasse
