/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovParameters

/-!
# Linear kernel for the rational Stepanov auxiliary polynomial

On a trace fiber, a high rational monomial of homogeneous denominator degree
`p-1` reduces to a polynomial in the low numerator and denominator.  This
file imposes the resulting low Hasse identities and obtains a nonzero family
of auxiliary coefficients from the strict parameter count.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators
open Waring.Analytic.Stepanov

namespace RationalStepanov

/-- One denominator-cleared reduced Hasse term. -/
noncomputable def rationalReducedTerm
    {E : Type*} [CommRing E] (p h : ℕ) (c pole : E)
    (r i k : ℕ) (e lowN lowD : E[X]) : E[X] :=
  ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
      lowD ^ (p - 1 - i)) * (X - C pole) ^ k

/-- Every reduced rational condition has degree below the declared bound. -/
theorem natDegree_rationalReducedTerm_lt
    {E : Type*} [CommRing E] {p h s r i k : ℕ}
    (hp : 0 < p) (c pole : E) {e lowN lowD : E[X]}
    (he : e.natDegree < S p h)
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hi : i < p) (hk : k ≤ K p h) :
    (rationalReducedTerm p h c pole r i k e lowN lowD).natDegree <
      rationalConditionDegree p h s := by
  let L := s * frobeniusOrderSum p (h + 3)
  have hW : (C c * lowD - lowN).natDegree ≤ L := by
    exact (natDegree_sub_le _ _).trans <| by
      apply max_le
      · exact (natDegree_C_mul_le _ _).trans hD
      · exact hN
  have hderiv : (hasseDeriv r e).natDegree ≤ e.natDegree :=
    (natDegree_hasseDeriv_le e r).trans (Nat.sub_le _ _)
  have hWi : ((C c * lowD - lowN) ^ i).natDegree ≤ i * L :=
    natDegree_pow_le_of_le i hW
  have hDp : (lowD ^ (p - 1 - i)).natDegree ≤ (p - 1 - i) * L :=
    natDegree_pow_le_of_le _ hD
  have hcenter : ((X - C pole) ^ k : E[X]).natDegree ≤ k := by
    calc
      ((X - C pole) ^ k : E[X]).natDegree ≤
          k * (X - C pole : E[X]).natDegree := natDegree_pow_le
      _ ≤ k * 1 := Nat.mul_le_mul_left k (natDegree_X_sub_C_le pole)
      _ = k := Nat.mul_one k
  have hdegree :
      (rationalReducedTerm p h c pole r i k e lowN lowD).natDegree ≤
        e.natDegree + i * L + (p - 1 - i) * L + k := by
    unfold rationalReducedTerm
    calc
      (((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
          lowD ^ (p - 1 - i)) * (X - C pole) ^ k).natDegree ≤
          ((hasseDeriv r e).natDegree +
            ((C c * lowD - lowN) ^ i).natDegree) +
              (lowD ^ (p - 1 - i)).natDegree +
                ((X - C pole) ^ k).natDegree := by
        have hmul1 :
            (hasseDeriv r e * (C c * lowD - lowN) ^ i).natDegree ≤
              (hasseDeriv r e).natDegree +
                ((C c * lowD - lowN) ^ i).natDegree := natDegree_mul_le
        have hmul2 :
            ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
              lowD ^ (p - 1 - i)).natDegree ≤
              (hasseDeriv r e * (C c * lowD - lowN) ^ i).natDegree +
                (lowD ^ (p - 1 - i)).natDegree := natDegree_mul_le
        have hmul3 :
            (((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
              lowD ^ (p - 1 - i)) * (X - C pole) ^ k).natDegree ≤
              ((hasseDeriv r e * (C c * lowD - lowN) ^ i) *
                lowD ^ (p - 1 - i)).natDegree +
                  ((X - C pole) ^ k).natDegree := natDegree_mul_le
        omega
      _ ≤ e.natDegree + i * L + (p - 1 - i) * L + k := by
        omega
  have hi' : i ≤ p - 1 := by omega
  have hphase :
      i * L + (p - 1 - i) * L = rationalPhaseAllowance p h s := by
    unfold rationalPhaseAllowance L
    rw [← Nat.add_mul, Nat.add_sub_of_le hi']
    ring
  unfold rationalConditionDegree
  rw [← hphase]
  omega

/-- Scalar coordinates of all reduced rational derivative conditions. -/
abbrev RationalAuxiliaryConditions (E : Type*) (p h s : ℕ) :=
  Fin (R p h) → Fin (rationalConditionDegree p h s) → E

/-- Sum of all reduced terms for one Hasse derivative order. -/
noncomputable def rationalReducedConditionPolynomial
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (a : AuxiliaryCoefficients E p h) : E[X] :=
  ∑ i : Fin p, ∑ k : Fin (K p h + 1),
    rationalReducedTerm p h c pole r i k
      (auxiliaryCoefficientPolynomial a i k) lowN lowD

private theorem auxiliaryCoefficientPolynomial_add
    {E : Type*} [Field E] {p h : ℕ}
    (a b : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (a + b) i k =
      auxiliaryCoefficientPolynomial a i k +
        auxiliaryCoefficientPolynomial b i k := by
  simp [auxiliaryCoefficientPolynomial]

private theorem auxiliaryCoefficientPolynomial_smul
    {E : Type*} [Field E] {p h : ℕ} (z : E)
    (a : AuxiliaryCoefficients E p h) (i : Fin p)
    (k : Fin (K p h + 1)) :
    auxiliaryCoefficientPolynomial (z • a) i k =
      z • auxiliaryCoefficientPolynomial a i k := by
  simp [auxiliaryCoefficientPolynomial]

private theorem rationalReducedConditionPolynomial_add
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (a b : AuxiliaryCoefficients E p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD (a + b) =
      rationalReducedConditionPolynomial p h c pole r lowN lowD a +
        rationalReducedConditionPolynomial p h c pole r lowN lowD b := by
  simp only [rationalReducedConditionPolynomial,
    auxiliaryCoefficientPolynomial_add, rationalReducedTerm, map_add,
    add_mul, Finset.sum_add_distrib]

private theorem rationalReducedConditionPolynomial_smul
    {E : Type*} [Field E] (p h : ℕ) (c pole : E) (r : ℕ)
    (lowN lowD : E[X]) (z : E) (a : AuxiliaryCoefficients E p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD (z • a) =
      z • rationalReducedConditionPolynomial p h c pole r lowN lowD a := by
  simp only [rationalReducedConditionPolynomial,
    auxiliaryCoefficientPolynomial_smul, rationalReducedTerm,
    LinearMap.map_smul_of_tower, smul_mul_assoc, Finset.smul_sum]

/-- The rational reduced-condition linear map. -/
noncomputable def rationalReducedConditionLinear
    {E : Type*} [Field E] (p h s : ℕ) (c pole : E)
    (lowN lowD : E[X]) :
    AuxiliaryCoefficients E p h →ₗ[E] RationalAuxiliaryConditions E p h s where
  toFun a r j :=
    (rationalReducedConditionPolynomial p h c pole r lowN lowD a).coeff j
  map_add' a b := by
    funext r j
    rw [rationalReducedConditionPolynomial_add, coeff_add]
    rfl
  map_smul' z a := by
    funext r j
    rw [rationalReducedConditionPolynomial_smul, coeff_smul]
    rfl

private theorem finrank_auxiliaryCoefficients
    {E : Type*} [Field E] (p h : ℕ) :
    Module.finrank E (AuxiliaryCoefficients E p h) =
      p * S p h * (K p h + 1) := by
  simp [AuxiliaryCoefficients, Module.finrank_pi_fintype]
  ring

private theorem finrank_rationalAuxiliaryConditions
    {E : Type*} [Field E] (p h s : ℕ) :
    Module.finrank E (RationalAuxiliaryConditions E p h s) =
      R p h * rationalConditionDegree p h s := by
  simp [RationalAuxiliaryConditions, Module.finrank_pi_fintype]

/-- The strict count supplies a nonzero family satisfying every rational
reduced condition. -/
theorem exists_nonzero_rationalAuxiliaryCoefficients
    {E : Type*} [Field E] {p h s : ℕ}
    (hp : 1 < p) (hs : s < p) (c pole : E) (lowN lowD : E[X]) :
    ∃ a : AuxiliaryCoefficients E p h,
      a ≠ 0 ∧
        rationalReducedConditionLinear p h s c pole lowN lowD a = 0 := by
  let T := rationalReducedConditionLinear p h s c pole lowN lowD
  have hker : LinearMap.ker T ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective T := LinearMap.ker_eq_bot.mp hbot
    have hle := T.finrank_le_finrank_of_injective hinj
    rw [finrank_auxiliaryCoefficients p h,
      finrank_rationalAuxiliaryConditions p h s] at hle
    exact (not_le_of_gt (rationalConstraints_lt_coefficients hp hs)) hle
  obtain ⟨a, ha, hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hker
  exact ⟨a, hane, ha⟩

/-- A kernel coefficient family makes every reduced condition polynomial
identically zero. -/
theorem rationalReducedConditionPolynomial_eq_zero_of_linear_eq_zero
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    (c pole : E) {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    {a : AuxiliaryCoefficients E p h}
    (ha : rationalReducedConditionLinear p h s c pole lowN lowD a = 0)
    {r : ℕ} (hr : r < R p h) :
    rationalReducedConditionPolynomial p h c pole r lowN lowD a = 0 := by
  let F := rationalReducedConditionPolynomial p h c pole r lowN lowD a
  have hdegree : F.natDegree < rationalConditionDegree p h s := by
    have hboundPos : 0 < rationalConditionDegree p h s := by
      exact Nat.add_pos_left (Nat.add_pos_left (Nat.pow_pos hp) _) _
    refine (natDegree_sum_le_of_forall_le _ _ ?_).trans_lt
      (Nat.pred_lt hboundPos.ne')
    intro i hi
    apply natDegree_sum_le_of_forall_le
    intro k hk
    exact Nat.le_pred_of_lt <|
      natDegree_rationalReducedTerm_lt hp c pole
        (natDegree_auxiliaryCoefficientPolynomial_lt hp a i k)
        hN hD i.isLt (by omega)
  ext j
  by_cases hj : j < rationalConditionDegree p h s
  · have hcoeff := congrFun (congrFun ha ⟨r, hr⟩) ⟨j, hj⟩
    change (rationalReducedConditionPolynomial
      p h c pole r lowN lowD a).coeff j = 0 at hcoeff
    exact hcoeff
  · rw [coeff_eq_zero_of_natDegree_lt
      (hdegree.trans_le (Nat.le_of_not_gt hj)), coeff_zero]

end RationalStepanov

end Erdos387
