/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos240.Delta
import Mathlib.RingTheory.Binomial
import Mathlib.NumberTheory.Chebyshev

/-!
# Sharp derivative denominators for integer-valued binomial polynomials

This module isolates the arithmetic fact behind the sharp `lcmUpto h ^ m`
normalization in van der Poorten--Loxton's Lemma 1.  The key observation is
that, for `L` divisible by `1, ..., h`, the polynomial

`T ↦ (z + L*T).choose h`

has integral coefficients for every integer `z`.  Chu--Vandermonde reduces
this to the explicit integral factorization of `(L*T).choose j`.

The coefficient of `T^m` is `L^m` times the `m`th Hasse derivative at `z`.
The final section records closure under products directly from the Hasse
Leibniz rule.  In particular, no power depending on the total degree of a
product is introduced.
-/

noncomputable section

open scoped Polynomial

namespace Erdos240.IntegerValuedPolynomial

open Finset Polynomial
open Erdos240Delta

/-- A rational polynomial is integer-valued on the embedded integers. -/
def IsIntegerValued (p : ℚ[X]) : Prop :=
  ∀ z : ℤ, ∃ w : ℤ, p.eval (z : ℚ) = (w : ℚ)

/-- The denominator assigned to the `i`th factor of the falling-binomial
polynomial.  The factor with index zero receives denominator `k`; all other
factors receive their index. -/
def fallingDenom (k i : ℕ) : ℕ :=
  if i = 0 then k else i

theorem fallingDenom_pos {k i : ℕ} (hk : 0 < k) (hi : i < k) :
    0 < fallingDenom k i := by
  simp only [fallingDenom]
  split_ifs with h
  · exact hk
  · exact Nat.pos_of_ne_zero h

theorem fallingDenom_le {k i : ℕ} (hi : i < k) :
    fallingDenom k i ≤ k := by
  simp only [fallingDenom]
  split_ifs
  · exact le_rfl
  · exact hi.le

theorem fallingDenom_dvd_index (k i : ℕ) : fallingDenom k i ∣ i := by
  simp only [fallingDenom]
  split_ifs with h
  · simp [h]
  · exact dvd_refl i

theorem prod_fallingDenom (k : ℕ) :
    ∏ i ∈ Finset.range k, fallingDenom k i = k.factorial := by
  obtain rfl | k := k
  · simp [fallingDenom]
  · calc
      ∏ i ∈ Finset.range (k + 1), fallingDenom (k + 1) i =
          (∏ i ∈ Finset.Ico 0 1, fallingDenom (k + 1) i) *
            ∏ i ∈ Finset.Ico 1 (k + 1), fallingDenom (k + 1) i := by
        rw [← Nat.Ico_zero_eq_range]
        exact (Finset.prod_Ico_consecutive
          (fun i ↦ fallingDenom (k + 1) i)
          (m := 0) (n := 1) (k := k + 1) (by omega) (by omega)).symm
      _ = (k + 1) * ∏ i ∈ Finset.Ico 1 (k + 1), i := by
        rw [show (∏ i ∈ Finset.Ico 0 1, fallingDenom (k + 1) i) =
            k + 1 by simp [fallingDenom]]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp [fallingDenom, Nat.ne_of_gt hi.1]
      _ = (k + 1).factorial := by
        rw [Finset.prod_Ico_id_eq_factorial]
        simp [Nat.factorial_succ, mul_comm]

/-- The falling-binomial polynomial `X choose k`, over `ℚ`. -/
def fallingChoose (k : ℕ) : ℚ[X] :=
  Ring.choose (X : ℚ[X]) k

/-- An integral polynomial representing `(L*X).choose k`, provided the
assigned denominator of every factor divides `L`. -/
def scaledFallingChooseInt (L k : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range k,
    (C ((L / fallingDenom k i : ℕ) : ℤ) * X -
      C ((i / fallingDenom k i : ℕ) : ℤ))

theorem fallingDenom_dvd_lcmUpto {h k i : ℕ}
    (hk : k ≤ h) (hi : i < k) :
    fallingDenom k i ∣ Nat.lcmUpto h := by
  apply Finset.dvd_lcm (s := Finset.Icc 1 h) (f := id)
  simp only [Finset.mem_Icc]
  exact ⟨fallingDenom_pos (Nat.zero_lt_of_lt hi) hi,
    (fallingDenom_le hi).trans hk⟩

theorem map_scaledFallingChooseInt_factor
    {L k i : ℕ} (hk : 0 < k) (hi : i < k)
    (hd : fallingDenom k i ∣ L) :
    (C ((L / fallingDenom k i : ℕ) : ℤ) * X -
        C ((i / fallingDenom k i : ℕ) : ℤ)).map
        (Int.castRingHom ℚ) =
      C ((fallingDenom k i : ℚ)⁻¹) *
        (C (L : ℚ) * X - C (i : ℚ)) := by
  let d := fallingDenom k i
  have hdpos : 0 < d := fallingDenom_pos hk hi
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
  have hdi : d ∣ i := fallingDenom_dvd_index k i
  have hLdiv : ((L / d : ℕ) : ℚ) = (L : ℚ) / d := by
    apply (eq_div_iff hd0).2
    exact_mod_cast Nat.div_mul_cancel hd
  have hidiv : ((i / d : ℕ) : ℚ) = (i : ℚ) / d := by
    apply (eq_div_iff hd0).2
    exact_mod_cast Nat.div_mul_cancel hdi
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X]
  change C (((L / d : ℕ) : ℚ)) * X - C (((i / d : ℕ) : ℚ)) =
    C ((d : ℚ)⁻¹) * (C (L : ℚ) * X - C (i : ℚ))
  rw [hLdiv, hidiv]
  rw [mul_sub, ← mul_assoc, ← C_mul, ← C_mul]
  congr 2 <;> field_simp

theorem descPochhammer_eq_prod_range (k : ℕ) :
    descPochhammer ℚ k = ∏ i ∈ Finset.range k, (X - C (i : ℚ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [descPochhammer_succ_right, ih, Finset.prod_range_succ]
      rfl

theorem fallingChoose_eq (k : ℕ) :
    fallingChoose k =
      C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k := by
  rw [fallingChoose]
  have h := Ring.descPochhammer_eq_factorial_smul_choose
    (r := (X : ℚ[X])) k
  have hdesc : (descPochhammer ℤ k).smeval (X : ℚ[X]) =
      descPochhammer ℚ k := by
    clear h
    induction k with
    | zero => simp
    | succ k ih =>
        rw [descPochhammer_succ_right, descPochhammer_succ_right,
          Polynomial.smeval_mul, ih]
        congr 1
        simp only [Polynomial.smeval_sub, Polynomial.smeval_X,
          Polynomial.smeval_natCast, pow_one, pow_zero]
        simp
  rw [hdesc] at h
  calc
    Ring.choose (X : ℚ[X]) k =
        C ((k.factorial : ℚ)⁻¹) *
          (k.factorial • Ring.choose (X : ℚ[X]) k) := by
      rw [nsmul_eq_mul, ← C_eq_natCast, ← mul_assoc, ← C_mul,
        inv_mul_cancel₀ (by positivity), C_1, one_mul]
    _ = C ((k.factorial : ℚ)⁻¹) * descPochhammer ℚ k := by rw [← h]

theorem fallingChoose_comp_eq (L k : ℕ) :
    (fallingChoose k).comp (C (L : ℚ) * X) =
      C ((k.factorial : ℚ)⁻¹) *
        ∏ i ∈ Finset.range k,
          (C (L : ℚ) * X - C (i : ℚ)) := by
  rw [fallingChoose_eq, Polynomial.mul_comp, Polynomial.C_comp,
    descPochhammer_eq_prod_range, Polynomial.prod_comp]
  apply congrArg (fun p : ℚ[X] ↦ C ((k.factorial : ℚ)⁻¹) * p)
  apply Finset.prod_congr rfl
  intro i hi
  simp

theorem map_scaledFallingChooseInt (h k : ℕ) (hk : k ≤ h) :
    (scaledFallingChooseInt (Nat.lcmUpto h) k).map (Int.castRingHom ℚ) =
      (fallingChoose k).comp (C (Nat.lcmUpto h : ℚ) * X) := by
  obtain rfl | k := k
  · simp [scaledFallingChooseInt, fallingChoose, Ring.choose_zero_right]
  · have hkpos : 0 < k + 1 := Nat.succ_pos k
    simp only [scaledFallingChooseInt, Polynomial.map_prod]
    rw [Finset.prod_congr rfl (fun i hi ↦
      map_scaledFallingChooseInt_factor hkpos (Finset.mem_range.mp hi)
        (fallingDenom_dvd_lcmUpto hk (Finset.mem_range.mp hi)))]
    rw [Finset.prod_mul_distrib]
    calc
      (∏ i ∈ Finset.range (k + 1), C ((fallingDenom (k + 1) i : ℚ)⁻¹)) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) =
          C (∏ i ∈ Finset.range (k + 1),
              ((fallingDenom (k + 1) i : ℚ)⁻¹)) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) := by
        rw [map_prod]
      _ = C (((k + 1).factorial : ℚ)⁻¹) *
            ∏ i ∈ Finset.range (k + 1),
              (C (Nat.lcmUpto h : ℚ) * X - C (i : ℚ)) := by
        rw [Finset.prod_inv_distrib]
        have hcast :
            (∏ i ∈ Finset.range (k + 1),
              (fallingDenom (k + 1) i : ℚ)) = ((k + 1).factorial : ℚ) := by
          exact_mod_cast prod_fallingDenom (k + 1)
        rw [hcast]
      _ = (fallingChoose (k + 1)).comp
            (C (Nat.lcmUpto h : ℚ) * X) :=
        (fallingChoose_comp_eq (Nat.lcmUpto h) (k + 1)).symm

/-- An integral Chu--Vandermonde expansion of
`(z + lcmUpto(h)*X).choose k`. -/
def scaledShiftedChooseInt (h k : ℕ) (z : ℤ) : ℤ[X] :=
  ∑ ij ∈ Finset.antidiagonal k,
    C (Ring.choose z ij.1) * scaledFallingChooseInt (Nat.lcmUpto h) ij.2

theorem fallingChoose_comp (p : ℚ[X]) (k : ℕ) :
    (fallingChoose k).comp p = Ring.choose p k := by
  simpa [fallingChoose, Polynomial.coe_compRingHom_apply] using
    (Ring.map_choose (Polynomial.compRingHom p) (X : ℚ[X]) k)

theorem choose_comp (a p : ℚ[X]) (k : ℕ) :
    (Ring.choose a k).comp p = Ring.choose (a.comp p) k := by
  simpa [Polynomial.coe_compRingHom_apply] using
    (Ring.map_choose (Polynomial.compRingHom p) a k)

theorem map_scaledShiftedChooseInt (h k : ℕ) (hk : k ≤ h) (z : ℤ) :
    (scaledShiftedChooseInt h k z).map (Int.castRingHom ℚ) =
      Ring.choose
        (C (z : ℚ) + C (Nat.lcmUpto h : ℚ) * X) k := by
  rw [scaledShiftedChooseInt]
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  rw [Ring.add_choose_eq k (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro ij hij
  have hjk : ij.2 ≤ k := by
    exact Finset.mem_antidiagonal.mp hij ▸ Nat.le_add_left _ _
  rw [Ring.map_choose, map_scaledFallingChooseInt h ij.2 (hjk.trans hk),
    fallingChoose_comp]
  rw [Ring.map_choose (Polynomial.C : ℚ →+* ℚ[X])]
  rfl

/-- Scaling the Taylor variable scales the `m`th coefficient by `L^m`. -/
theorem coeff_comp_C_mul_X_add_C (p : ℚ[X]) (L : ℕ) (z : ℤ) (m : ℕ) :
    (p.comp (C (L : ℚ) * X + C (z : ℚ))).coeff m =
      (L : ℚ) ^ m * (hasseDeriv m p).eval (z : ℚ) := by
  calc
    (p.comp (C (L : ℚ) * X + C (z : ℚ))).coeff m =
        ((taylor (z : ℚ) p).comp (C (L : ℚ) * X)).coeff m := by
      congr 1
      simp only [taylor_apply, comp_assoc, add_comp, X_comp, C_comp,
        mul_comp]
    _ = (taylor (z : ℚ) p).coeff m * (L : ℚ) ^ m := by
      exact comp_C_mul_X_coeff
    _ = (L : ℚ) ^ m * (hasseDeriv m p).eval (z : ℚ) := by
      rw [taylor_coeff]
      ring

theorem descPochhammer_comp_add_nat (h : ℕ) :
    (descPochhammer ℚ h).comp (X + C (h : ℚ)) =
      (ascPochhammer ℚ h).comp (X + 1) := by
  have hi := congrArg
    (fun p : ℤ[X] ↦ p.map (Int.castRingHom ℚ))
    (descPochhammer_eq_ascPochhammer h)
  have hiQ :
      descPochhammer ℚ h =
        (ascPochhammer ℚ h).comp (X - C (h : ℚ) + 1) := by
    simpa [Polynomial.map_comp] using hi
  rw [hiQ, comp_assoc]
  congr 1
  simp only [add_comp, sub_comp, X_comp, C_comp, one_comp]
  ring

theorem delta_eq_shifted_fallingChoose (h : ℕ) :
    delta h = Ring.choose (X + C (h : ℚ)) h := by
  rw [← fallingChoose_comp (X + C (h : ℚ)) h, fallingChoose_eq,
    Polynomial.mul_comp, Polynomial.C_comp, descPochhammer_comp_add_nat]
  rw [delta, deltaNumerator_eq]

/-- The sharp one-factor denominator theorem: at every integer argument,
`lcm(1,...,h)^m` times the `m`th normalized derivative of `Delta_h` is an
integer. -/
theorem exists_int_lcmUpto_pow_mul_eval_deltaHasse
    (h m : ℕ) (z : ℤ) :
    ∃ w : ℤ,
      (Nat.lcmUpto h : ℚ) ^ m * (deltaHasse h m).eval (z : ℚ) = (w : ℚ) := by
  let A : ℤ[X] :=
    scaledShiftedChooseInt h h (z + (h : ℤ))
  refine ⟨A.coeff m, ?_⟩
  have hpoly :
      A.map (Int.castRingHom ℚ) =
        (delta h).comp
          (C (Nat.lcmUpto h : ℚ) * X + C (z : ℚ)) := by
    dsimp only [A]
    rw [map_scaledShiftedChooseInt h h le_rfl,
      delta_eq_shifted_fallingChoose, choose_comp]
    congr 1
    simp only [add_comp, X_comp, C_comp]
    push_cast
    rw [map_add]
    ring
  have hc := congrArg (fun p : ℚ[X] ↦ p.coeff m) hpoly
  rw [Polynomial.coeff_map,
    coeff_comp_C_mul_X_add_C (delta h) (Nat.lcmUpto h) z m] at hc
  simpa [deltaHasse] using hc.symm

/-- Integer-valuedness with a multiplicative derivative denominator. -/
def HasSharpDerivativeDenominators (L : ℕ) (p : ℚ[X]) : Prop :=
  ∀ (m : ℕ) (z : ℤ),
    ∃ w : ℤ, (L : ℚ) ^ m * (hasseDeriv m p).eval (z : ℚ) = (w : ℚ)

theorem hasSharpDerivativeDenominators_delta (h : ℕ) :
    HasSharpDerivativeDenominators (Nat.lcmUpto h) (delta h) := by
  intro m z
  exact exists_int_lcmUpto_pow_mul_eval_deltaHasse h m z

/-- Sharp derivative denominators are closed under multiplication.  This is
the Hasse-Leibniz step that prevents a denominator exponent proportional to
the total degree. -/
theorem HasSharpDerivativeDenominators.mul {L : ℕ} {p q : ℚ[X]}
    (hp : HasSharpDerivativeDenominators L p)
    (hq : HasSharpDerivativeDenominators L q) :
    HasSharpDerivativeDenominators L (p * q) := by
  intro m z
  classical
  choose a ha using fun i ↦ hp i z
  choose b hb using fun j ↦ hq j z
  refine ⟨∑ ij ∈ Finset.antidiagonal m, a ij.1 * b ij.2, ?_⟩
  rw [Polynomial.hasseDeriv_mul]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul]
  rw [Finset.mul_sum]
  calc
    (∑ ij ∈ Finset.antidiagonal m,
        (L : ℚ) ^ m *
          ((hasseDeriv ij.1 p).eval (z : ℚ) *
            (hasseDeriv ij.2 q).eval (z : ℚ))) =
        ∑ ij ∈ Finset.antidiagonal m,
          ((L : ℚ) ^ ij.1 * (hasseDeriv ij.1 p).eval (z : ℚ)) *
            ((L : ℚ) ^ ij.2 * (hasseDeriv ij.2 q).eval (z : ℚ)) := by
      apply Finset.sum_congr rfl
      intro ij hij
      have hij' : ij.1 + ij.2 = m := Finset.mem_antidiagonal.mp hij
      rw [← hij', pow_add]
      ring
    _ = ∑ ij ∈ Finset.antidiagonal m,
          (a ij.1 : ℚ) * (b ij.2 : ℚ) := by
      apply Finset.sum_congr rfl
      intro ij _hij
      rw [ha, hb]
    _ = ((∑ ij ∈ Finset.antidiagonal m, a ij.1 * b ij.2 : ℤ) : ℚ) := by
      norm_cast

/-- Consequently every power of `Delta_h` has the same sharp derivative
denominator `lcmUpto h ^ m`, independent of the power. -/
theorem hasSharpDerivativeDenominators_delta_pow (h lambda : ℕ) :
    HasSharpDerivativeDenominators (Nat.lcmUpto h) (delta h ^ lambda) := by
  induction lambda with
  | zero =>
      intro m z
      by_cases hm : m = 0
      · subst m
        exact ⟨1, by simp⟩
      · refine ⟨0, ?_⟩
        rw [pow_zero,
          Polynomial.hasseDeriv_apply_one m (Nat.pos_of_ne_zero hm)]
        simp
  | succ lambda ih =>
      simpa [pow_succ] using ih.mul (hasSharpDerivativeDenominators_delta h)

theorem exists_int_lcmUpto_pow_mul_eval_delta_pow_hasse
    (h lambda m : ℕ) (z : ℤ) :
    ∃ w : ℤ,
      (Nat.lcmUpto h : ℚ) ^ m *
          (hasseDeriv m (delta h ^ lambda)).eval (z : ℚ) = (w : ℚ) :=
  hasSharpDerivativeDenominators_delta_pow h lambda m z

#print axioms Erdos240.IntegerValuedPolynomial.exists_int_lcmUpto_pow_mul_eval_deltaHasse
#print axioms Erdos240.IntegerValuedPolynomial.HasSharpDerivativeDenominators.mul
#print axioms Erdos240.IntegerValuedPolynomial.exists_int_lcmUpto_pow_mul_eval_delta_pow_hasse

end Erdos240.IntegerValuedPolynomial
