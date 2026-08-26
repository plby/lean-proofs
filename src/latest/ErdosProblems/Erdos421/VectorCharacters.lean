import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Finite Fourier orthogonality for vectors of residues -/

namespace Erdos421

open scoped ComplexConjugate

variable {q k : ℕ} [NeZero q]

noncomputable def vectorCharacter (a v : Fin k → ZMod q) : ℂ :=
  ∏ j : Fin k, ZMod.stdAddChar (a j * v j)

theorem vectorCharacter_add (a v w : Fin k → ZMod q) :
    vectorCharacter a (v + w) = vectorCharacter a v * vectorCharacter a w := by
  simp only [vectorCharacter, Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]

theorem stdAddChar_neg_conj (a : ZMod q) : ZMod.stdAddChar (-a) = conj (ZMod.stdAddChar a) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv,
    Circle.coe_inv_eq_conj]

theorem vectorCharacter_neg (a v : Fin k → ZMod q) :
    vectorCharacter a (-v) = conj (vectorCharacter a v) := by
  simp only [vectorCharacter, Pi.neg_apply, mul_neg, stdAddChar_neg_conj, map_prod]

theorem vectorCharacter_mul_conj (a v w : Fin k → ZMod q) :
    vectorCharacter a v * conj (vectorCharacter a w) = vectorCharacter a (v - w) := by
  rw [sub_eq_add_neg, vectorCharacter_add, vectorCharacter_neg]

theorem stdAddChar_sum_mul (v : ZMod q) :
    (∑ a : ZMod q, ZMod.stdAddChar (a * v)) = if v = 0 then (q : ℂ) else 0 := by
  split_ifs with hv
  · simp only [hv, mul_zero, AddChar.map_zero_eq_one, Finset.sum_const,
      Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  · simpa only [AddChar.mulShift_apply, mul_comm] using
      AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q hv)

theorem sum_vectorCharacter (v : Fin k → ZMod q) :
    (∑ a : Fin k → ZMod q, vectorCharacter a v) = if v = 0 then (q : ℂ) ^ k else 0 := by
  classical
  unfold vectorCharacter
  rw [← Fintype.prod_sum (fun (j : Fin k) (b : ZMod q) ↦ ZMod.stdAddChar (b * v j))]
  simp_rw [stdAddChar_sum_mul]
  split_ifs with hv
  · simp only [hv, Pi.zero_apply, if_true, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  · obtain ⟨j, hj⟩ : ∃ j : Fin k, v j ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

noncomputable def vectorCharacterSum {X : Type*} (S : Finset X) (f : X → Fin k → ZMod q)
    (a : Fin k → ZMod q) : ℂ := ∑ x ∈ S, vectorCharacter a (f x)

theorem sum_vectorCharacterSum_mul_conj {X : Type*} (S : Finset X)
    (f : X → Fin k → ZMod q) :
    (∑ a : Fin k → ZMod q, vectorCharacterSum S f a * conj (vectorCharacterSum S f a)) =
      (q : ℂ) ^ k * (((S ×ˢ S).filter (fun p ↦ f p.1 = f p.2)).card : ℂ) := by
  classical
  have hexpand (a : Fin k → ZMod q) :
      vectorCharacterSum S f a * conj (vectorCharacterSum S f a) =
        ∑ x ∈ S, ∑ y ∈ S, vectorCharacter a (f x - f y) := by
    simp only [vectorCharacterSum, map_sum, Finset.sum_mul, Finset.mul_sum,
      vectorCharacter_mul_conj]
    exact Finset.sum_comm
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  have hswap (x : X) : (∑ a : Fin k → ZMod q, ∑ y ∈ S, vectorCharacter a (f x - f y)) =
      ∑ y ∈ S, ∑ a : Fin k → ZMod q, vectorCharacter a (f x - f y) := Finset.sum_comm
  simp_rw [hswap, sum_vectorCharacter, sub_eq_zero]
  rw [← Finset.sum_product (f := fun p : X × X ↦ if f p.1 = f p.2 then (q : ℂ) ^ k else 0),
    ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem sum_norm_vectorCharacterSum_sq {X : Type*} (S : Finset X)
    (f : X → Fin k → ZMod q) :
    (∑ a : Fin k → ZMod q, ‖vectorCharacterSum S f a‖ ^ 2) =
      (q : ℝ) ^ k * (((S ×ˢ S).filter (fun p ↦ f p.1 = f p.2)).card : ℝ) := by
  have h := sum_vectorCharacterSum_mul_conj S f
  simp only [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_sum,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

theorem vectorCharacter_zero (a : Fin k → ZMod q) : vectorCharacter a 0 = 1 := by
  simp only [vectorCharacter, Pi.zero_apply, mul_zero, AddChar.map_zero_eq_one,
    Finset.prod_const_one]

theorem vectorCharacter_sum {X : Type*} (S : Finset X) (a : Fin k → ZMod q)
    (f : X → Fin k → ZMod q) :
    vectorCharacter a (∑ x ∈ S, f x) = ∏ x ∈ S, vectorCharacter a (f x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, vectorCharacter_zero]
  | @insert x S hx ih =>
    rw [Finset.sum_insert hx, Finset.prod_insert hx, vectorCharacter_add, ih]

theorem vectorCharacterSum_power {X : Type*} [Fintype X]
    (f : X → Fin k → ZMod q) (a : Fin k → ZMod q) (s : ℕ) :
    vectorCharacterSum Finset.univ f a ^ s =
      vectorCharacterSum Finset.univ (fun x : Fin s → X ↦ ∑ i : Fin s, f (x i)) a := by
  simp only [vectorCharacterSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  exact (vectorCharacter_sum Finset.univ a (fun i ↦ f (x i))).symm

theorem vectorCharacterSum_moment {X : Type*} [Fintype X]
    (f : X → Fin k → ZMod q) (s : ℕ) :
    (∑ a : Fin k → ZMod q, ‖vectorCharacterSum Finset.univ f a‖ ^ (2 * s)) =
      (q : ℝ) ^ k * (((Finset.univ : Finset ((Fin s → X) × (Fin s → X))).filter
        (fun p ↦ (∑ i : Fin s, f (p.1 i)) = ∑ i : Fin s, f (p.2 i))).card : ℝ) := by
  have h := sum_norm_vectorCharacterSum_sq (Finset.univ : Finset (Fin s → X))
    (fun x ↦ ∑ i : Fin s, f (x i))
  simpa only [← vectorCharacterSum_power, norm_pow, ← pow_mul, Nat.mul_comm s 2,
    Finset.univ_product_univ] using h

end Erdos421
