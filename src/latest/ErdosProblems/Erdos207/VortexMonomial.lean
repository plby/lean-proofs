/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexVertex
import ErdosProblems.Erdos207.VortexWellSpread
import Mathlib.Algebra.BigOperators.Fin

/-! # A finite majorization inequality for vortex monomials -/

namespace Erdos207

open Finset

/-- Prefix-sum domination for lists of natural exponents. -/
def ListPrefixLe (v w : List ℕ) : Prop :=
  ∀ k : ℕ, (v.take k).sum ≤ (w.take k).sum

lemma ListPrefixLe.head_le
    {v₀ w₀ : ℕ} {v w : List ℕ}
    (h : ListPrefixLe (v₀ :: v) (w₀ :: w)) : v₀ ≤ w₀ := by
  simpa [ListPrefixLe] using h 1

/-- If exponent mass is moved toward earlier (larger) bases, the resulting
monomial can only increase.  This is the discrete summation-by-parts step in
KSSS Lemma 7.2. -/
theorem list_prod_pow_le_of_prefix
    (a v w : List ℕ)
    (hav : a.length = v.length) (haw : a.length = w.length)
    (ha : a.Pairwise fun x y ↦ y ≤ x)
    (hsum : v.sum = w.sum) (hpref : ListPrefixLe v w) :
    (List.zipWith (fun x e ↦ x ^ e) a v).prod ≤
      (List.zipWith (fun x e ↦ x ^ e) a w).prod := by
  induction a generalizing v w with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp (by simpa using hav.symm)
      have hw : w = [] := List.length_eq_zero_iff.mp (by simpa using haw.symm)
      simp [hv, hw]
  | cons a₀ aTail ih =>
      cases v with
      | nil => simp at hav
      | cons v₀ vTail =>
        cases w with
        | nil => simp at haw
        | cons w₀ wTail =>
          have hlenv : aTail.length = vTail.length := by simpa using hav
          have hlenw : aTail.length = wTail.length := by simpa using haw
          have hvw₀ : v₀ ≤ w₀ := hpref.head_le
          by_cases hTail : aTail = []
          · subst aTail
            have hvnil : vTail = [] :=
              List.length_eq_zero_iff.mp (by simpa using hlenv.symm)
            have hwnil : wTail = [] :=
              List.length_eq_zero_iff.mp (by simpa using hlenw.symm)
            subst vTail
            subst wTail
            have hvw : v₀ = w₀ := by simpa using hsum
            subst w₀
            simp
          · obtain ⟨a₁, aRest, rfl⟩ := List.exists_cons_of_ne_nil hTail
            cases vTail with
            | nil => simp at hlenv
            | cons v₁ vRest =>
              cases wTail with
              | nil => simp at hlenw
              | cons w₁ wRest =>
                let d := w₀ - v₀
                let wTail' : List ℕ := (w₁ + d) :: wRest
                have hv₀d : v₀ + d = w₀ := by
                  dsimp only [d]
                  omega
                have hsumTail : (v₁ :: vRest).sum = wTail'.sum := by
                  dsimp only [wTail', d]
                  simp only [List.sum_cons] at hsum ⊢
                  omega
                have hprefTail : ListPrefixLe (v₁ :: vRest) wTail' := by
                  intro k
                  cases k with
                  | zero => simp
                  | succ k =>
                    have h := hpref (k + 2)
                    dsimp only [wTail', d]
                    simp only [List.take_succ_cons, List.sum_cons] at h ⊢
                    omega
                have haParts := List.pairwise_cons.mp ha
                have haTail : (a₁ :: aRest).Pairwise fun x y ↦ y ≤ x :=
                  haParts.2
                have ha₁a₀ : a₁ ≤ a₀ := haParts.1 a₁ (by simp)
                have hrec := ih (v₁ :: vRest) wTail'
                  (by simpa using hlenv) (by simpa [wTail'] using hlenw)
                  haTail hsumTail hprefTail
                dsimp only [wTail'] at hrec
                simp only [List.zipWith_cons_cons, List.prod_cons] at hrec ⊢
                calc
                  a₀ ^ v₀ * (a₁ ^ v₁ *
                      (List.zipWith (fun x e ↦ x ^ e) aRest vRest).prod) ≤
                      a₀ ^ v₀ * (a₁ ^ (w₁ + d) *
                        (List.zipWith (fun x e ↦ x ^ e) aRest wRest).prod) :=
                    Nat.mul_le_mul_left _ hrec
                  _ = (a₀ ^ v₀ * a₁ ^ d) *
                      (a₁ ^ w₁ *
                        (List.zipWith (fun x e ↦ x ^ e) aRest wRest).prod) := by
                    rw [pow_add]
                    ac_rfl
                  _ ≤ (a₀ ^ v₀ * a₀ ^ d) *
                      (a₁ ^ w₁ *
                        (List.zipWith (fun x e ↦ x ^ e) aRest wRest).prod) := by
                    gcongr
                  _ = a₀ ^ w₀ * (a₁ ^ w₁ *
                      (List.zipWith (fun x e ↦ x ^ e) aRest wRest).prod) := by
                    rw [← pow_add, hv₀d]

/-- `zipWith` commutes with the canonical list enumeration of a finite
function. -/
lemma List.zipWith_ofFn
    {α β γ : Type*} {n : ℕ} (f : α → β → γ)
    (a : Fin n → α) (b : Fin n → β) :
    List.zipWith f (List.ofFn a) (List.ofFn b) =
      List.ofFn fun i ↦ f (a i) (b i) := by
  induction n with
  | zero => simp only [List.ofFn_zero, List.zipWith_nil_left]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ,
        List.zipWith_cons_cons]
      congr 1
      exact ih (fun i ↦ a i.succ) (fun i ↦ b i.succ)

/-- Sum of the first `k` coordinates of a finite function.  Coordinates past
the end are harmlessly ignored. -/
def finPrefixSum {n : ℕ} (v : Fin n → ℕ) (k : ℕ) : ℕ :=
  ∑ i, if i.val < k then v i else 0

/-- The first `k` entries of `List.ofFn` have the expected finite sum. -/
lemma sum_take_ofFn_eq_finPrefixSum
    {n : ℕ} (v : Fin n → ℕ) (k : ℕ) :
    ((List.ofFn v).take k).sum = finPrefixSum v k := by
  induction n generalizing k with
  | zero => simp [finPrefixSum]
  | succ n ih =>
      cases k with
      | zero => simp [finPrefixSum]
      | succ k =>
        rw [List.ofFn_succ]
        simp only [List.take_succ_cons, List.sum_cons, finPrefixSum,
          Fin.sum_univ_succ, Fin.val_zero, Nat.zero_lt_succ, if_true,
          Fin.val_succ]
        congr 1
        rw [ih (fun i ↦ v i.succ) k]
        unfold finPrefixSum
        apply Finset.sum_congr rfl
        intro i _hi
        simp

/-- Prefix domination for functions on an initial finite interval. -/
def FinPrefixLe {n : ℕ} (v w : Fin n → ℕ) : Prop :=
  ∀ k : ℕ, finPrefixSum v k ≤ finPrefixSum w k

lemma finPrefixSum_eq_sum_of_length_le
    {n k : ℕ} (v : Fin n → ℕ) (hk : n ≤ k) :
    finPrefixSum v k = ∑ i, v i := by
  unfold finPrefixSum
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [if_pos (i.isLt.trans_le hk)]

/-- Function-indexed form of `list_prod_pow_le_of_prefix`. -/
theorem fin_prod_pow_le_of_prefix
    {n : ℕ} (a v w : Fin n → ℕ)
    (ha : Antitone a) (hsum : ∑ i, v i = ∑ i, w i)
    (hpref : FinPrefixLe v w) :
    ∏ i, a i ^ v i ≤ ∏ i, a i ^ w i := by
  have hpair : (List.ofFn a).Pairwise fun x y ↦ y ≤ x := by
    rw [List.pairwise_ofFn]
    intro i j hij
    exact ha hij.le
  have hprefList : ListPrefixLe (List.ofFn v) (List.ofFn w) := by
    intro k
    rw [sum_take_ofFn_eq_finPrefixSum, sum_take_ofFn_eq_finPrefixSum]
    exact hpref k
  have hlist := list_prod_pow_le_of_prefix
    (List.ofFn a) (List.ofFn v) (List.ofFn w)
    (by simp) (by simp) hpair (by
      rw [List.sum_ofFn, List.sum_ofFn]
      exact hsum) hprefList
  rw [List.zipWith_ofFn, List.zipWith_ofFn,
    List.prod_ofFn, List.prod_ofFn] at hlist
  exact hlist

/-- Add all unused exponent mass to the terminal coordinate. -/
def padTerminalExponent {ell : ℕ} (v : Fin (ell + 1) → ℕ) (R : ℕ) :
    Fin (ell + 1) → ℕ :=
  Fin.lastCases (v (Fin.last ell) + (R - ∑ i, v i))
    (fun i ↦ v i.castSucc)

/-- The exponent vector represented by an outer profile and a total mass. -/
def profileExponentVector {ell : ℕ} (R : ℕ) (t : VortexProfile ell) :
    Fin (ell + 1) → ℕ :=
  Fin.lastCases (R - t.mass) t

lemma finPrefixSum_padTerminalExponent_of_le
    {ell R k : ℕ} (v : Fin (ell + 1) → ℕ) (hk : k ≤ ell) :
    finPrefixSum (padTerminalExponent v R) k = finPrefixSum v k := by
  unfold finPrefixSum
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [padTerminalExponent, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  have hlast : ¬ ell < k := by omega
  simp only [Fin.val_last, hlast, if_false, add_zero]

lemma finPrefixSum_profileExponentVector_of_le
    {ell R k : ℕ} (t : VortexProfile ell) (hk : k ≤ ell) :
    finPrefixSum (profileExponentVector R t) k = finPrefixSum t k := by
  unfold finPrefixSum
  rw [Fin.sum_univ_castSucc]
  simp only [profileExponentVector, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  have hlast : ¬ ell < k := by omega
  simp only [Fin.val_last, hlast, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro i _hi
  simp

lemma sum_padTerminalExponent
    {ell R : ℕ} {v : Fin (ell + 1) → ℕ} (hv : ∑ i, v i ≤ R) :
    ∑ i, padTerminalExponent v R i = R := by
  have hsplit := Fin.sum_univ_castSucc v
  rw [Fin.sum_univ_castSucc] at hv
  rw [Fin.sum_univ_castSucc]
  simp only [padTerminalExponent, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  rw [hsplit]
  omega

lemma sum_profileExponentVector
    {ell R : ℕ} {t : VortexProfile ell} :
    ∑ i, profileExponentVector R t i = max R t.mass := by
  rw [Fin.sum_univ_castSucc]
  simp only [profileExponentVector, Fin.lastCases_castSucc,
    Fin.lastCases_last, VortexProfile.mass]
  omega

lemma prod_pow_le_padTerminalExponent
    {ell R : ℕ} (a v : Fin (ell + 1) → ℕ)
    (ha : 1 ≤ a (Fin.last ell)) :
    ∏ i, a i ^ v i ≤ ∏ i, a i ^ padTerminalExponent v R i := by
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  simp only [padTerminalExponent, Fin.lastCases_castSucc,
    Fin.lastCases_last]
  gcongr
  exact Nat.le_add_right _ _

/-- The finite monomial estimate used in the profile count: after padding at
the terminal level, cumulative domination by `t` converts choices of vertex
spans into the KSSS scale `|U_ell|^(R-|t|) prod |U_i|^t_i`. -/
theorem Vortex.vertexProfileMonomial_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell R : ℕ}
    (W : Vortex V ell) (v : VortexVertexProfile ell)
    (t : VortexProfile ell)
    (hv : ∑ i, v i ≤ R)
    (hterminal : 0 < W.terminalSize)
    (hpref : FinPrefixLe (padTerminalExponent v (max R t.mass))
      (profileExponentVector R t)) :
    ∏ i : Fin (ell + 1), (W.U i).card ^ v i ≤
      W.terminalSize ^ (R - t.mass) * W.profileScale t := by
  let a : Fin (ell + 1) → ℕ := fun i ↦ (W.U i).card
  have ha : Antitone a := by
    intro i j hij
    exact card_le_card (W.antitone i j hij)
  have hvmax : ∑ i, v i ≤ max R t.mass := hv.trans (le_max_left _ _)
  have hsum : ∑ i, padTerminalExponent v (max R t.mass) i =
      ∑ i, profileExponentVector R t i := by
    rw [sum_padTerminalExponent hvmax, sum_profileExponentVector]
  calc
    ∏ i : Fin (ell + 1), (W.U i).card ^ v i ≤
        ∏ i : Fin (ell + 1),
          (W.U i).card ^ padTerminalExponent v (max R t.mass) i := by
      apply prod_pow_le_padTerminalExponent
      simp only [Vortex.terminalSize] at hterminal ⊢
      omega
    _ ≤ ∏ i : Fin (ell + 1),
        (W.U i).card ^ profileExponentVector R t i :=
      fin_prod_pow_le_of_prefix a _ _ ha hsum hpref
    _ = W.terminalSize ^ (R - t.mass) * W.profileScale t := by
      rw [Fin.prod_univ_castSucc]
      simp only [profileExponentVector, Fin.lastCases_castSucc,
        Fin.lastCases_last, Vortex.profileScale, Vortex.terminalSize]
      ac_rfl

end Erdos207
