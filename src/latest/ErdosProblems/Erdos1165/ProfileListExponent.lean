/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileA11Assembly

/-!
# Exact profile-list exponent indexing

This file identifies the list-based Stirling exponent used by the finite
profile sum with the scale-indexed interval sum used by HLOZ (A.11).
-/

open scoped BigOperators

namespace Erdos1165.ProfileListExponent

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor

/-- A finite profile read at a natural scale.  Outside its genuine scale
interval `2,...,n`, it is extended by the parabolic centre. -/
def profileAtScale {n : ℕ} (m : Profile n) (l : ℕ) : ℕ :=
  if h : 2 ≤ l ∧ l ≤ n then m ⟨l - 2, by omega⟩ else profileCenter l

@[simp] lemma profileAtScale_scaleIndex {n : ℕ} (m : Profile n)
    (i : Fin (n - 1)) :
    profileAtScale m (scaleIndex i) = m i := by
  have hlower : 2 ≤ scaleIndex i := by simp [scaleIndex]
  have hupper : scaleIndex i ≤ n := by
    unfold scaleIndex
    omega
  rw [profileAtScale, dif_pos ⟨hlower, hupper⟩]
  congr 1

/-- Generic list/interval identity for a list sampled at consecutive natural
indices. -/
lemma stirlingLogLower_ofFn_eq_sum_Ico (f : ℕ → ℕ)
    (start len : ℕ) :
    stirlingLogLower
        (List.ofFn fun i : Fin len ↦ f (start + i.1)) =
      ∑ l ∈ Finset.Ico start (start + (len - 1)),
        edgeStirlingExponent (f l) (f (l + 1)) := by
  induction len generalizing start with
  | zero => simp
  | succ len ih =>
      cases len with
      | zero => simp
      | succ k =>
          have htail := ih (start + 1)
          rw [List.ofFn_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
          rw [show (List.ofFn fun i : Fin (k + 1) ↦
                f (start + (i.1 + 1))) =
              List.ofFn fun i : Fin (k + 1) ↦ f (start + 1 + i.1) by
            congr 1
            funext i
            congr 1
            omega]
          rw [List.ofFn_succ, stirlingLogLower_cons_cons]
          simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]
          rw [show (f (start + 1) :: List.ofFn
                (fun i : Fin k ↦ f (start + 1 + (i.1 + 1)))) =
              List.ofFn
                (fun i : Fin (k + 1) ↦ f (start + 1 + i.1)) by
            symm
            rw [List.ofFn_succ]
            simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero]]
          rw [htail]
          simp only [Nat.add_sub_cancel]
          rw [Finset.sum_eq_sum_Ico_succ_bot
            (Nat.lt_add_of_pos_right (Nat.succ_pos k))]
          congr 1
          simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- **Exact scale-indexed exponent identity for a finite profile.** -/
theorem stirlingLogLower_profileList_eq_sum_edgeStirlingExponent
    {n : ℕ} (hn : 2 ≤ n) (m : Profile n) :
    stirlingLogLower (profileList m) =
      ∑ l ∈ Finset.Ico 2 n,
        edgeStirlingExponent (profileAtScale m l)
          (profileAtScale m (l + 1)) := by
  have hgeneric := stirlingLogLower_ofFn_eq_sum_Ico
    (profileAtScale m) 2 (n - 1)
  have hlist :
      (List.ofFn m) =
        List.ofFn (fun i : Fin (n - 1) ↦ profileAtScale m (2 + i.1)) := by
    congr 1
    funext i
    rw [show 2 + i.1 = scaleIndex i by simp [scaleIndex, Nat.add_comm]]
    exact (profileAtScale_scaleIndex m i).symm
  have htop : 2 + (n - 1 - 1) = n := by omega
  rw [profileList, hlist]
  rw [htop] at hgeneric
  exact hgeneric

end

end Erdos1165.ProfileListExponent
