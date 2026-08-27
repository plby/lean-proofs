/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCommonPinnedSupport
import Mathlib.Algebra.BigOperators.Fin

/-! # Exact local separation of pinned and moved primes -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def localPinnedBaseWeight {m : ℕ} (v : ℝ) (r : Option (Fin m)) : ℝ :=
  if r = none then 1 else v / (v - 1)

def localPinnedDivisorWeight {m : ℕ} (v : ℝ) (r : Option (Fin m)) (a : Option Unit) : ℝ :=
  if a = none then 1 else if r = none then 1 / (v - (m + 1)) else 0

def localPinnedMovedCoeff {m : ℕ} (v : ℝ) (r : Option (Fin m))
    (a : Option Unit) (b : Option (Fin m)) : ℝ :=
  if b = none then 1 else
    if r = none ∧ a = none then -(1 / ((v - 1) * (v - (m + 1)))) else 0

def localPinnedSplitState {m : ℕ} (j : Fin (m + 1)) (r : Option (Fin m))
    (a : Option Unit) (b : Option (Fin m)) : Option (Fin (m + 1)) :=
  match r with
  | some i => some (j.succAbove i)
  | none => match a with
    | none => b.map j.succAboveEmb
    | some _ => some j

def localPinnedSplitWeight {m : ℕ} (v : ℝ) (r : Option (Fin m))
    (a : Option Unit) (b : Option (Fin m)) : ℝ :=
  localPinnedBaseWeight v r * localPinnedDivisorWeight v r a * localPinnedMovedCoeff v r a b

theorem sum_localPinnedProfileKernel_mul {m : ℕ} {v : ℝ}
    (hv : v - (m + 1) ≠ 0) (j : Fin (m + 1)) (r : Option (Fin m))
    (f : Option (Fin (m + 1)) → ℝ) :
    (∑ s, localPinnedProfileKernel v j.succAboveEmb r s * f s) =
      match r with
      | none => f none + (1 / (v - (m + 1))) * f (some j) -
          (1 / ((v - 1) * (v - (m + 1)))) * ∑ i, f (some (j.succAbove i))
      | some i => (v / (v - 1)) * f (some (j.succAbove i)) := by
  cases r with
  | none =>
    have him (i : Fin m) :
        localPinnedProfileKernel v j.succAboveEmb none (some (j.succAbove i)) =
          -(1 / ((v - 1) * (v - (m + 1)))) := by
      simpa only [Fin.coe_succAboveEmb, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        localPinnedProfileKernel_none_image v j.succAboveEmb i
    rw [Fintype.sum_option, Fin.sum_univ_succAbove _ j]
    simp only [localPinnedProfileKernel_none_none, one_mul, him]
    rw [localPinnedProfileKernel_none_missing v j.succAboveEmb j
      (fun i => Fin.succAbove_ne j i)]
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    simp only [Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    ring
  | some i =>
    have hc : Fintype.card (Fin (m + 1)) = Fintype.card (Fin m) + 1 := by simp
    have hv' : v - Fintype.card (Fin (m + 1)) ≠ 0 := by simpa using hv
    simp only [localPinnedProfileKernel_some hc hv', ite_mul, zero_mul]
    simp

theorem sum_localPinnedSplitWeight_mul {m : ℕ} (v : ℝ)
    (j : Fin (m + 1)) (r : Option (Fin m)) (f : Option (Fin (m + 1)) → ℝ) :
    (∑ a : Option Unit, ∑ b : Option (Fin m),
      localPinnedSplitWeight v r a b * f (localPinnedSplitState j r a b)) =
      match r with
      | none => f none + (1 / (v - (m + 1))) * f (some j) -
          (1 / ((v - 1) * (v - (m + 1)))) * ∑ i, f (some (j.succAbove i))
      | some i => (v / (v - 1)) * f (some (j.succAbove i)) := by
  cases r <;>
    simp [Fintype.sum_option, localPinnedSplitWeight, localPinnedBaseWeight,
      localPinnedDivisorWeight, localPinnedMovedCoeff, localPinnedSplitState, Finset.mul_sum]
  ring

theorem localPinnedSplit_pushforward {m : ℕ} {v : ℝ}
    (hv : v - (m + 1) ≠ 0) (j : Fin (m + 1)) (r : Option (Fin m))
    (s : Option (Fin (m + 1))) :
    (∑ a : Option Unit, ∑ b : Option (Fin m),
      if localPinnedSplitState j r a b = s then localPinnedSplitWeight v r a b else 0) =
        localPinnedProfileKernel v j.succAboveEmb r s := by
  have h := (sum_localPinnedSplitWeight_mul v j r
    (fun t => if t = s then 1 else 0)).trans
      (sum_localPinnedProfileKernel_mul hv j r (fun t => if t = s then 1 else 0)).symm
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.localPinnedSplit_pushforward
