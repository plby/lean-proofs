import ErdosProblems.Erdos520.FreshExpansion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Largest-prime decomposition

This file proves the exact squarefree-Rademacher version of equations (6)--(7)
in the supplied repair.  Because `f` vanishes on nonsquarefree integers, there
is no separate squareful-largest-prime remainder.
-/

/-- Extending the right endpoint of a fresh-prime block either inserts the new
prime or leaves the block unchanged. -/
theorem freshPrimes_succ_right {a b : ℕ} (hab : a ≤ b) :
    freshPrimes a (b + 1) =
      if (b + 1).Prime then insert (b + 1) (freshPrimes a b)
      else freshPrimes a b := by
  classical
  split_ifs with hprime
  · ext p
    simp only [mem_freshPrimes, mem_insert]
    constructor
    · rintro ⟨hp, hap, hpb⟩
      by_cases heq : p = b + 1
      · exact Or.inl heq
      · exact Or.inr ⟨hp, hap, by omega⟩
    · rintro (rfl | ⟨hp, hap, hpb⟩)
      · exact ⟨hprime, by omega, le_rfl⟩
      · exact ⟨hp, hap, hpb.trans (Nat.le_succ b)⟩
  · ext p
    simp only [mem_freshPrimes]
    constructor
    · rintro ⟨hp, hap, hpb⟩
      exact ⟨hp, hap, by
        by_contra hle
        have : p = b + 1 := by omega
        exact hprime (this ▸ hp)⟩
    · rintro ⟨hp, hap, hpb⟩
      exact ⟨hp, hap, hpb.trans (Nat.le_succ b)⟩

/-- Telescoping the one-prime recurrence gives the exact largest-prime sum
between two cutoffs. -/
theorem Ψ_eq_Ψ_add_freshPrimeSum (omega : Omega) (z : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    Ψ omega z b = Ψ omega z a +
      ∑ p ∈ freshPrimes a b, ε omega p * Ψ' omega (z / p) p := by
  classical
  induction b, hab using Nat.le_induction with
  | base =>
      have hempty : freshPrimes a a = ∅ := by
        ext p
        simp [mem_freshPrimes]
      simp [hempty]
  | @succ b hab ih =>
      have hpos : 0 < b + 1 := Nat.succ_pos b
      rw [Ψ_recurrence omega z hpos]
      simp only [Nat.add_sub_cancel]
      rw [ih, freshPrimes_succ_right hab]
      by_cases hprime : (b + 1).Prime
      · rw [if_pos hprime, if_pos hprime]
        have hnotmem : b + 1 ∉ freshPrimes a b := by
          simp [mem_freshPrimes]
        rw [sum_insert hnotmem]
        rw [Ψ'_eq_Ψ_pred omega (z / (b + 1)) hpos]
        simp only [Nat.add_sub_cancel]
        ring
      · rw [if_neg hprime, if_neg hprime]
        ring

/-- Every positive integer `n ≤ N` is `(N+1)`-smooth, so the fully smooth
sum is exactly the ordinary one-indexed partial sum. -/
theorem partialSum_eq_Ψ_self (omega : Omega) (N : ℕ) :
    partialSum omega N = Ψ omega N N := by
  classical
  have hsmooth : Nat.smoothNumbersUpTo N (N + 1) =
      (Finset.range N).image Nat.succ := by
    ext n
    rw [Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hnN, hsmooth⟩
      have hn0 : 0 < n := Nat.pos_of_ne_zero
        (Nat.ne_zero_of_mem_smoothNumbers hsmooth)
      rw [Finset.mem_image]
      exact ⟨n - 1, Finset.mem_range.mpr (by omega), by omega⟩
    · intro hn
      rw [Finset.mem_image] at hn
      rcases hn with ⟨k, hk, rfl⟩
      have hklt : k < N := Finset.mem_range.mp hk
      exact ⟨by omega,
        Nat.mem_smoothNumbers_of_lt (Nat.succ_pos k) (by omega)⟩
  unfold partialSum Ψ
  rw [hsmooth, Finset.sum_image]
  exact Nat.succ_injective.injOn

/-- The one-largest-prime martingale piece on `(a,b]`. -/
noncomputable def largestPrimeMain
    (omega : Omega) (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b, ε omega p * Ψ' omega (x / p) p

/-- Predictable quadratic variation of `largestPrimeMain`; this is equation
(8) in the supplied proof. -/
noncomputable def largestPrimeQuadraticVariation
    (omega : Omega) (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b, |Ψ' omega (x / p) p| ^ 2

theorem largestPrimeQuadraticVariation_nonneg
    (omega : Omega) (x a b : ℕ) :
    0 ≤ largestPrimeQuadraticVariation omega x a b := by
  unfold largestPrimeQuadraticVariation
  apply Finset.sum_nonneg
  intro p _hp
  exact sq_nonneg _

/-- Equations (6)--(7) for the squarefree Rademacher model.  The second term
is already a martingale sum in the freshly revealed prime signs. -/
theorem partialSum_largestPrimeDecomposition (omega : Omega) (x y₀ : ℕ)
    (hy : y₀ ≤ x) :
    partialSum omega x = Ψ omega x y₀ +
      ∑ p ∈ freshPrimes y₀ x,
        ε omega p * Ψ' omega (x / p) p := by
  rw [partialSum_eq_Ψ_self]
  exact Ψ_eq_Ψ_add_freshPrimeSum omega x hy

/-- Named form of equations (6)--(8). -/
theorem partialSum_eq_smooth_add_largestPrimeMain
    (omega : Omega) (x y₀ : ℕ) (hy : y₀ ≤ x) :
    partialSum omega x =
      Ψ omega x y₀ + largestPrimeMain omega x y₀ x := by
  simpa only [largestPrimeMain] using!
    partialSum_largestPrimeDecomposition omega x y₀ hy

end Problem520
end Erdos
