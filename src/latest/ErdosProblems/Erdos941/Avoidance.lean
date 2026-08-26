import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Counting words that avoid a target in a three-choice automaton

Every block that admits a route to the target removes at least one of its
`3 ^ K` words. The lemma is finite and does not assume equidistribution.
-/

namespace Erdos941

section Automaton

variable {α : Type*} (step : α → Fin 3 → α) (target : α → Prop) [DecidablePred target]

def avoidanceCount : ℕ → α → ℕ
  | 0, s => if target s then 0 else 1
  | n + 1, s => if target s then 0 else ∑ i : Fin 3, avoidanceCount n (step s i)

def CanHit : ℕ → α → Prop
  | 0, s => target s
  | n + 1, s => target s ∨ ∃ i : Fin 3, CanHit n (step s i)

theorem avoidanceCount_le (n : ℕ) (s : α) : avoidanceCount step target n s ≤ 3 ^ n := by
  induction n generalizing s with
  | zero => simp only [avoidanceCount, pow_zero]; split <;> omega
  | succ n ih =>
    by_cases hs : target s
    · simp only [avoidanceCount, hs, ↓reduceIte, zero_le]
    · simp only [avoidanceCount, hs, ↓reduceIte]
      calc
        _ ≤ ∑ _i : Fin 3, 3 ^ n := Finset.sum_le_sum (fun i _ => ih (step s i))
        _ = 3 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

theorem avoidanceCount_lt_of_canHit {n : ℕ} {s : α} (h : CanHit step target n s) :
    avoidanceCount step target n s < 3 ^ n := by
  induction n generalizing s with
  | zero =>
    change target s at h
    simp only [avoidanceCount, h, ↓reduceIte, pow_zero, Nat.zero_lt_one]
  | succ n ih =>
    by_cases hs : target s
    · simp only [avoidanceCount, hs, ↓reduceIte]
      positivity
    · obtain ⟨i, hi⟩ := h.resolve_left hs
      simp only [avoidanceCount, hs, ↓reduceIte]
      calc
        _ < ∑ _j : Fin 3, 3 ^ n := Finset.sum_lt_sum
          (fun j _ => avoidanceCount_le step target n (step s j))
          ⟨i, Finset.mem_univ i, ih hi⟩
        _ = 3 ^ (n + 1) := by simp [pow_succ, Nat.mul_comm]

theorem avoidanceCount_add_le {m B : ℕ}
    (hB : ∀ s : α, avoidanceCount step target m s ≤ B) (n : ℕ) (s : α) :
    avoidanceCount step target (n + m) s ≤ B * avoidanceCount step target n s := by
  induction n generalizing s with
  | zero =>
    by_cases hs : target s
    · cases m <;> simp [avoidanceCount, hs]
    · simpa only [zero_add, avoidanceCount, hs, ↓reduceIte, mul_one] using hB s
  | succ n ih =>
    by_cases hs : target s
    · simp only [Nat.succ_add, avoidanceCount, hs, ↓reduceIte, mul_zero, le_refl]
    · simp only [Nat.succ_add, avoidanceCount, hs, ↓reduceIte, Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => ih (step s i))

theorem avoidanceCount_block_bound {K : ℕ}
    (hK : ∀ s : α, CanHit step target K s) (t : ℕ) (s : α) :
    avoidanceCount step target (K * t) s ≤ (3 ^ K - 1) ^ t := by
  have hB : ∀ s : α, avoidanceCount step target K s ≤ 3 ^ K - 1 := by
    intro s
    have := avoidanceCount_lt_of_canHit step target (hK s)
    omega
  induction t generalizing s with
  | zero => simpa using avoidanceCount_le step target 0 s
  | succ t ih =>
    rw [Nat.mul_succ]
    calc
      _ ≤ (3 ^ K - 1) * avoidanceCount step target (K * t) s :=
        avoidanceCount_add_le step target hB (K * t) s
      _ ≤ (3 ^ K - 1) * (3 ^ K - 1) ^ t := Nat.mul_le_mul_left _ (ih s)
      _ = (3 ^ K - 1) ^ (t + 1) := by rw [pow_succ, Nat.mul_comm]

end Automaton

end Erdos941
