/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Erdos179

/-- `IsAPPair k A (a,b)` says that `a` and `b` are the first two terms of a
nontrivial `k`-term arithmetic progression contained in `A`.

For `k ≥ 2`, first two terms are a canonical code for an unoriented
progression: requiring `a < b` fixes the positive orientation. -/
def IsAPPair (k : ℕ) (A : Finset ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ ∀ i ∈ Finset.range k, p.1 + i * (p.2 - p.1) ∈ A

/-- The finite set of canonical first-two-term codes of the `k`-APs in `A`. -/
noncomputable def apPairs (k : ℕ) (A : Finset ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (A ×ˢ A).filter (IsAPPair k A)

/-- The number of nontrivial, unoriented `k`-term APs in `A`.

The branch at `k = 1` implements the usual singleton convention.  Length
zero is irrelevant to Problem 179 and is assigned count zero. -/
noncomputable def apCount : ℕ → Finset ℕ → ℕ
  | 0, _ => 0
  | 1, A => #A
  | Nat.succ (Nat.succ k), A => #(apPairs (k + 2) A)

/-- A finite set contains a `k`-term arithmetic progression. -/
def HasAP : ℕ → Finset ℕ → Prop
  | 0, _ => True
  | 1, A => A.Nonempty
  | Nat.succ (Nat.succ k), A => (apPairs (k + 2) A).Nonempty

/-- A finite set contains no `k`-term arithmetic progression. -/
def APFree (k : ℕ) (A : Finset ℕ) : Prop := ¬HasAP k A

@[simp] lemma mem_apPairs {k : ℕ} {A : Finset ℕ} {a b : ℕ} :
    (a, b) ∈ apPairs k A ↔
      a ∈ A ∧ b ∈ A ∧ a < b ∧
        ∀ i < k, a + i * (b - a) ∈ A := by
  classical
  simp [apPairs, IsAPPair, and_assoc]

lemma apCount_le_sq (k : ℕ) (A : Finset ℕ) : apCount k A ≤ #A ^ 2 := by
  classical
  rcases k with _ | k
  · simp [apCount]
  rcases k with _ | k
  · simp only [apCount]
    have h : (#A : ℤ) ≤ (#A : ℤ) ^ 2 := by
      by_cases hA : #A = 0
      · simp [hA]
      · have : (1 : ℤ) ≤ #A := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hA)
        nlinarith
    exact_mod_cast h
  · change #(apPairs (k + 2) A) ≤ #A ^ 2
    exact (Finset.card_filter_le _ _).trans_eq (by simp [apPairs, pow_two])

/-- `ForcesLongAP s n k m` is the literal forcing property in Problem 179. -/
def ForcesLongAP (s n k m : ℕ) : Prop :=
  ∀ A : Finset ℕ, #A = n → m ≤ apCount s A → HasAP k A

lemma forcesLongAP_sq_add_one (s n k : ℕ) : ForcesLongAP s n k (n ^ 2 + 1) := by
  intro A hA hm
  exfalso
  have hcount := apCount_le_sq s A
  rw [hA] at hcount
  omega

lemma exists_forcing_threshold (s n k : ℕ) : ∃ m, ForcesLongAP s n k m :=
  ⟨n ^ 2 + 1, forcesLongAP_sq_add_one s n k⟩

/-- Erdős's threshold: the least number of short progressions forcing a long
progression in every `n`-element subset of `ℕ`. -/
noncomputable def F (s n k : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_forcing_threshold s n k)

theorem erdos_179 :
    (fun n : ℕ ↦ (F 3 n 4 : ℝ)) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ) ^ 2) ∧
      ∀ k : ℕ, 3 < k →
        Tendsto (fun n : ℕ ↦ Real.log (F 3 n k) / Real.log n)
          atTop (𝓝 2) := by
  sorry

end Erdos179

end
