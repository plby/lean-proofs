/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Finset Nat

namespace Erdos1136

noncomputable def countIn (S : Set ℕ) (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun x =>
    letI : Decidable (x ∈ S) := Classical.dec _
    decide (x ∈ S))).card

def pow2SumFree (S : Set ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ k : ℕ, a + b ≠ 2 ^ k
end Erdos1136

open Finset Nat

namespace Erdos1136

open scoped Classical in
theorem main_result :
    (∃ S : Set ℕ, pow2SumFree S ∧
      Filter.Tendsto (fun n : ℕ => (countIn S n : ℝ) / ↑n)
        Filter.atTop (nhds (1 / 2 : ℝ))) ∧
    (∀ S : Set ℕ, pow2SumFree S →
      Filter.limsup (fun n : ℕ => (countIn S n : ℝ) / ↑n)
        Filter.atTop ≤ 1 / 2) := by
  sorry

open scoped Classical in
theorem general_upper_bound (s : ℕ → ℕ) (hs_pos : ∀ k, 0 < s k)
    (hs_mono : StrictMono s) (hs_growth : ∀ k, s (k + 1) ≤ 2 * s k + 2)
    (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA_sub : A ⊆ Finset.Icc 1 n)
    (hA_card : 2 * A.card > n + s 0) :
    ∃ i, ∃ a ∈ A, ∃ b ∈ A, a + b = s i := by
  sorry

open scoped Classical in
theorem general_upper_bound_infinite
    (s : ℕ → ℕ) (hs_pos : ∀ k, 0 < s k)
    (hs_mono : StrictMono s) (hs_growth : ∀ k, s (k + 1) ≤ 2 * s k + 2)
    (A : Set ℕ)
    (hA_density : 1 / 2 < Filter.limsup (fun n : ℕ => (countIn A n : ℝ) / ↑n) Filter.atTop) :
    Set.Infinite {i : ℕ | ∃ a ∈ A, ∃ b ∈ A, a + b = s i} := by
  sorry

end Erdos1136
