/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos866b

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.flexible false
set_option linter.style.whitespace false

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

open Finset
open scoped Pointwise

open scoped Classical in
def HasPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ ∀ i j : Fin k, i < j → b i + b j ∈ A

open scoped Classical in
def HasPosPairwiseSums (A : Finset ℤ) (k : ℕ) : Prop :=
  ∃ b : Fin k → ℤ, Function.Injective b ∧ (∀ i : Fin k, 0 < b i) ∧
    ∀ i j : Fin k, i < j → b i + b j ∈ A

open scoped Classical in
noncomputable def gFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPairwiseSums A k}

open scoped Classical in
noncomputable def hFun (k n : ℕ) : ℕ :=
  sInf {m : ℕ | ∀ (A : Finset ℤ), A ⊆ Icc (1 : ℤ) (2 * ↑n) →
    n + m ≤ A.card → HasPosPairwiseSums A k}
section SidonBound

open Real

end SidonBound

end Erdos866b

open Finset
open scoped Pointwise
open Real

namespace Erdos866b

open scoped Classical in
theorem g3 (n : ℕ) (hn : 3 ≤ n) : gFun 3 n = 1 := by
  sorry

open scoped Classical in
theorem h3 (n : ℕ) (hn : 4 ≤ n) : hFun 3 n = 2 := by
  sorry

open scoped Classical in
theorem g4 (n : ℕ) (hn : 2 ≤ n) : gFun 4 n = 3 := by
  sorry

open scoped Classical in
theorem h4upper (n : ℕ) (hn : 0 < n) : hFun 4 n ≤ 2270 := by
  sorry

open scoped Classical in
theorem g5upper (n : ℕ) : gFun 5 n < 120000000 := by
  sorry

open scoped Classical in
theorem generalupper (k : ℕ) (hk : 3 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      gFun k n ≤ hFun k n ∧
      (hFun k n : ℝ) < 4 * (↑n : ℝ) ^ ((1:ℝ) - 1 / 2 ^ ((k:ℝ) - 2)) := by
  sorry

end Erdos866b
