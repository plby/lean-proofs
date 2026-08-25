/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Topology Filter

namespace Erdos694

noncomputable def R (x : ℕ) : ℝ :=
  ⨆ n ∈ {n | n ∈ Set.Icc 1 x ∧ ∃ m, Nat.totient m = n},
    let mmax := sSup {m | Nat.totient m = n}
    let mmin := sInf {m | Nat.totient m = n}
    (mmax : ℝ) / mmin

theorem totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log x) := by
  sorry

theorem infinitely_many_collisions (a b : ℕ) (hb : 1 ≤ b) (hgt : b < a)
    (hab : Nat.totient a = Nat.totient b) :
    {N : ℕ | ∃ x y, Nat.totient x = N ∧ Nat.totient y = N ∧ y < x ∧ b * x ≥ a * y}.Infinite := by
  sorry

theorem erdos_694 :
    Tendsto
      (fun x : ℕ => R x /
        (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log x)))
      atTop (𝓝 1) := by
  sorry

end Erdos694
