/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

namespace Erdos897

theorem not_erdos_897 :
    ¬ ((∀ (f : ℕ → ℝ),
        (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
        ((Filter.atTop ⊓ Filter.principal {x : ℕ × ℕ | x.1.Prime}).limsup
          (fun x => (f (x.1 ^ x.2) / (x.1 ^ x.2 : ℝ).log : EReal)) = ⊤) →
        Filter.atTop.limsup (fun (n : ℕ) => ((f (n + 1) - f n) / (n : ℝ).log : EReal)) = ⊤)) := by
  sorry

theorem not_erdos_897_part_ii :
    ¬ ((∀ (f : ℕ → ℝ),
        (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
        ((Filter.atTop ⊓ Filter.principal {x : ℕ × ℕ | x.1.Prime}).limsup
          (fun x => (f (x.1 ^ x.2) / (x.1 ^ x.2 : ℝ).log : EReal)) = ⊤) →
        Filter.atTop.limsup (fun (n : ℕ) => (f (n + 1) / f n : EReal)) = ⊤)) := by
  sorry

end Erdos897
