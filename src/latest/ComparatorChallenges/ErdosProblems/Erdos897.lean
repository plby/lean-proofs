import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Std.Tactic.BVDecide.LRAT.Internal.Clause

set_option linter.style.setOption false

namespace Erdos897

set_option linter.style.longLine false
set_option linter.flexible false

attribute [local instance] Classical.propDecidable

theorem erdos_897.parts.i : (∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {x : ℕ × ℕ | x.1.Prime}).limsup
      (fun x => (f (x.1 ^ x.2) / (x.1 ^ x.2 : ℝ).log : EReal)) = ⊤) →
    Filter.atTop.limsup (fun (n : ℕ) => ((f (n + 1) - f n) / (n : ℝ).log : EReal)) = ⊤) ↔
    false := by
  sorry

theorem erdos_897.parts.ii : (∀ (f : ℕ → ℝ),
    (∀ᵉ (a > 0) (b > 0), a.Coprime b → f (a * b) = f a + f b) →
    ((Filter.atTop ⊓ Filter.principal {x : ℕ × ℕ | x.1.Prime}).limsup
      (fun x => (f (x.1 ^ x.2) / (x.1 ^ x.2 : ℝ).log : EReal)) = ⊤) →
    Filter.atTop.limsup (fun (n : ℕ) => (f (n + 1) / f n : EReal)) = ⊤) ↔ false := by
  sorry

end Erdos897
