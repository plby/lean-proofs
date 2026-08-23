/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

open Lean Elab Command

namespace Erdos418

open scoped Classical in
theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  sorry

end Erdos418
