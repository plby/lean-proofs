import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false
attribute [local instance] Classical.propDecidable

open Lean Elab Command

namespace Erdos418

theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  sorry

end Erdos418
