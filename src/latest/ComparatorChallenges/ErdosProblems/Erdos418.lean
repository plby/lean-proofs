import Mathlib

set_option linter.style.setOption false
set_option linter.flexible false

namespace Erdos418

def m_BS : ℕ := 509203
end Erdos418

attribute [local instance] Classical.propDecidable

open Lean Elab Command

namespace Erdos418

theorem erdos_418 : { (n - n.totient : ℕ) | n }ᶜ.Infinite := by
  sorry

end Erdos418
