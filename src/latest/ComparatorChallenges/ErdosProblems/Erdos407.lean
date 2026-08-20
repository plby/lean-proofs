import Mathlib

open scoped BigOperators Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos407

structure Rep where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq

end Erdos407

namespace Erdos407

def Rep.value (r : Rep) : ℕ :=
  2 ^ r.a + 3 ^ r.b + 2 ^ r.c * 3 ^ r.d

end Erdos407

namespace Erdos407

def solutions (n : ℕ) : Set Rep := {r | r.value = n}

end Erdos407

namespace Erdos407

noncomputable def w (n : ℕ) : ℕ := (solutions n).ncard

end Erdos407

namespace Erdos407

theorem erdos_407 : ∃ C : ℕ, ∀ n : ℕ, w n ≤ C := by
  sorry

end Erdos407

end
