/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos370

noncomputable def maxPrimeFac (n : ℕ) : ℕ := sSup {p : ℕ | p.Prime ∧ p ∣ n}

theorem erdos_370 :
    { n | maxPrimeFac n < √n ∧ maxPrimeFac (n + 1) < √(n + 1) }.Infinite := by
  sorry

end Erdos370
