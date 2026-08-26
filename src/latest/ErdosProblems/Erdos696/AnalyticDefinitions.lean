/-
Adapted from Jayyhk/erdos-lean, problems/696/Erdos696.lean,
revision 806d0b587ea7a2fb5afd5154edfe416a0cd404a4.
Source: https://www.erdosproblems.com/forum/thread/696#post-6848
All upstream heartbeat overrides have been removed.
-/

import Mathlib

namespace Erdos696

/-- The prime-counting function in arithmetic progressions:
`piMod t q a = #{p ≤ t : p prime, p ≡ a (mod q)}`. -/
noncomputable def piMod (t : ℝ) (q a : ℕ) : ℕ :=
  Nat.card {p : ℕ | p ≤ ⌊t⌋₊ ∧ p.Prime ∧ p % q = a % q}



/-- The logarithmic integral `Li(t) = ∫₂^t dt / log t`.  We adopt the
standard convention `Li(t) := ∫_{2}^{t} 1 / log u du`. -/
noncomputable def li (t : ℝ) : ℝ :=
  ∫ u in (2 : ℝ)..t, 1 / Real.log u

/-- The sole analytic hypothesis of the upstream formalization. -/
class SiegelWalfisz : Prop where
  estimate :
    ∀ A : ℝ, 0 < A →
    ∃ c : ℝ, 0 < c ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ t : ℝ, 2 ≤ t →
          ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (Real.log t) ^ A →
            ∀ a : ℕ, Nat.Coprime a q →
              |((piMod t q a : ℝ)) - li t / (q.totient : ℝ)| ≤
                C * t * Real.exp (-c * Real.sqrt (Real.log t))

alias siegel_walfisz := SiegelWalfisz.estimate

end Erdos696
