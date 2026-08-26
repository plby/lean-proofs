/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos696

/-- Increasing prime divisors with each entry congruent to one modulo its predecessor. -/
def IsPrimeChain (n : ℕ) (ps : List ℕ) : Prop :=
  (∀ p ∈ ps, p.Prime ∧ p ∣ n) ∧
  ps.Pairwise (· < ·) ∧
  (∀ i : Fin ps.length, ∀ hi : i.val + 1 < ps.length,
      ps.get ⟨i.val + 1, hi⟩ % ps.get i = 1)

/-- Increasing positive divisors with the same congruence condition, allowing predecessor one. -/
def IsDivisorChain (n : ℕ) (ds : List ℕ) : Prop :=
  (∀ d ∈ ds, 1 ≤ d ∧ d ∣ n) ∧
  ds.Pairwise (· < ·) ∧
  (∀ i : Fin ds.length, ∀ hi : i.val + 1 < ds.length,
      Nat.ModEq (ds.get i) (ds.get ⟨i.val + 1, hi⟩) 1)

/-- The maximal length of a prime chain dividing `n`. -/
noncomputable def hChain (n : ℕ) : ℕ :=
  sSup {ℓ | ∃ ps : List ℕ, IsPrimeChain n ps ∧ ps.length = ℓ}

/-- The maximal divisor-chain length, with value zero at one by convention. -/
noncomputable def HChain (n : ℕ) : ℕ :=
  if n = 1 then 0
  else sSup {u | ∃ ds : List ℕ, IsDivisorChain n ds ∧ ds.length = u}

/-- The `k`-fold natural logarithm. -/
noncomputable def iteratedLog : ℕ → ℝ → ℝ
  | 0,     x => x
  | k+1,   x => Real.log (iteratedLog k x)

/-- The first iterate at most `exp 1`, with fallback zero if none exists. -/
noncomputable def logStar (x : ℝ) : ℕ := by
  classical
  exact
    if h : ∃ k : ℕ, iteratedLog k x ≤ Real.exp 1 then Nat.find h else 0

/-- A property holds on a set of natural numbers of asymptotic density one. -/
def almostAll (P : ℕ → Prop) : Prop :=
  Filter.Tendsto
    (fun x : ℝ => ((Nat.card {n : ℕ | n ≤ ⌊x⌋₊ ∧ ¬ P n} : ℕ) : ℝ) / x)
    Filter.atTop (nhds 0)

/-- The asymptotics of the prime-chain length, divisor-chain length, and their ratio. -/
theorem erdos_696 :
    ∀ ε : ℝ, 0 < ε →
      almostAll (fun n =>
        |(hChain n : ℝ) - (logStar n : ℝ) / 2| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
        |(HChain n : ℝ) - (logStar n : ℝ)| ≤ ε * (logStar n : ℝ)) ∧
      almostAll (fun n =>
        n ≥ 2 → |(HChain n : ℝ) / (hChain n : ℝ) - 2| ≤ ε) := by
  sorry

end Erdos696
