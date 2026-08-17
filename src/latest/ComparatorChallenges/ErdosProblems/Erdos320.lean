import Mathlib

open Filter
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos321

def reciprocalSubsetSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, ((n : ℚ)⁻¹)

noncomputable def realIteratedLog : ℕ → ℝ → ℝ
  | 0, x => x
  | k + 1, x => Real.log (realIteratedLog k x)

noncomputable def iteratedLogTailProduct : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k + 1, x => Real.log x * iteratedLogTailProduct k (Real.log x)

def LogTowerAbove (B : ℝ) (k : ℕ) (x : ℝ) : Prop :=
  ∀ j ≤ k, B ≤ realIteratedLog j x

def IsTerminalLogDepth (B : ℝ) (n d : ℕ) : Prop :=
  LogTowerAbove B d (Real.log (Real.log (n : ℝ))) ∧
    realIteratedLog (d + 1) (Real.log (Real.log (n : ℝ))) < B

noncomputable def terminalReciprocalScale (n d : ℕ) : ℝ :=
  (n : ℝ) / Real.log n *
    iteratedLogTailProduct d (Real.log (Real.log (n : ℝ)))

end Erdos321

namespace Erdos320

def S (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.image Erdos321.reciprocalSubsetSum).card

end Erdos320

namespace Erdos320

noncomputable def logS (N : ℕ) : ℝ :=
  Real.log (S N)

end Erdos320

namespace Erdos320

theorem erdos_320 :
    ∃ N₀ : ℕ, ∃ B c C : ℝ,
      3 ≤ N₀ ∧ 192 ≤ B ∧ 0 < c ∧ 0 < C ∧
      ∀ n, N₀ ≤ n → ∃ d : ℕ,
        d ≤ n ∧ Erdos321.IsTerminalLogDepth B n d ∧
          c * Erdos321.terminalReciprocalScale n d ≤ logS n ∧
          logS n ≤ C * Erdos321.terminalReciprocalScale n d := by
  sorry

end Erdos320

end
