import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter Set
open scoped BigOperators Topology

namespace Erdos227

noncomputable def maximumTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range fun n : ℕ ↦ ‖a n‖ * r ^ n)

noncomputable def maximumModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  sSup (Set.range fun θ : ℝ ↦ ‖f (r * Complex.exp (θ * Complex.I))‖)

def IsEntirePowerSeries (a : ℕ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, HasSum (fun n : ℕ ↦ a n * z ^ n) (f z)

def IsTranscendentalSeries (a : ℕ → ℂ) : Prop :=
  ¬ ∃ N : ℕ, ∀ n ≥ N, a n = 0

def Erdos227Claim : Prop :=
  ∀ (a : ℕ → ℂ) (f : ℂ → ℂ) (L : ℝ),
    IsEntirePowerSeries a f →
    IsTranscendentalSeries a →
    Tendsto (fun r : ℝ ↦ maximumTerm a r / maximumModulus f r) atTop (𝓝 L) →
    L = 0

theorem erdos_227 : ¬ Erdos227Claim := by
  sorry

end Erdos227
