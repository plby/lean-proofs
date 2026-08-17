import Mathlib

open Finset Set
open scoped BigOperators ArithmeticFunction.Omega

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos542

def PairwiseLCMExceeds (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

end Erdos542

namespace Erdos542

noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

end Erdos542

namespace Erdos542

def constructionExponent (t : ℕ) : ℕ := 2 ^ (6 * t)

end Erdos542

namespace Erdos542

def constructionAmbient (t : ℕ) : ℕ := 2 ^ constructionExponent t

end Erdos542

namespace Erdos542

def thresholdSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun r => n < r * r.minFac

end Erdos542

namespace Erdos542

def minimalThresholdSet (n : ℕ) : Finset ℕ :=
  (thresholdSet n).filter fun a =>
    ∀ c ∈ thresholdSet n, c ∣ a → a ∣ c

end Erdos542

namespace Erdos542

def constructionFamily (t : ℕ) : Finset ℕ :=
  minimalThresholdSet (constructionAmbient t)

end Erdos542

namespace Erdos542

def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬a ∣ m

/-! ## Definitions and the Schinzel--Szekeres rational certificate -/

end Erdos542

namespace Erdos542

def HasUniformLinearUncoveredLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ A : Finset ℕ,
    PairwiseLCMExceeds n A → c * n ≤ ((uncovered n A).card : ℝ)

end Erdos542

namespace Erdos542

theorem erdos542_resolution :
    (∀ n : ℕ, ∀ A : Finset ℕ,
      PairwiseLCMExceeds n A → reciprocalSum A ≤ (31 : ℝ) / 30) ∧
    (PairwiseLCMExceeds 5 {2, 3, 5} ∧
      reciprocalSum {2, 3, 5} = (31 : ℝ) / 30) ∧
    (∀ t : ℕ, PairwiseLCMExceeds (constructionAmbient t) (constructionFamily t)) ∧
    Filter.Tendsto
      (fun t : ℕ =>
        ((uncovered (constructionAmbient t) (constructionFamily t)).card : ℝ) /
          constructionAmbient t)
      Filter.atTop (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℕ in Filter.atTop,
      1 - ε < reciprocalSum (constructionFamily t)) ∧
    ¬HasUniformLinearUncoveredLowerBound := by
  sorry

end Erdos542

end
