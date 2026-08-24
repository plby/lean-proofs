/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos542

def PairwiseLCMExceeds (n : ℕ) (A : Finset ℕ) : Prop :=
  (∀ a ∈ A, 1 ≤ a ∧ a ≤ n) ∧
    ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b

noncomputable def reciprocalSum (A : Finset ℕ) : ℝ :=
  ∑ a ∈ A, (1 : ℝ) / a

def constructionExponent (t : ℕ) : ℕ := 2 ^ (6 * t)

def constructionAmbient (t : ℕ) : ℕ := 2 ^ constructionExponent t

def thresholdSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun r => n < r * r.minFac

def minimalThresholdSet (n : ℕ) : Finset ℕ :=
  (thresholdSet n).filter fun a =>
    ∀ c ∈ thresholdSet n, c ∣ a → a ∣ c

def constructionFamily (t : ℕ) : Finset ℕ :=
  minimalThresholdSet (constructionAmbient t)

def uncovered (n : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun m => ∀ a ∈ A, ¬a ∣ m

/-! ## Definitions and the Schinzel--Szekeres rational certificate -/

theorem erdos_542 :
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
        ¬(∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ A : Finset ℕ,
      Erdos542.PairwiseLCMExceeds n A → c * n ≤ ((Erdos542.uncovered n A).card : ℝ)) := by
  sorry

end Erdos542
